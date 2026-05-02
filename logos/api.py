"""Claude API wrapper for Logos AI — mirrors gnosis-ai pattern."""

from __future__ import annotations

import json
import random
import time
from dataclasses import dataclass
from typing import Optional

import anthropic

from logos.config import LogosConfig


PRICING = {
    "claude-sonnet-4-20250514": {"input": 3.0, "output": 15.0},
    "claude-sonnet-4-6": {"input": 3.0, "output": 15.0},
    "claude-opus-4-20250514": {"input": 15.0, "output": 75.0},
    "claude-opus-4-6": {"input": 15.0, "output": 75.0},
}


@dataclass
class APIStats:
    """Track API usage across a session."""
    calls: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    errors: int = 0
    cost_usd: float = 0.0

    def record(self, model: str, input_tokens: int, output_tokens: int):
        self.calls += 1
        self.input_tokens += input_tokens
        self.output_tokens += output_tokens
        pricing = PRICING.get(model, {"input": 10.0, "output": 50.0})
        self.cost_usd += (
            input_tokens * pricing["input"] / 1_000_000
            + output_tokens * pricing["output"] / 1_000_000
        )


class ClaudeAPI:
    """Wrapper around the Anthropic Claude API with fallback and retry."""

    def __init__(self, config: LogosConfig):
        if not config.api_key:
            raise RuntimeError(
                "No API key found. Set ANTHROPIC_API_KEY or add "
                '"anthropic_api_key" to logos.json.'
            )
        self.config = config
        self.client = anthropic.Anthropic(
            api_key=config.api_key,
            timeout=600.0,
            max_retries=2,
        )
        self.stats = APIStats()

    def query(
        self,
        prompt: str,
        system: str = "",
        model: Optional[str] = None,
        max_tokens: int = 8192,
        temperature: float = 0.2,
    ) -> str:
        """Send a query to Claude and return text response."""
        if model is None:
            model = self.config.model_fast

        if self.stats.cost_usd >= self.config.max_cost_usd:
            raise RuntimeError(
                f"Cost limit reached: ${self.stats.cost_usd:.2f} "
                f"(max: ${self.config.max_cost_usd:.2f})"
            )

        messages = [{"role": "user", "content": prompt}]
        kwargs = {
            "model": model,
            "max_tokens": max_tokens,
            "messages": messages,
            "temperature": temperature,
        }
        if system:
            kwargs["system"] = system

        models_to_try = [model]
        if self.config.model_fallback and self.config.model_fallback != model:
            models_to_try.append(self.config.model_fallback)

        for model_idx, try_model in enumerate(models_to_try):
            kwargs["model"] = try_model
            last_error = None

            for attempt in range(self.config.max_retries):
                try:
                    text_parts = []
                    input_tokens = 0
                    output_tokens = 0

                    with self.client.messages.stream(**kwargs) as stream:
                        for event in stream:
                            if hasattr(event, "type"):
                                if event.type == "content_block_delta" and hasattr(event, "delta"):
                                    if hasattr(event.delta, "text"):
                                        text_parts.append(event.delta.text)
                        final = stream.get_final_message()
                        input_tokens = final.usage.input_tokens
                        output_tokens = final.usage.output_tokens

                    text = "".join(text_parts)
                    self.stats.record(try_model, input_tokens, output_tokens)
                    return text

                except anthropic.RateLimitError:
                    wait = min(60, (2 ** attempt) + random.uniform(0.5, 1.5))
                    time.sleep(wait)
                    last_error = "rate_limit"

                except (anthropic.APIConnectionError, anthropic.APITimeoutError):
                    self.stats.errors += 1
                    last_error = "connection_error"
                    if attempt < self.config.max_retries - 1:
                        time.sleep(min(30, (2 ** attempt) + random.uniform(1, 3)))

                except anthropic.APIError as e:
                    self.stats.errors += 1
                    last_error = str(e)
                    if attempt < self.config.max_retries - 1:
                        time.sleep(2 ** attempt)

            if model_idx < len(models_to_try) - 1:
                continue
            else:
                raise RuntimeError(
                    f"API failed after trying {len(models_to_try)} model(s) "
                    f"with {self.config.max_retries} retries each: {last_error}"
                )

        raise RuntimeError(f"API failed: {last_error}")

    def query_json(
        self,
        prompt: str,
        system: str = "",
        model: Optional[str] = None,
        max_tokens: int = 8192,
    ) -> dict | list:
        """Query Claude and parse response as JSON."""
        full_prompt = (
            prompt
            + "\n\nRespond with valid JSON only. No markdown fencing, no explanation — just the JSON."
        )
        text = self.query(full_prompt, system=system, model=model, max_tokens=max_tokens)
        text = text.strip()

        if text.startswith("```"):
            lines = text.split("\n")
            lines = [l for l in lines if not l.strip().startswith("```")]
            text = "\n".join(lines)

        try:
            return json.loads(text)
        except json.JSONDecodeError:
            for start_char, end_char in [("{", "}"), ("[", "]")]:
                start = text.find(start_char)
                end = text.rfind(end_char) + 1
                if start >= 0 and end > start:
                    try:
                        return json.loads(text[start:end])
                    except json.JSONDecodeError:
                        continue
            raise ValueError(f"Failed to parse JSON from API response: {text[:200]}")

    def query_deep(self, prompt: str, system: str = "", max_tokens: int = 8192) -> str:
        """Query using the deep model (Opus)."""
        return self.query(prompt, system=system, model=self.config.model_deep, max_tokens=max_tokens)

    def query_deep_json(self, prompt: str, system: str = "", max_tokens: int = 8192) -> dict | list:
        """Query deep model and parse as JSON."""
        return self.query_json(prompt, system=system, model=self.config.model_deep, max_tokens=max_tokens)
