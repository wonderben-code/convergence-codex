"""Claude API wrapper for Logos AI — mirrors gnosis-ai pattern.

Provides two backends:
  - ClaudeAPI: Uses the Anthropic API directly (requires API key, costs money)
  - MaxPlanAPI: Uses the Claude Code CLI (`claude -p`) via Max plan subscription ($0 cost)

Both expose the same interface: query(), query_json(), query_deep(), query_deep_json().
Use create_api(config, use_max_plan=False) to get the right one.
"""

from __future__ import annotations

import json
import os
import random
import subprocess
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

# Map full model IDs to CLI-friendly aliases
MODEL_CLI_ALIASES = {
    "claude-opus-4-20250514": "opus",
    "claude-opus-4-6": "opus",
    "claude-sonnet-4-20250514": "sonnet",
    "claude-sonnet-4-6": "sonnet",
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


class MaxPlanAPI:
    """Drop-in replacement for ClaudeAPI using Claude Code CLI (`claude -p`).

    Runs queries through the user's Max plan subscription instead of the
    Anthropic API, making all calls effectively free. Same interface as
    ClaudeAPI: query(), query_json(), query_deep(), query_deep_json().

    Requires `claude` CLI to be installed and the user to be authenticated
    with a Max plan subscription.
    """

    def __init__(self, config: LogosConfig):
        self.config = config
        self.stats = APIStats()

        # Verify claude CLI is available
        try:
            result = subprocess.run(
                ["claude", "--version"],
                capture_output=True, text=True, timeout=10,
                env=self._clean_env(),
            )
            if result.returncode != 0:
                raise FileNotFoundError
        except (FileNotFoundError, subprocess.TimeoutExpired):
            raise RuntimeError(
                "Claude Code CLI not found. Install it to use Max plan mode:\n\n"
                "  npm install -g @anthropic-ai/claude-code\n\n"
                "Then authenticate with: claude auth login"
            )

    @staticmethod
    def _clean_env() -> dict:
        """Return env dict with CLAUDECODE unset (allows nested invocation).

        Also removes ANTHROPIC_API_KEY so the CLI uses Max plan auth
        instead of a potentially invalid API key from the environment.
        """
        env = os.environ.copy()
        env.pop("CLAUDECODE", None)
        env.pop("CLAUDE_CODE_ENTRYPOINT", None)
        env.pop("ANTHROPIC_API_KEY", None)
        return env

    def _run_cli(self, prompt: str, system: str = "", model: str | None = None) -> str:
        """Execute a single Claude CLI call and return the text response."""
        if model is None:
            model = self.config.model_fast

        # Map full model ID to CLI alias
        cli_model = MODEL_CLI_ALIASES.get(model, model)

        cmd = [
            "claude", "-p",
            "--model", cli_model,
            "--output-format", "json",
            "--no-session-persistence",
        ]

        if system:
            cmd.extend(["--system-prompt", system])

        # Pipe prompt via stdin to avoid argument length limits
        for attempt in range(self.config.max_retries):
            try:
                result = subprocess.run(
                    cmd,
                    input=prompt,
                    capture_output=True,
                    text=True,
                    timeout=180,
                    env=self._clean_env(),
                )

                if result.returncode != 0:
                    self.stats.errors += 1
                    stderr = result.stderr.strip()
                    if attempt < self.config.max_retries - 1:
                        time.sleep(2 ** attempt)
                        continue
                    raise RuntimeError(
                        f"Claude CLI failed (exit {result.returncode}): {stderr[:500]}"
                    )

                # Parse JSON output
                output = json.loads(result.stdout)

                if output.get("is_error", False):
                    self.stats.errors += 1
                    if attempt < self.config.max_retries - 1:
                        time.sleep(2 ** attempt)
                        continue
                    raise RuntimeError(
                        f"Claude CLI error: {output.get('result', 'unknown error')}"
                    )

                text = output.get("result", "")
                self.stats.calls += 1
                # Cost is $0 on Max plan — track call count only
                return text

            except subprocess.TimeoutExpired:
                self.stats.errors += 1
                if attempt < self.config.max_retries - 1:
                    continue
                raise RuntimeError("Claude CLI timed out after 180s")

            except json.JSONDecodeError as e:
                self.stats.errors += 1
                if attempt < self.config.max_retries - 1:
                    time.sleep(2 ** attempt)
                    continue
                raise RuntimeError(
                    f"Failed to parse Claude CLI JSON output: {e}\n"
                    f"Raw output: {result.stdout[:500]}"
                )

        raise RuntimeError("Claude CLI failed after all retries")

    def query(
        self,
        prompt: str,
        system: str = "",
        model: Optional[str] = None,
        max_tokens: int = 8192,
        temperature: float = 0.2,
    ) -> str:
        """Send a query via Claude CLI and return the text response."""
        return self._run_cli(prompt, system=system, model=model)

    def query_json(
        self,
        prompt: str,
        system: str = "",
        model: Optional[str] = None,
        max_tokens: int = 8192,
    ) -> dict | list:
        """Query via CLI and parse response as JSON."""
        full_prompt = (
            prompt
            + "\n\nRespond with valid JSON only. No markdown fencing, no explanation — just the JSON."
        )

        text = self.query(full_prompt, system=system, model=model, max_tokens=max_tokens)

        # Strip markdown fencing if present
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

            raise ValueError(
                f"Failed to parse JSON from CLI response. "
                f"Response starts with: {text[:200]}"
            )

    def query_deep(
        self,
        prompt: str,
        system: str = "",
        max_tokens: int = 8192,
    ) -> str:
        """Query using the deep/powerful model (Opus) via CLI."""
        return self.query(
            prompt, system=system, model=self.config.model_deep, max_tokens=max_tokens
        )

    def query_deep_json(
        self,
        prompt: str,
        system: str = "",
        max_tokens: int = 8192,
    ) -> dict | list:
        """Query deep model via CLI and parse as JSON."""
        return self.query_json(
            prompt, system=system, model=self.config.model_deep, max_tokens=max_tokens
        )


def create_api(config: LogosConfig, use_max_plan: bool = False) -> ClaudeAPI | MaxPlanAPI:
    """Factory: return MaxPlanAPI (free via CLI) or ClaudeAPI (paid via API).

    Args:
        config: Logos configuration.
        use_max_plan: If True, use Claude Code CLI with Max plan subscription.
                      If False, use the standard Anthropic API.
    """
    if use_max_plan:
        return MaxPlanAPI(config)
    return ClaudeAPI(config)
