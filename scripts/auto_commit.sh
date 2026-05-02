#!/bin/bash
# Auto-commit pipeline data to git every N minutes during active runs.
# Usage: nohup bash scripts/auto_commit.sh &
#
# Commits any new/changed files in data/ to git and pushes to origin.
# Runs until manually killed or no new changes for 30 consecutive checks.
#
# This ensures all pipeline output is Bitcoin-stamped via GitHub Actions.

INTERVAL_SECONDS=300  # 5 minutes
MAX_IDLE_CHECKS=30    # Stop after 30 checks (~2.5 hours) with no changes
REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"

cd "$REPO_DIR" || exit 1

idle_count=0
total_commits=0

echo "[auto-commit] Started at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "[auto-commit] Repo: $REPO_DIR"
echo "[auto-commit] Interval: ${INTERVAL_SECONDS}s"

while true; do
    sleep "$INTERVAL_SECONDS"

    # Stage all data files
    git add data/ 2>/dev/null

    # Check if there are changes to commit
    if git diff --cached --quiet 2>/dev/null; then
        idle_count=$((idle_count + 1))
        echo "[auto-commit] $(date -u +%H:%M:%S) No new data (idle: $idle_count/$MAX_IDLE_CHECKS)"

        if [ "$idle_count" -ge "$MAX_IDLE_CHECKS" ]; then
            echo "[auto-commit] No changes for $MAX_IDLE_CHECKS checks. Stopping."
            break
        fi
        continue
    fi

    idle_count=0
    total_commits=$((total_commits + 1))

    # Count what's new
    new_proofs=$(git diff --cached --name-only | grep "data/logos/proofs/" | wc -l | tr -d ' ')
    new_logs=$(git diff --cached --name-only | grep "data/logos/logs/" | wc -l | tr -d ' ')
    new_flags=$(git diff --cached --name-only | grep "data/logos/flags/" | wc -l | tr -d ' ')
    new_synthesis=$(git diff --cached --name-only | grep "data/synthesis/" | wc -l | tr -d ' ')
    total_proofs=$(ls data/logos/proofs/*.json 2>/dev/null | wc -l | tr -d ' ')

    # Commit
    git commit -m "Pipeline checkpoint #${total_commits} — ${total_proofs}/266 proofs (${new_proofs} new proofs, ${new_logs} logs, ${new_flags} flags, ${new_synthesis} synthesis)

Auto-committed by scripts/auto_commit.sh during active pipeline run.

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>" 2>/dev/null

    echo "[auto-commit] $(date -u +%H:%M:%S) Committed: ${new_proofs} proofs, ${new_logs} logs, ${new_flags} flags (total: ${total_proofs}/266)"

    # Push (handle rebase if Bitcoin timestamp commits arrived)
    if ! git push origin main 2>/dev/null; then
        git pull --rebase origin main 2>/dev/null && git push origin main 2>/dev/null
    fi

    if [ $? -eq 0 ]; then
        echo "[auto-commit] $(date -u +%H:%M:%S) Pushed to origin (will be Bitcoin-stamped)"
    else
        echo "[auto-commit] $(date -u +%H:%M:%S) WARNING: Push failed, will retry next cycle"
    fi
done

echo "[auto-commit] Finished. Total commits: $total_commits"
