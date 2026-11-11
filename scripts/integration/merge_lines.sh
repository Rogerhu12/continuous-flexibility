#!/usr/bin/env bash
# Merge line branches into the current integration branch, one merge commit each.
#
# Usage: bash scripts/integration/merge_lines.sh <Task> [<Task> ...]
#
# Always --no-ff, so that the pull request head itself is an ancestor of main and
# GitHub marks the pull request merged. Expected conflicts (root import, STATUS,
# BlueprintStatus audit lines) are resolved by resolve_merge.py; any other
# conflict stops the script with the merge in progress. The regenerated root
# import is committed separately, never amended into a line's commit.
set -euo pipefail
git fetch -q origin "${@/#/line/}"
for task in "$@"; do
  head=$(git rev-parse --short "origin/line/$task")
  if git merge -q --no-ff --no-edit "origin/line/$task" -m "Merge line/$task ($head)"; then
    echo "$task @$head: clean"
  else
    echo "$task @$head: conflicts: $(git diff --name-only --diff-filter=U | tr '\n' ' ')"
    python -I scripts/integration/resolve_merge.py
    git commit -q --no-edit
    echo "$task @$head: resolved"
  fi
done
python -I scripts/gen_root.py >/dev/null
git add src/ContinuousFlexibility.lean
if ! git diff --cached --quiet; then
  git commit -q -m "Regenerate the root import"
fi
git log --oneline -n $(( $# + 1 ))
