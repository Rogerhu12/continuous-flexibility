#!/usr/bin/env bash
# Print the modules this branch adds or modifies relative to its merge base with
# main, one per line. Prints nothing on main or when the merge base is unknown.
set -u
[ "${GITHUB_REF_NAME:-}" = main ] && exit 0
git fetch -q --no-tags --depth=400 origin main 2>/dev/null || exit 0
base=$(git merge-base HEAD FETCH_HEAD 2>/dev/null) || exit 0
git diff --name-only --diff-filter=AM "$base" HEAD -- 'src/ContinuousFlexibility/*.lean' |
  while read -r f; do
    [ -f "$f" ] || continue
    m=${f#src/}; m=${m%.lean}; echo "${m//\//.}"
  done
