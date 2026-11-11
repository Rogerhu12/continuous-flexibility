#!/usr/bin/env bash
# Mechanical review of one pull request: head, CI of the head, mergeability,
# frozen statement, protected files, forbidden constructs, and the PR's own report.
set -u
R=Rogerhu12/continuous-flexibility
pr=$1
cd "C:/Users/Boyang/Desktop/Math/ContinuousFlexibility"
br=$(gh pr view "$pr" -R "$R" --json headRefName --jq .headRefName)
head=$(gh pr view "$pr" -R "$R" --json headRefOid --jq .headRefOid)
task=${br#line/}
echo "=== PR #$pr $task  head ${head:0:7}  $(gh pr view "$pr" -R "$R" --json isDraft,mergeable,mergeStateStatus,additions,deletions,changedFiles --jq '"draft=\(.isDraft) \(.mergeable)/\(.mergeStateStatus) +\(.additions) -\(.deletions) files=\(.changedFiles)"')"
echo "CI of head: $(gh run list -R "$R" --commit "$head" --json conclusion,status,event --jq '[.[] | "\(.event):\(.status)/\(.conclusion)"] | join(" ")')"
git fetch -q origin "$br" main
base=$(git merge-base origin/main "origin/$br")
node="src/ContinuousFlexibility/Blueprint/$task.lean"
if git cat-file -e "origin/main:$node" 2>/dev/null; then
  a=$(git show "origin/main:$node" | grep -E "^theorem $task\b" ); b=$(git show "origin/$br:$node" | grep -E "^theorem $task\b")
  [ "$a" = "$b" ] && echo "frozen statement: unchanged" || { echo "frozen statement: CHANGED"; echo " main: $a"; echo " pr:   $b"; }
  echo "node file sorry count: $(git show "origin/$br:$node" | grep -cw sorry)"
else
  echo "no blueprint node file (tool task or new file)"
fi
prot=$(git diff --name-only "$base" "origin/$br" -- src/ContinuousFlexibility/Statements src/ContinuousFlexibility/Blueprint/Statements.lean src/ContinuousFlexibility/Blueprint/Assembly.lean src/Challenge src/Solution lakefile.toml lake-manifest.json lean-toolchain .github src/AxiomAudit.lean)
[ -n "$prot" ] && echo "PROTECTED FILES CHANGED: $prot" || echo "protected files: untouched"
other=$(git diff --name-only "$base" "origin/$br" -- src/ContinuousFlexibility/Blueprint | grep -v "Blueprint/$task\(\.lean\|/\)" )
[ -n "$other" ] && echo "other blueprint files changed: $other"
mod=$(git diff --name-status "$base" "origin/$br" | grep '^M' | grep '\.lean$' | awk '{print $2}' | grep -v "Blueprint/$task.lean\|src/ContinuousFlexibility.lean$")
[ -n "$mod" ] && echo "existing lean files modified: $(echo $mod | tr ' ' '\n' | sed 's|src/ContinuousFlexibility/||' | tr '\n' ' ')"
bad=$(git diff "$base" "origin/$br" -- '*.lean' | grep -E '^\+' | grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|maxHeartbeats|maxRecDepth)\b|@\[extern' )
[ -n "$bad" ] && { echo "FORBIDDEN on added lines:"; echo "$bad" | cut -c1-150 | head -8; } || echo "forbidden constructs: none added"
echo "new lean files: $(git diff --name-status "$base" "origin/$br" | grep -c '^A.*\.lean$'), added lean lines: $(git diff --numstat "$base" "origin/$br" -- '*.lean' | awk '{s+=$1} END{print s+0}')"
echo "--- PR body (first 30 lines):"
gh pr view "$pr" -R "$R" --json body --jq .body | head -30 | cut -c1-200
