#!/usr/bin/env bash
# Kill any `lean` process that has compiled one of the listed files for longer
# than LIMIT seconds, and record it in slow_files.txt. Runs until killed.
# Usage: watchdog.sh <file with module names> <LIMIT seconds>
list=$1; limit=$2
: > slow_files.txt
while sleep 10; do
  ps -eo pid=,etimes=,args= | while read -r pid secs cmd; do
    case "$cmd" in *"/bin/lean "*) ;; *) continue;; esac
    [ "$secs" -gt "$limit" ] || continue
    src=$(echo "$cmd" | grep -o 'src/ContinuousFlexibility/[^ ]*\.lean' | head -1)
    [ -n "$src" ] || continue
    m=${src#src/}; m=${m%.lean}; m=${m//\//.}
    if grep -qx "$m" "$list"; then
      kill "$pid" 2>/dev/null && echo "$m $secs" >> slow_files.txt
    fi
  done
done
