#!/bin/bash
# kt-int disk guard: every 10 min, if free disk < 30 GB, truncate the compiled-C outputs (.c) of finished modules in
# kt-int: > 1 MB, mtime older than 60 min, a .c.hash present, NOT hard-linked (-links 1: a link's inode is shared
# with another workspace and frees nothing).  .c.hash and mtime kept (lake trusts the hash; proofs read only .olean).
# Logged to /root/kt-int-logs/truncated_c2.txt as "<size> <path>".
cd /root/kt-int/lean/.lake/build/ir || exit 1
while true; do
  a=$(df -BG --output=avail / | tail -1 | tr -dc 0-9)
  if [ "$a" -lt 30 ]; then
    find . -name "*.c" -size +1M -mmin +60 -links 1 | while read f; do
      [ -f "$f.hash" ] || continue
      s=$(stat -c %s "$f"); m=$(stat -c %Y "$f")
      truncate -s 0 "$f" && touch -d "@$m" "$f" && echo "$s $f" >> /root/kt-int-logs/truncated_c2.txt
    done
    echo "$(date +%T) free ${a}G -> $(df -BG --output=avail / | tail -1 | tr -d ' ')" >> /root/kt-int-logs/diskguard.log
  fi
  sleep 600
done
