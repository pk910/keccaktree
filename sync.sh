#!/bin/bash
# sync worktree lean/ to /root/kt-lib/lean and build the given targets (memory capped)
cd "$(dirname "$0")"
sshpass -p 'ClaudePass123' rsync -a -e "ssh -o StrictHostKeyChecking=no" --exclude .lake --exclude .git lean/ root@2.28.133.253:/root/kt-lib/lean/
[ $# -eq 0 ] && exit 0
sshpass -p 'ClaudePass123' ssh -o StrictHostKeyChecking=no root@2.28.133.253 "cd /root/kt-lib/lean && export PATH=/root/.elan/bin:\$PATH && systemd-run --scope -q -p MemoryMax=10G lake build $* 2>&1 | grep -v '^✔\|^⣿\|^info' | tail -${TAILN:-60}"
