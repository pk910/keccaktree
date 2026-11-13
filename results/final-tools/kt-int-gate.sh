#!/bin/bash
# kt-int-gate.sh: wait until a new lean process may start: machine MemAvailable >= 15 GB and the summed RSS of
# all kt-int build units <= 20 GB (budget 30 GB, ~10 GB headroom for the new process). Never kills.
myrss() { for u in kt-int-arm kt-int-rv kt-int-x86 kt-int-x86b kt-int-ip kt-int-ip9 kt-int-ip2 kt-int-ip3 kt-int-x86vl; do cg=/sys/fs/cgroup/system.slice/$u.service/cgroup.procs; [ -f $cg ] && cat $cg; done | while read p; do awk "/VmRSS/{print \$2}" /proc/$p/status 2>/dev/null; done | awk "{s+=\$1} END {print int(s/1048576)}"; }
while true; do
  av=$(awk "/MemAvailable/{print int(\$2/1048576)}" /proc/meminfo); m=$(myrss)
  [ $av -ge 15 ] && [ $m -le 18 ] && exit 0
  sleep 20
done
