#!/usr/bin/env bash
# Launch one stage of the phase-2 campaign as N concurrent shards on this host.
#
#   difftest/tools/campaign.sh STAGE N JOBS [FIRST LAST] -- [stage args...]
#
# starts shards FIRST..LAST (default 0..N-1) of `dt STAGE --shard i/N`, each with `-j JOBS`,
# detached (setsid nohup), logging to $DT_WORK/logs/STAGE-<tag>.shard-i-of-N.log. Each shard
# writes its own results/<stage>.shard-i-of-N.jsonl, and every stage is resumable, so
# re-running the same command after an interruption continues where it stopped.
#
# Several shard processes, rather than one process with many jobs, keep the Python driver
# (which spawns two subprocesses per llubi case) from becoming the bottleneck.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DT="$HERE/../bin/dt"
: "${DT_WORK:?set DT_WORK}"
stage=$1 n=$2 jobs=$3; shift 3
first=0 last=$((n - 1))
if [ "${1:-}" != "--" ] && [ $# -ge 2 ]; then first=$1 last=$2; shift 2; fi
[ "${1:-}" = "--" ] && shift
tag=$(echo "$*" | tr -c 'A-Za-z0-9,=-' '_' | cut -c1-60)
mkdir -p "$DT_WORK/logs"
for i in $(seq "$first" "$last"); do
  log="$DT_WORK/logs/$stage-${tag}.shard-$i-of-$n.log"
  echo "$(date -u +%FT%TZ) start $stage --shard $i/$n -j $jobs $*" >>"$log"
  setsid nohup "$DT" -j "$jobs" "$stage" --shard "$i/$n" "$@" >>"$log" 2>&1 </dev/null &
  echo "$!" >"$log.pid"
done
echo "launched $stage shards $first..$last of $n (-j $jobs) $*"
