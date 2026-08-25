#!/usr/bin/env bash
# Two-binary lean4lean Nat-arith benchmark on the 4.31 toolchain.
# Verified (limb-native seam) vs stock (GMP). Best-of-3 min wall per module;
# cross-checks that both accept the same declaration count.
set -u
cd "$(dirname "$0")"
export LEAN_PATH="."
STOCK=./lean4lean-stock
VERIF=./lean4lean-verified
N=3
TIMEOUT=180
MODS=(SmallInt MulW256 MulW1024 MulW4096 MulW16384 PowMix)

bestof() {  # $1=binary $2=module  -> prints "min_wall checked_line"
  local bin=$1 mod=$2 best="" line=""
  for _ in $(seq "$N"); do
    local t0 t1 out rc
    t0=$(date +%s.%N)
    out=$(timeout "$TIMEOUT" "$bin" "$mod" 2>&1); rc=$?
    t1=$(date +%s.%N)
    if [ "$rc" -ne 0 ]; then echo "FAIL(rc=$rc) ${out:0:40}"; return; fi
    local dt; dt=$(awk "BEGIN{print $t1-$t0}")
    if [ -z "$best" ] || awk "BEGIN{exit !($dt<$best)}"; then best=$dt; line=$out; fi
  done
  echo "$best | $line"
}

printf "%-11s | %-28s | %-28s | %s\n" "module" "stock (GMP)" "verified (limb)" "ratio v/s"
printf -- "------------+------------------------------+------------------------------+---------\n"
for m in "${MODS[@]}"; do
  s=$(bestof "$STOCK" "$m"); v=$(bestof "$VERIF" "$m")
  st=${s%% |*}; vt=${v%% |*}
  sc=${s#*| }; vc=${v#*| }
  if [[ "$st" =~ ^[0-9.]+$ && "$vt" =~ ^[0-9.]+$ ]]; then
    r=$(awk "BEGIN{printf \"%.2f\", $vt/$st}")
    ok=$([ "$sc" = "$vc" ] && echo "" || echo "  !!CHECK-MISMATCH!!")
    printf "%-11s | %6.2fs  %-19s | %6.2fs  %-19s | %5sx%s\n" "$m" "$st" "${sc:0:19}" "$vt" "${vc:0:19}" "$r" "$ok"
  else
    printf "%-11s | %-28s | %-28s | %s\n" "$m" "${s:0:28}" "${v:0:28}" "-"
  fi
done
