#!/bin/bash
# Independent check: compile the 1094 attempt in the shared FC view and print axioms of every helper.
set -u
SRC=/Users/kvn/workspace/wt/n74-formal-math/physics-agent/bench/runs/20261124-152609-codex-sol/Erdos1094_erdos_1094.final.lean
set -a; . /Users/kvn/workspace/sandbox/wt/physics-agent-bench/bench/state/host.env; set +a
W="$PA_FC/.lake/pa-work/n74-check-1094"
mkdir -p "$W"
F="$W/Check1094.lean"
# drop the final `end Erdos1094`, append axiom prints inside the namespace, then close it
sed '$d' "$SRC" > "$F"
for t in mod_le_mod_of_not_dvd_choose minFac_gt_iff_no_carries prime_power_dvd_choose_of_dvd_interval \
         exception_multiple_dvd_lcm exception_upper_bound bounded_exception_set_finite \
         dvd_mul_choose_of_interval_coprime exception_quotient_dvd exception_squarefree \
         exception_remainder_bounds finite_exceptions_iff_bounded small_exceptions erdos_1094; do
  echo "#print axioms $t" >> "$F"
done
echo "end Erdos1094" >> "$F"
tail -3 "$SRC" | head -1
cd "$PA_FC"
/usr/bin/time -p lake env lean "$F" > "$W/out.txt" 2>&1
echo "exit=$?"
# join Lean's wrapped lines so each axiom list is on one line
tr '\n' ' ' < "$W/out.txt" | sed -E "s/'(_private[^']*Check1094\.0\.)?/\n'/g" | grep -E "depends on axioms|sorry|error" | sed -E 's/ +/ /g'
echo "sorryAx_mentions=$(grep -c sorryAx "$W/out.txt")"
