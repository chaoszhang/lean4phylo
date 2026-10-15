#!/bin/bash
# ============================================================================
#  list_gaps.sh —— 「开放缺口清单 + 状态 + 卡点」的自动产出（W21 任务 C5-2 / 派单 D3）
#
#  ★ 口径（**写死在此，不再漂移**）：
#    一条「缺口」= 名字里含 gap / Gap **且** 用 `def ... : Prop` 落盘的声明。
#    （本库的缺口一律登记为 `def X : Prop`，**不是** `theorem`：见
#      PerfectPhylogeny.lean §6 的说明「以下两条只是把目标陈述写清楚，
#      非 theorem，不引入任何公理」。）
#
#  ★ 两套口径**同时输出并标差异**（回应协调侧「机械扫 36 条 vs 逐条读 docstring 25 条」的漂移）：
#    口径 A（机械）：`grep -nE '^def +[A-Za-z0-9_]*([Gg]ap|Gap)[A-Za-z0-9_]*'` 直出的条数；
#    口径 B（收口判定）：在 A 的基础上，扣掉「库内已有同名 `…_holds` / `…_proof` 定理」的那些
#            —— 那些是**已收口**的缺口（`def` 按纪律**逐字保留**，故 `def` 仍在库，但真值已证）。
#
#  ★ 诚实声明：本脚本**只做机械扫描**，**不**判定忠实性（那要逐条读文献，机器判不了）；
#    也不判定「卡点」（那要读 docstring）。它给的是**清单与收口状态**，
#    作为「别再把 36/25 两个数各说一遍」的**共同底账**。
#
#  用法：  cd lean4phylo && bash scripts/list_gaps.sh
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

echo "=== 口径 A：机械扫「def 名含 gap/Gap」==="
mapfile -t DEFS < <(grep -rnE '^def +[A-Za-z0-9_]*(gap|Gap)[A-Za-z0-9_]*' Phylo/ | sort)
printf '%s\n' "${DEFS[@]}" | sed 's/^/  /'
echo "  口径 A 条数 = ${#DEFS[@]}"

echo
echo "=== 口径 B：扣掉「库内已有同名 _holds / _proof 定理」的已收口项 ==="
# ⚠️ 必须在**全库** Phylo/ 内搜（收口定理常落在**另一个模块**，如
#    SBD.two_parent_trees_gap 由 TwoParent.two_parent_trees_gap_holds 收口）；
#    并允许**命名空间前缀**（`TwoParent.` / `Split.` 等）。
open=0
closed=0
for line in "${DEFS[@]}"; do
  file="${line%%:*}"
  rest="${line#*:}"
  name="$(printf '%s' "$rest" | sed -E 's/^[0-9]+:def +([A-Za-z0-9_]+).*/\1/')"
  hit="$(grep -rnE "^(theorem|lemma) +([A-Za-z0-9_]+\.)*${name}(_holds|_proof)? *[:({]" Phylo/ 2>/dev/null | head -1)"
  if [ -n "$hit" ]; then
    printf '  [已收口] %-52s %s\n' "$name" "$file"
    printf '           ↳ %s\n' "$hit"
    closed=$((closed+1))
  else
    printf '  [开放  ] %-52s %s\n' "$name" "$file"
    open=$((open+1))
  fi
done
echo "  口径 B：开放 = ${open} · 已收口 = ${closed} · 合计 = $((open+closed))"

echo
echo "=== ★ 与协调侧记录的口径差异（须逐条解释，不要再各说一遍）==="
echo "  · 本脚本只数「def 名含 gap」的登记项；协调侧的 36 条可能含 _gap_correct_shape/_gap_false 等"
echo "    派生名与「结论位」扫法；25 条可能只数了「尚未收口」的。"
echo "  · ⇒ 用本脚本的 A/B 两个数作为底账，差异逐条对；★ 忠实性判定与卡点仍以各 def 的 docstring 为准。"
