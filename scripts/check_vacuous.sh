#!/bin/bash
# ============================================================================
#  check_vacuous.sh —— 「空转缺口」的**机械自证**（W26 任务 B）
#
#  ★ 为什么需要这个脚本（老师 W26 派单 §B 的原话）：
#    「『空转』判定我接受，但它必须有机械护栏 —— 因为『证不出 ⇒ 说它空转』
#      是一条极容易走的逃逸路线。」
#
#  ★ 判定类型（三选一，必须能指出**一条定理**）：
#    ∃自由槽       —— `def` 把要造的对象写成了 `∃` 绑定的变量 ⇒
#                     证据必须是「对任意输入该 Prop 恒真」的定理（`_holds` / `_iff_*`）。
#    假设槽         —— 证据必须是「前提恒真」或「前提不可满足」的定理。
#    已证半边冒充   —— 证据必须是指出「哪半边已证」的定理（旧 `def` 只是它的重述）。
#
#  ★ 判据：`grep` 不到依据定理 ⇒ **该条「空转」判定无效**，脚本以非零码退出，
#    并要求把它退回 `[真开放]`（老师在派单里写死的处置）。
#
#  用法：  bash scripts/check_vacuous.sh
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

LEDGER="scripts/gap_ledger.py"
ok=0
bad=0
rows=0

printf '%-46s | %-12s | %-52s | %-6s | %s\n' "缺口名" "判定类型" "机械依据定理名" "可复跑" "证据位置"
printf '%s\n' "--------------------------------------------------------------------------------------------------------------------------------------------"

check() {
  # $1 缺口名  $2 判定类型  $3 依据定理  $4 备注
  local name="$1" kind="$2" thm="$3" note="$4"
  rows=$((rows+1))
  local hit
  hit="$(grep -rnE "^(theorem|lemma) +([A-Za-z0-9_]+\.)*${thm} *[:({]" Phylo/ 2>/dev/null | head -1)"
  if [ -n "$hit" ]; then
    local loc="${hit%%:*}"
    local rest="${hit#*:}"
    local ln="${rest%%:*}"
    printf '%-46s | %-12s | %-52s | %-6s | %s:%s\n' "$name" "$kind" "$thm" "是" "$loc" "$ln"
    if [ -n "$note" ]; then
      printf '%-46s   ↳ %s\n' "" "$note"
    fi
    ok=$((ok+1))
  else
    printf '%-46s | %-12s | %-52s | %-6s | %s\n' "$name" "$kind" "$thm" "**否**" "grep 不到 ⇒ 撤回「空转」标注、退回 [真开放]"
    bad=$((bad+1))
  fi
}

# ── 6 条由 gap_ledger.py 的 VACUOUS 台账登记的「空转」 ─────────────────────
check "quarnetRules_level1_gap" "∃自由槽" "quarnetRules_level1_gap_vacuous_holds" \
      "四条规则（consistent/minimallyDense/cyclative/saturated）与 displayedBy/isTypeI 全被 ∃ 绑定 ⇒ 取退化数据即真；另有 _degenerate 见证"
check "level1QuartetSystem_gap" "∃自由槽" "level1QuartetSystem_gap_vacuous_degenerate" \
      "QuartetSystem / multiplicity 同样被 ∃ 绑定；只有退化见证，无一般形态定理"
check "neighborNetAgglomeration_gap" "∃自由槽" "neighborNetAgglomeration_gap_iff_star" \
      "残量把 Prop 钉成「每个 X 上存在星形族」；输入 d 与 ∃Step 双双消失（另有 _holds 直接证成）"
# ★ W36：本 `def` 已降级为 `…_correct_shape_legacy`（进 `[追溯]`）；空转事实不变，键与依据同步改名。
check "canonicalSplitDecomposition_gap_correct_shape_legacy" "∃自由槽" "canonicalSplitDecomposition_gap_correct_shape_legacy_holds" \
      "只需「∃ 某个分解」，取退化 δ₀ = δ − M·Σδ_s（非对角任意负）即真 ⇒ 不是 BdD Thm 2"
check "bootstrap_confidence_gap" "∃自由槽" "bootstrap_confidence_gap_iff_true" \
      "「∃ Ω TrueSplit p」三个自由槽 ⇒ 取 Ω := Empty 三条 ∀ω 全空真 ⇒ Prop ↔ True（另有 _holds）"
check "msc_split_probability_object_gap" "∃自由槽" "msc_split_probability_object_gap_vacuous_holds" \
      "取 σ := Unit、P r = if IsTrivialSplit r then 1 else (if r = r₀ then 2n−6 else 0) 即满足账目 2n+(2n−6)=2(2n−3)，对一切 n ≥ 3 恒真"

# ── 第 7 条：旧形态空转、但**已被改强修复**（不计入 VACUOUS 台账）────────────
check "TreeMarkovFactorGap" "已证半边冒充" "rank_flatAB_le_four_of_factor" \
      "旧 def 只是「给定因子分解 ⇒ rank ≤ 4」的逐字重述（这半边早已证）；W25 已改强为 IsTreeModelFreq P → ∃ A B, … 并证成（treeMarkovFactorGap_holds），四要素见 commit 497766c。★ W36 注：「rank_flatAB_le_four_of_factor」是**改强前**旧 def 的依据定理（旧 def 已废），现登记的是**改强后**形态「treeMarkovFactorGap_holds」；本条**保留不撤**"

printf '%s\n' "--------------------------------------------------------------------------------------------------------------------------------------------"
echo "合计 ${rows} 行 · 有机械依据 ${ok} · 无依据 ${bad}"

# ── 台账一致性：VACUOUS 里的键必须都在上面 6 行里出现 ──────────────────────
echo
echo "== 与 gap_ledger.py 的 VACUOUS 台账对齐 =="
vkeys="$(sed -n '/^VACUOUS = {/,/^}/p' "$LEDGER" | grep -oE '"[A-Za-z0-9_]+": *$|"[A-Za-z0-9_]+":' | tr -d '":' | sort -u)"
echo "VACUOUS 键（${LEDGER}）："
echo "$vkeys" | sed 's/^/  - /'
for k in $vkeys; do
  if ! grep -q "^check \"$k\"" "$0"; then
    echo "  ✗ 台账里有、本脚本没有机械依据：$k ⇒ 要么补依据，要么从 VACUOUS 删掉"
    bad=$((bad+1))
  fi
done

if [ "$bad" -ne 0 ]; then
  echo
  echo "VERDICT: ✗ 有 ${bad} 项缺机械依据 ⇒ 按老师 W26 §B：撤回「空转」标注、退回 [真开放]"
  exit 1
fi
echo
echo "VERDICT: ✓ 7/7 条「空转」都有可复跑的定理依据"
