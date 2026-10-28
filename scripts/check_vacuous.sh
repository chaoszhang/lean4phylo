#!/bin/bash
# ============================================================================
#  check_vacuous.sh —— 「空转缺口」的**机械自证** ＋ 「已收口」全表**归类**（W26-B ⇒ W39-3）
#
#  ★ 为什么需要这个脚本（老师 W26 派单 §B 的原话）：
#    「『空转』判定我接受，但它必须有机械护栏 —— 因为『证不出 ⇒ 说它空转』
#      是一条极容易走的逃逸路线。」
#
#  ★ 本脚本回答两个问题，共 **44 行**（= 台账【已收口】**38** ＋【追溯】里那条空转 legacy
#    ＋【判定收档】里 2026-10-28 降级的 **5** 条空转 —— 它们仍是空转，只是不再算「已收口」）：
#
#    (1) 每条**登记为空转**的缺口，依据必须是**一条可复跑的定理**。判定类型三选一：
#        ∃自由槽       —— `def` 把要造的对象写成了 `∃` 绑定的变量 ⇒
#                         证据必须是「对任意输入该 Prop 恒真」的定理（`_holds` / `_iff_*`）。
#        假设槽         —— 证据必须是「前提恒真」或「前提不可满足」的定理。
#        已证半边冒充   —— 证据必须是指出「哪半边已证」的定理（旧 `def` 只是它的重述）。
#
#    (2) 每条**已收口**的缺口（W35 审计的 44 行）必须**有归类**，三选一：
#        实例     —— 库内有一条定理把该缺口的结论用在**具体对象**上（具体 `Fin 4`／具体树／
#                    具体 `δ`／具体数值）。依据 = 那条定理名 ⇒ **机械可查**。
#                    注意：把一条已证的 `∀…` 定理特化不算实例（零信息），见 W39-3 报告。
#        自由槽   —— 6 条 VACUOUS 白名单（与 `gap_ledger.py` 的 `VACUOUS` 逐个对齐）。
#        无实例   —— 已复核：库里**没有**非退化的具体对象用法。必须写出原因，不算缺陷
#                    （W39-3 的「可造性预判」：能造 / 不能造 / 缺什么器材）。
#
#  ★ 判据：`grep -F` 不到依据 ⇒ **该条判定无效**，脚本以非零码退出，
#    并要求把它退回 `[真开放]`（老师在派单里写死的处置）；有「未归类」的已收口条目同样非零退出
#    （已收口条目数一变，本脚本就必须跟着补一行 —— 债务不能悄悄长出来）。
#
#  用法：  bash scripts/check_vacuous.sh        （须在 WSL/Linux 里跑，见 axioms_snapshot.sh 的说明）
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

LEDGER="scripts/gap_ledger.py"
rows=0; ok=0; bad=0
n_inst=0; n_free=0; n_none=0; n_noevid=0
# n_noevid = 「无实例」的条数（仅人工原因、**无机械依据**）。2026-10-28 外援 review_v2 指出：
# 这些行原来也 ok=$((ok+1))，导致汇总行把 13 条无依据的算进「有机械依据」⇒「44/44 有机械依据」是失真。

printf '%-42s | %-6s | %-9s | %s\n' "缺口名" "归类" "机械依据" "位置 / 原因"
printf '%s\n' "----------------------------------------------------------------------------------------------------------------------"

# check <缺口名> <归类> <依据的固定串> <备注>
#   依据的固定串必须是 Phylo/ 下**真的出现**的一段源码：定理用 "theorem <名>"，
#   example 用那段唯一的字面量。用 `grep -F` 而不是正则 —— 名字里有 `.`、括号时不会误判。
check() {
  local name="$1" cls="$2" pat="$3" note="$4"
  rows=$((rows+1))
  case "$cls" in
    实例)   n_inst=$((n_inst+1)) ;;
    自由槽) n_free=$((n_free+1)) ;;
  esac
  local hit
  hit="$(grep -rnF "$pat" --include='*.lean' Phylo/ 2>/dev/null | head -1)"
  if [ -n "$hit" ]; then
    local loc="${hit%%:*}" rest ln
    rest="${hit#*:}"; ln="${rest%%:*}"
    printf '%-42s | %-6s | %-9s | %s:%s\n' "$name" "$cls" "是" "$loc" "$ln"
    ok=$((ok+1))
  else
    printf '%-42s | %-6s | %-9s | %s\n' "$name" "$cls" "**否**" "grep -F 不到 ⇒ 撤回标注、退回 [真开放]"
    bad=$((bad+1))
  fi
  [ -n "$note" ] && printf '%-42s   ↳ %s\n' "" "$note"
}

# noinst <缺口名> <原因>：**无实例（已复核）**，不要求定理依据，但必须写清原因
noinst() {
  local name="$1" reason="$2"
  rows=$((rows+1)); n_none=$((n_none+1)); n_noevid=$((n_noevid+1))
  # ★ 不增加 ok：它们**合规**（口径只要求「有归类」），但**没有机械依据**，不能计入 ok。
  printf '%-42s | %-6s | %-9s | %s\n' "$name" "无实例" "—" "已复核，无具体对象用法"
  printf '%-42s   ↳ %s\n' "" "$reason"
}

# ══════════════════════════════════════════════════════════════════════════
#  一、6 条由 gap_ledger.py 的 VACUOUS 台账登记的「空转」＋ 1 条已修复的旧形态
# ══════════════════════════════════════════════════════════════════════════
check "quarnetRules_level1_gap" "自由槽" "theorem quarnetRules_level1_gap_vacuous_holds" \
      "四条规则（consistent/minimallyDense/cyclative/saturated）与 displayedBy/isTypeI 全被 ∃ 绑定 ⇒ 取退化数据即真；另有 _degenerate 见证"
check "level1QuartetSystem_gap" "自由槽" "theorem level1QuartetSystem_gap_vacuous_degenerate" \
      "QuartetSystem / multiplicity 同样被 ∃ 绑定；只有退化见证（PUnit），无一般形态定理"
check "neighborNetAgglomeration_gap" "自由槽" "theorem neighborNetAgglomeration_gap_vacuous_holds" \
      "残量把 Prop 钉成「每个 X 上存在星形族」（_iff_star）；输入 d 与 ∃Step 双双消失"
check "canonicalSplitDecomposition_gap_correct_shape_legacy" "自由槽" \
      "theorem canonicalSplitDecomposition_gap_correct_shape_legacy_holds" \
      "只需「∃ 某个分解」，取退化 δ₀ = δ − M·Σδ_s（非对角任意负）即真 ⇒ 不是 BdD Thm 2｜W36 已降 _legacy（[追溯]）"
check "bootstrap_confidence_gap" "自由槽" "theorem bootstrap_confidence_gap_vacuous_holds" \
      "「∃ Ω TrueSplit p」三个自由槽 ⇒ 取 Ω := Empty 三条 ∀ω 全空真 ⇒ Prop ↔ True"
check "msc_split_probability_object_gap" "自由槽" "theorem msc_split_probability_object_gap_vacuous_holds" \
      "取 σ := Unit、P r = if IsTrivialSplit r then 1 else (if r = r₀ then 2n−6 else 0) 即满足账目 2n+(2n−6)=2(2n−3)"

# ══════════════════════════════════════════════════════════════════════════
#  二、已收口 38 条 ＋ 追溯 1 条 ＋ 判定收档 5 条 = 44 条：逐条归类（W39-3 覆盖 7 → 44；W40 降级后重算）
# ══════════════════════════════════════════════════════════════════════════
# ── ① 有非退化实例（25 条）────────────────────────────────────────────────
check "nniDistance_min_gap" "实例" "theorem tree_nniDist₁₂_eq_one" \
      "Fin 4 具体两树、真实 1 步（比 _nonempty:650 的 0 步自反强）"
check "circularIndicatorFullRank_gap" "实例" "theorem alm_injective_of_three_le" \
      "Fin n 弧族 Alm 上的单射性，与 §7 逆矩阵同一套工具"
check "circularDistanceRealization_gap_corrected" "实例" "theorem circularRealization_fin4" \
      "X := Fin 4 上显式给出 (F,w)；F,w 须逐点实现 d，取 F=∅,w=0 只对零距离成立"
check "circularWeights_realization_gap" "实例" "theorem circularWeights_realization_gap_fin_le_five" \
      "本 gap 在 n = 3 ∧ 4 ∧ 5 的逐字实例（X := Fin n、f := refl）"
check "atteson_lemma11_gap_order_form" "实例" "theorem atteson_lemma11_gap_order_form_at_exDiss" \
      "★W39-3 新造：exDiss（4 叶真树度量）上逐对算出 δmin = 5、间隙 10 = 2(n−3)δmin，**不走** _order_form_holds"
check "mnCorollary_gap" "实例" "theorem mnCorollary_gap_at_thresholdRule" \
      "★W39-3 新造：C := ThresholdRule k t（t ≤ k < 2t）上六条前提逐条证 ⇒ 阈值参数由规则本身确定"
check "QuartetBridgeGap" "实例" "theorem fitchCostGen_quartet" \
      "见证是具体 7 顶点树 quartetTree（Fin 4），逐 σ 计算 fitchCostGen"
check "pauplinFormula_gap" "实例" "theorem ex4_bmeLength" \
      "4 叶端到端 15 = l(T)（BMELeastSquares）；量词收到 e ∈ edgeSet 后实质证成"
check "pauplinEdgeCoeff_gap_correct_shape" "实例" "theorem ex4S_normalization" \
      "4 叶逐边归一化和 = 2（真边归一化）；原形态 not_edgeCoeff_forall_eq_two 为假"
check "MultiStatePairwiseInsufficiencyGap" "实例" "theorem pairwise_displays_fitchMeachamF3" \
      "见证矩阵钉为 F₃（5 taxa × 3 字符）；两两可解 + 整体不可解"
check "weakCompatibilityRealization_gap" "实例" "theorem weakCompatibilityRealization_gap_card_four" \
      "card X = 4 的逐字数值实例（另有 _card_five）"
check "fourPointOfSplitMetricSum_gap" "实例" "example : FourPointStd (fun x y : Fin 4 =>" \
      "具体 cexF2（Fin 4、w≡1）上证 FourPointStd；与下一条共享同一个 example"
check "fourPointOfSplitMetricSum_gap_correct_shape" "实例" "example : FourPointStd (fun x y : Fin 4 =>" \
      "同一实例（cexF2）；注册形态 _proof 复用它"
check "multinomial_weight_count_gap" "实例" "weightOf σ = (fun i : Fin 2 => if i = 0 then 2 else 0)" \
      "n=2,w=(2,0) 的具体值；另有 (1,1)/(0,2)/(1,1,1)/(3,0,0) 共 5 个 example"
check "kolmogorov_extension_gap" "实例" "theorem kolmogorov_extension_gap_nonempty" \
      "Ω₀ := Bool、coin 上的具体测度，边缘 / 联合乘积逐个算（另 _bool_mass）"
check "TreeMarkovFactorGap" "实例" "theorem gmmFreq_factorizable" \
      "★ 旧 def 只是「给定因子分解 ⇒ rank ≤ 4」的重述（这半边早证）；W25 改强为 IsTreeModelFreq P → ∃ A B 并证成"
check "rankedTree_card_gap" "实例" "theorem card_mergeHistories_four_eq_H" \
      "n = 4 → H₄ 的具体计数（另有 n = 5 → 180）"
check "rankedFiberCount_gap" "实例" "theorem rankedFiberCount_four_all" \
      "n = 4 一般 f 上的纤维计数（另有 n = 3）"
check "sd2012_eq4_uniform_rates_gap" "实例" "theorem eq4_two_uniform_rates" \
      "m = 2 独立实例，与一般公式互核"
check "ranked4_probability_gap" "实例" "ranked4_probability_gap_proved 1 (by norm_num)" \
      "t = 1 的具体概率表（2+16 纤维）；p 被三式钉住，非自由槽"
check "YHKClanLawGap" "实例" "theorem yhkLawFour_clanEvent_two" \
      "n = 4 整条；RHS 取 1/3 的非 0/1 值，退化分布填不出"
check "TwoClanLawGap" "实例" "theorem yhkLawFour_twoClanEvent" \
      "n = 4 整条；载体 RankedTree n ＋ prob ≡ 1/H n 显式装配"
check "card_trivial_splits_gap" "实例" "theorem card_trivial_splits_four" \
      "n = 4 → 8（另有可计算代理 example）"
check "two_parent_trees_gap" "实例" "theorem treeP1_displays_prof" \
      "显式 T₁/T₂（treeP1/treeP2，Fin 6）展示同一 prof"
check "two_parent_trees_gap_correct_shape" "实例" "theorem two_parent_trees_gap_correct_shape_holds" \
      "同一对显式树 ＋ ③ 分类定理（precisely two）＋ sP2a ∈ T₂∖T₁ 的非退化见证"

# ── ② 无实例（已复核）13 条 + 可造性预判 ───────────────────────────────────
noinst "atteson_reduction_gap_correct_shape" \
      "可造性：只有零信息特化（_proved 对一切 δ 成立）。非平凡实例要显式给 (Y,q,δm) 与四条取值等式 ⇒ 缺 mergeDissim 在具体 δ 上的求值引理"
noinst "BinaryConnectedEqualsSideGap" \
      "可造性：只有特化（_holds 对一切 T,A）。非平凡实例要在具体 Cladogram 上写出 ℓ : T.V → Bool ⇒ 缺 T.V 的枚举层（treeP1 的载体是内部构造）"
noinst "greedy_gap_correct_shape" \
      "可造性：需在具体 Phylogram（T1234/star4Tree）上算每 k 的 PD 最大化子集；PD 是实数和、decide 不适用 ⇒ 缺 PD 的具体值表"
noinst "pdExchange_gap" \
      "可造性：同上（需逐 x 比较 PD 增量）；同上缺口"
noinst "fourPointCharacterization_gap" \
      "可造性：只有特化。非平凡实例要构造 δ := Σ w_s·δ_s 并证 (B1)/(B2) = 本文件 §7.1 登记的瓶颈 ⇒ 缺 (B2) 的隔离指数层"
noinst "notIsDSplit_of_splitMetricSum_gap" \
      "可造性：不能造 —— _holds 以 noWRealizer_exists_gap 为前提，非平凡实例等价于证 (B2) 瓶颈本身"
noinst "canonicalSplitDecomposition_gap" \
      "可造性：只有特化。非平凡实例要给具体 δ 的 (F,c,δ₀) 分解表 —— _holds 走 dSplits 基数下降，不产出可读分解 ⇒ 缺求分解的计算层"
noinst "noWRealizer_exists_gap" \
      "可造性：需在具体 (F,w,S) 上算出 F.filter (bPairW …) 为空；bPairW 取值依赖 Real，decide 不可用 ⇒ 缺可计算复刻"
noinst "weakCompatibilityRealization_gap_weights" \
      "可造性：需具体弱相容 F + w 并算出 isolationIndex = 2(w_s + …)；库内可计算复刻（§8.14.1 sepQ）只到 n=4 且未与注册形态接桥"
noinst "variance_empFreq_gap" \
      "可造性：不能造（W36-C 已记）—— 第五条前提 ∫ ind = m.freq.p 要具体 MSC 频率表，且 iIndepFun 要在乘积测度上验 ⇒ 缺 MSC 频率 ↔ ind 的桥"
noinst "evansSpeed_general_gap" \
      "可造性：只能造零信息特化（m=0 空族 / χ≡1 计数）。有信息量要字符正交性，而本 gap 的 χ 是两条公理的任意函数，与 Mathlib AddChar 无桥"
noinst "MultiLocusPosteriorConcentrationGap" \
      "可造性：能造但成本 ≫ 收益（ι=Fin 2、perLocus=(1,e^{−n}) 要 Tendsto 商 + exp 衰减）；且该条无假设已证成，实例只是把已证结论算一遍"
noinst "quartetMeanEquidistributed_gap" \
      "可造性：需 Fin 4 上 3 个拓扑的 quartetDistFull 值表（9 个有序对）求和 = 48 ⇒ 缺 quartetDistFull 在具体 quartet 上的求值引理"

printf '%s\n' "----------------------------------------------------------------------------------------------------------------------"
echo "合计 ${rows} 行 · 有机械依据 ${ok}（＝实例 ${n_inst} ＋ 自由槽 ${n_free}）· 无机械依据 ${n_noevid}（＝无实例，仅人工原因）· 依据缺失 ${bad}"
echo "归类：实例 ${n_inst} · 自由槽 ${n_free} · 无实例 ${n_none}（= $((n_inst+n_free+n_none))，应为 44）"

# ── 台账一致性 ①：VACUOUS 里的键必须都在上面出现 ──────────────────────────
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

# 2026-10-28：5 条空转从「已收口」降「判定收档」（老师批），它们仍在本表里 ⇒ 对齐时要加回来。
DEMOTED_VACUOUS=5

# ── 台账一致性 ②：已收口条目数变了就必须补归类（债务不能悄悄长出来）──────
echo
echo "== 与 list_gaps.sh 的【已收口】条目数对齐 =="
if command -v python3 >/dev/null 2>&1; then
  closed="$(bash scripts/list_gaps.sh B 2>/dev/null |
    awk '/【已收口】/{f=1;next} /【/{f=0} f' |
    grep -cE '^ {4}[A-Za-z0-9_]+ +(Phylo/)?[A-Za-z0-9_/]+\.lean:[0-9]+')"
  if [ -n "$closed" ] && [ "$closed" -gt 0 ] 2>/dev/null; then
    # +1 = 【追溯】里那条空转 legacy；+5 = 2026-10-28 老师批的 5 条降级（已收口 → 判定收档），仍在表内
    want=$((closed + 1 + DEMOTED_VACUOUS))
    echo "台账【已收口】= ${closed} 条，+1 条空转 legacy ＋${DEMOTED_VACUOUS} 条降判定收档的空转 ⇒ 应覆盖 ${want} 行；本脚本 ${rows} 行"
    if [ "$rows" -ne "$want" ]; then
      echo "  ✗ 覆盖数不符 ⇒ 台账新增/删除了已收口条目，请在本脚本里补一行（归类 + 依据/原因）"
      bad=$((bad+1))
    else
      echo "  ✓ ${rows} 行全覆盖：每条都有归类，无「未归类」"
    fi
  else
    echo "  ⚠ 取不到【已收口】条目数（跳过对齐；不影响上面的逐条判定）"
  fi
else
  echo "  ⚠ 无 python3（跳过对齐）"
fi

if [ "$bad" -ne 0 ]; then
  echo
  echo "VERDICT: ✗ 有 ${bad} 项不达标 ⇒ 按老师 W26 §B：撤回对应标注、退回 [真开放]"
  exit 1
fi
echo
echo "VERDICT: ✓ ${rows}/${rows} 条全部有归类（有机械依据 ${ok} ＝ 实例 ${n_inst} ＋ 自由槽 ${n_free}；无实例 ${n_none} 仅人工原因、无机械依据）"
