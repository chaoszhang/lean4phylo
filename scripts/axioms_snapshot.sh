#!/bin/bash
# ============================================================================
#  axioms_snapshot.sh —— `#print axioms` 快照护栏（W38-7 · 外部审计 audit-6）
#
#  ★ 为什么需要它：库内声称「零 sorry / 零 axiom / 零 native_decide」，但除了 CI 里那条
#    `grep "declaration uses 'sorry'"` 之外，**没有任何机器门禁盯着「收口定理到底还依赖什么」**。
#    `#print axioms` 是 Lean 内核自己给的答案（不是声明，是事实）。
#
#  ★ 判据：把关键收口定理的公理集合**逐字**与 `scripts/axioms_expected.txt` 比对，
#    不一致就非零退出。期望文件是**实跑产物**（不是手写的）：
#        bash scripts/axioms_snapshot.sh --update     # 重录期望文件（只在确认变动合理时用）
#
#  ★ 覆盖（至少）：三条已发表定理的收口 ＋ 5 条空转的 `_vacuous_*` ＋ W38-1 的
#    `_order_form_holds` ＋ W36-E 的非退化见证。
#
#  用法：  bash scripts/axioms_snapshot.sh            # 核
#          bash scripts/axioms_snapshot.sh --update   # 重录
#  前置：  `lake build` 已绿（否则 `lake env lean` 找不到 olean）
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

EXPECTED="scripts/axioms_expected.txt"
TMP="AxiomsSnapshot.lean"
ACTUAL="$(mktemp)"

# ── 被核的声明（完全限定名；由 namespace 栈实测推导，见 HANDOVER §9.10）──
LIST=(
  # ① 三条已发表定理的收口
  "Phylo.Stat.ClanPairLaw.twoClanLawGap_holds"
  "NJ.Pauplin.pauplinFormula_gap_of_isBinary"
  "Phylo.Stat.InvariantsRank.treeMarkovFactorGap_holds"
  # ② 5 条「空转」缺口的收口定理（W36-A item 8 改名为 _vacuous_*）
  "Phylo.Stat.Bootstrap.bootstrap_confidence_gap_vacuous_holds"
  "Phylo.Stat.SplitProbabilities.msc_split_probability_object_gap_vacuous_holds"
  "NeighborNet.neighborNetAgglomeration_gap_vacuous_holds"
  "Split.quarnetRules_level1_gap_vacuous_holds"
  "Split.level1QuartetSystem_gap_vacuous_degenerate"
  # ③ W38-1 拆两半后的序关系形态
  "NJ.Dissimilarity.atteson_lemma11_gap_order_form_holds"
  # ④ W36-E 的非退化见证
  "Split.nniDistance_min_gap_nonempty_nontrivial"
)

{
  echo "import Phylo"
  for n in "${LIST[@]}"; do
    echo "#print axioms $n"
  done
} > "$TMP"

lake env lean "$TMP" > "$ACTUAL" 2>&1
st=$?
rm -f "$TMP" "${TMP%.lean}.olean" "${TMP%.lean}.ilean"

if [ "$st" -ne 0 ]; then
  echo "✗ 快照文件本身没跑通（EXIT=$st）—— 先确认 \`lake build\` 已绿，再看下面："
  cat "$ACTUAL"
  rm -f "$ACTUAL"
  exit 1
fi

if [ "${1:-}" = "--update" ]; then
  cp "$ACTUAL" "$EXPECTED"
  echo "✓ 期望文件已重录：$EXPECTED（$(wc -l < "$EXPECTED") 行）"
  rm -f "$ACTUAL"
  exit 0
fi

if diff -u "$EXPECTED" "$ACTUAL"; then
  echo "✓ 公理快照与期望文件逐字一致（${#LIST[@]} 条声明）"
  rm -f "$ACTUAL"
  exit 0
fi
echo
echo "VERDICT: ✗ 公理快照与 $EXPECTED 不一致"
echo "  · 若这是**有意的**变动（例如换了证明路线）：bash scripts/axioms_snapshot.sh --update 并在报告里写明。"
echo "  · 若不该变：说明有人引入了 axiom / sorry / native_decide，或改了被核定理的依赖链。"
rm -f "$ACTUAL"
exit 1
