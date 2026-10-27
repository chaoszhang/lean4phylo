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
#
#  ★ 执行环境（W39-7 补写；很重要，否则失败会被误读成「脚本坏了」）：
#    本脚本**必须跑在 Linux（WSL）里**，且 PATH 里有 elan 装的 `lake`/`lean`。
#    在 Windows 原生 shell（PowerShell / Git Bash / cmd）里跑，`lake` 不存在，
#    会是裸的 `EXIT=127`（`lake: command not found`）——**那是环境不对，不是代码失败**。
#    正确跑法：
#        wsl -e bash -lc 'cd ~/lean4phylo-main && bash scripts/axioms_snapshot.sh'
#    （`~/lean4phylo-main` 是有 olean 的构建镜像；canonical 仓库的 `.lake` 只有配置，
#     没有 olean，在那里跑会报 `unknownIdentifier` / 缺 import。）
#    ⇒ 脚本自己做环境自检：找不到 `lake` 就打印人话提示并以 **EXIT=2** 退出，
#      与「快照真的不一致」的 **EXIT=1** 区分开（三态：0 一致 / 1 不一致 / 2 环境不对）。
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

# ── 环境自检：缺 lake 时不要吐裸 127 ────────────────────────────────────────
if ! command -v lake >/dev/null 2>&1; then
  cat >&2 <<'EOF'
✗ 环境不对：PATH 里没有 `lake`（elan 未加载，或当前是 Windows 原生 shell）。

  本脚本必须在 **WSL (Linux)** 里跑，且要有 elan：
      wsl -e bash -lc 'cd ~/lean4phylo-main && bash scripts/axioms_snapshot.sh'

  另外：canonical 仓库的 `.lake` 只有配置、没有 olean，请在构建镜像里跑
  （`~/lean4phylo-main`，用 `bash ~/w28/build.sh` 同步并构建）。

  ⇒ 这不是代码失败，是执行环境不对（EXIT=2）；真不一致才是 EXIT=1。
EOF
  exit 2
fi

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
