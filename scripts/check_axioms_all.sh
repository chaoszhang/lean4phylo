#!/bin/bash
# ============================================================================
#  check_axioms_all.sh —— **全库**公理扫描门禁（2026-10-28，外援 review_v2 #5 / audit_v2 建议 #1）
#
#  ★ 与 `axioms_snapshot.sh` 的分工：
#    · `axioms_snapshot.sh`：**人工挑的 10 条**关键定理，`#print axioms` 逐字比对 —— 精度高、覆盖窄；
#    · 本脚本：**全部 62 条收口定理**（`_holds` / `_proved` / `_proof` / 含 `_vacuous_`），
#      由 `scripts/axioms_all.lean` 在 Lean 里遍历环境自动枚举 —— 覆盖全、粗粒度。
#    两者互补：抽样那份盯住头条定理，这份保证**没有任何一条收口定理偷偷引入信任公理**。
#
#  ★ 判据（两条，都要过）：
#    ① 输出与 `scripts/axioms_all_expected.txt` **逐字一致**（期望文件是实跑产物，不许手写）；
#    ② 输出里**不许出现** `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` ——
#       这三个是「看起来证了、实际没证」或「绕过内核」的入口，出现了就是红灯，不必等 diff。
#
#  用法：  bash scripts/check_axioms_all.sh            # 核（不一致 ⇒ EXIT 1）
#          bash scripts/check_axioms_all.sh --update   # 重录期望文件（只在确认变动合理时用）
#  退出码：0 一致 · 1 不一致（真问题）· 2 环境不对（找不到 `lake`，例如在 Windows 侧直接跑）
#  前置：  `lake build` 已绿（本脚本会 `import Phylo`，需要 olean）
#         ⇒ **必须在 WSL/CI 里跑**：wsl -e bash -lc 'cd <镜像> && bash scripts/check_axioms_all.sh'
# ============================================================================
set -u

cd "$(dirname "$0")/.." || exit 2

LEAN_SRC=scripts/axioms_all.lean
EXPECTED=scripts/axioms_all_expected.txt
OUT="$(mktemp)"
trap 'rm -f "$OUT"' EXIT

if ! command -v lake >/dev/null 2>&1; then
  echo "✗ 找不到 \`lake\` —— 这是**环境不对**（EXIT=2），不是代码失败。"
  echo "  本脚本必须在一个已 \`lake build\` 过的仓库里跑："
  echo "      wsl -e bash -lc 'cd <镜像> && bash scripts/check_axioms_all.sh'"
  exit 2
fi

echo "== 全库公理扫描（#print axioms · 全部收口定理）=="
lake env lean "$LEAN_SRC" > "$OUT" 2>&1
rc=$?
if [ "$rc" -ne 0 ]; then
  echo "✗ Lean 运行失败（EXIT=$rc）—— 先确认 \`lake build\` 已绿："
  tail -20 "$OUT"
  exit 1
fi

echo "扫到 $(head -1 "$OUT")"

# ── 判据 ②：可疑公理（比 diff 更早、更硬）──────────────────────────────────
if grep -qE 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' "$OUT"; then
  echo
  echo "✗ 出现**信任公理/未证明入口** ⇒ 立即红灯："
  grep -nE 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' "$OUT"
  exit 1
fi
echo "  ✓ 无 sorryAx / ofReduceBool / trustCompiler"

if [ "${1:-}" = "--update" ]; then
  cp "$OUT" "$EXPECTED"
  echo "已重录 $EXPECTED（$(wc -l < "$EXPECTED") 行）"
  exit 0
fi

# ── 判据 ①：与期望文件逐字一致 ─────────────────────────────────────────────
if diff -u "$EXPECTED" "$OUT" > /tmp/axall.diff 2>&1; then
  echo "  ✓ 与 $EXPECTED 逐字一致（$(wc -l < "$EXPECTED") 行）"
  echo
  echo "VERDICT: ✓ 全部收口定理的公理依赖与快照一致，无信任公理"
  exit 0
fi

echo
echo "✗ 与期望文件不一致："
head -40 /tmp/axall.diff
echo "…（完整 diff 见 /tmp/axall.diff）"
echo
echo "  处置：若变更是**有意**的（新增/改名收口定理），跑 --update 重录并随提交一起提交；"
echo "        若是**意外**的（某条定理突然多了公理），那就是真问题，别 --update。"
echo
echo "VERDICT: ✗ 公理快照不一致"
exit 1
