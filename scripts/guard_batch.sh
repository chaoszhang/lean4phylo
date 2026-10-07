#!/usr/bin/env bash
# scripts/guard_batch.sh —— 每批收口的固定验收链（DISPATCH「每批收口清单」的机器化）
#
# 用法：
#   bash scripts/guard_batch.sh <期望 jobs 数> [<声明名> ...]
# 例：
#   bash scripts/guard_batch.sh 3203 QuartetDecidesTree Cladogram.iso_of_isSplitOf_iff
#   （<期望 jobs 数> 传 0 = 不检查 job 数）
#
# 做 7 件事（顺序固定，任一硬失败即 exit 1）：
#   ① 正本 → 镜像同步；② 全量 lake build（并核对 job 数）；
#   ③ 零 sorry / 零 axiom 扫描；④ 对给定声明跑 #print axioms（含 sorryAx 兜底）；
#   ⑤ scripts/check_file_imports.sh；⑥ scripts/list_star_claims.sh；⑦ git status。
#
# 环境变量 MIRROR 可覆盖镜像目录（默认 ~/lean4phylo-main）。
# ⚠️ 必须在**镜像**里编译（正本没有物化依赖，lake 会去 GitHub fetch 然后超时）。
set -u

cd "$(dirname "$0")/.." || exit 1
CANON=$(pwd)
MIRROR=${MIRROR:-$HOME/lean4phylo-main}
EXPECT=${1:-0}
shift 2>/dev/null || true
DECLS=("$@")

echo "canonical = $CANON"
echo "mirror    = $MIRROR"
echo "expect    = $EXPECT jobs"
echo "decls     = ${DECLS[*]:-（无）}"

# ① 同步
cp -r "$CANON/Phylo/." "$MIRROR/Phylo/" || { echo '✗ 同步 Phylo/ 失败'; exit 1; }
cp "$CANON/Phylo.lean" "$MIRROR/Phylo.lean" || { echo '✗ 同步 Phylo.lean 失败'; exit 1; }

cd "$MIRROR" || { echo '✗ 镜像不存在'; exit 1; }

# ② 全量构建
LOG=$(mktemp)
~/.elan/bin/lake build > "$LOG" 2>&1
tail -3 "$LOG"
if ! grep -q 'Build completed successfully' "$LOG"; then
  echo '✗ 构建失败（最后 40 行如下）'
  tail -40 "$LOG"
  rm -f "$LOG"
  exit 1
fi
N=$(grep -oE '\([0-9]+ jobs\)' "$LOG" | tail -1 | tr -dc '0-9')
rm -f "$LOG"
echo "jobs = $N"
if [ "$EXPECT" != 0 ] && [ "$N" != "$EXPECT" ]; then
  echo "✗ job 数与期望不符：实际 $N，期望 $EXPECT（新登记模块必须 +1；不涨就怀疑同步/登记没生效）"
  exit 1
fi

# ③ sorry / axiom
if grep -rqE 'sorryAx|^axiom' "$CANON/Phylo"; then
  echo '✗ 发现 sorryAx 或 axiom：'
  grep -rnE 'sorryAx|^axiom' "$CANON/Phylo" | head -5
  exit 1
fi
echo '✓ 零 sorry / 零 axiom'

# ④ #print axioms
if [ "${#DECLS[@]}" -gt 0 ]; then
  PROBE="$MIRROR/Phylo/GuardProbe.lean"
  {
    echo 'import Phylo'
    for d in "${DECLS[@]}"; do echo "#print axioms $d"; done
  } > "$PROBE"
  OUT=$(~/.elan/bin/lake env lean Phylo/GuardProbe.lean 2>&1)
  echo "$OUT"
  if printf '%s' "$OUT" | grep -q 'sorryAx'; then
    echo '✗ 有声明依赖 sorryAx'
    exit 1
  fi
  BAD=$(printf '%s\n' "$OUT" | grep 'depends on axioms' \
    | grep -v -e 'propext' -e 'Classical.choice' -e 'Quot.sound' || true)
  if [ -n "$BAD" ]; then
    echo '✗ 下列声明的公理集超出标准三公理：'
    echo "$BAD"
    exit 1
  fi
  echo '✓ #print axioms 全部只含 [propext, Classical.choice, Quot.sound]'
fi

# ⑤/⑥ 两个既有脚本
bash "$CANON/scripts/check_file_imports.sh" || exit 1
bash "$CANON/scripts/list_star_claims.sh" | tail -3

# ⑦ git
cd "$CANON" || exit 1
echo '=== git status ==='
git status --short
echo '✓ guard 全绿'
