#!/usr/bin/env bash
# scripts/guard_batch.sh —— 每批收口的固定验收链（DISPATCH「每批收口清单」的机器化）
#
# 用法：
#   bash scripts/guard_batch.sh <期望 jobs 数> [<声明名> ...]
# 例：
#   bash scripts/guard_batch.sh 3203 QuartetDecidesTree Cladogram.iso_of_isSplitOf_iff
#   （<期望 jobs 数> 传 0 = 不检查 job 数）
#
# 做 8 件事（顺序固定，任一硬失败即 exit 1）：
#   ① 正本 → 镜像同步；② 全量 lake build（并核对 job 数）；
#   ③ 零 sorry / 零 axiom 扫描；④ 对给定声明跑 #print axioms（含 sorryAx 兜底）；
#   ④′ **自动暂存「未登记」的在建 .lean**（并行开发时别的 agent 的在建文件不该让本批变红；
#      验收结束（含失败退出）用 trap 自动放回；若期间被 agent 重建则保留新写的、丢弃暂存副本）；
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

# ③ sorry / axiom（**源码级**正则；只扫「根模块可达」的模块 —— 未登记的在建文件不算库的一部分）
MODS=$(grep -oE '^import [A-Za-z0-9_.]+' "$CANON/Phylo.lean" | sed 's/^import //' | tr '.' '/')
MODS_SP=$(echo $MODS)
PAT='^[[:space:]]*sorry[[:space:]]*$|:= *sorry|by *sorry|^axiom '
BAD=""
for m in $MODS; do
  f="$CANON/$m.lean"
  [ -f "$f" ] || continue
  if grep -qE "$PAT" "$f"; then BAD="$BAD $f"; fi
done
if [ -n "$BAD" ]; then
  echo "✗ 库内（根模块可达）发现 sorry/axiom："
  for f in $BAD; do grep -nE "$PAT" "$f" | head -3; done
  exit 1
fi
echo '✓ 零 sorry / 零 axiom（根模块可达模块，源码级）'
# 另：报告**未登记**文件里的 sorry（仅提示，不算失败 —— 那些是在建文件）
STRAY=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  rel=${f#"$CANON"/}
  mod=${rel%.lean}
  mod=${mod//\//.}
  case " $MODS_SP " in
    *" $mod "*) ;;
    *) STRAY="$STRAY $f" ;;
  esac
done <<< "$(grep -rlE '^[[:space:]]*sorry[[:space:]]*$|:= *sorry|by *sorry' "$CANON/Phylo" 2>/dev/null || true)"
if [ -n "$STRAY" ]; then
  echo 'ℹ️ 未登记文件里仍有 sorry（不算失败，但提交前应清零）：'
  echo "$STRAY"
fi

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

# ④′ **自动暂存**「未登记」的在建 .lean（否则 check_file_imports.sh 会红）；验收结束（含失败退出）自动放回。
#     —— 并行开发时其它 agent 的在建文件不该让本批验收变红（协调侧此前靠手工暂存，现固化）。
#     ⚠️ `MODS`/`MODS_SP` 是**斜杠形式**（如 `Phylo/Core`），本循环的比较也一律用斜杠形式；
#     曾因「斜杠 vs 点号」不一致把所有模块误判为未登记、把整个 Phylo/ 暂存走 —— 故加了两道保险：
#     (a) 需暂存文件数 > 8 视为异常，立刻放回并放弃暂存；(b) 恢复以暂存目录的实际内容为准。
#     ⚠️ 2026-10-09 W10 修正：扫描范围从 `$CANON`（整个仓库）**收紧到 `$CANON/Phylo`** ——
#     与 `check_file_imports.sh`（它只扫 `Phylo/`）对齐。此前会把并行 agent 放在
#     `scripts/*.lean` 的 **scratch 文件**也算成「未登记模块」，个数一多就触发阈值 (a)
#     而**整个暂存被放弃**（W10 实测踩到：6 个文件 > 旧阈值 5）。阈值同时放宽到 8。
STASHDIR=$(mktemp -d)
STASHED=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  rel=${f#"$CANON"/}
  [ "$rel" = "Phylo.lean" ] && continue          # 根模块本身不是「未登记文件」
  mod=${rel%.lean}                               # 保持斜杠形式，与 MODS_SP 同形
  case " $MODS_SP " in
    *" $mod "*) ;;                                # 已登记 ⇒ 保留
    *)
      mkdir -p "$STASHDIR/$(dirname "$rel")"
      if mv "$f" "$STASHDIR/$rel"; then STASHED="$STASHED $rel"; fi
      ;;
  esac
done <<< "$(find "$CANON/Phylo" -name '*.lean' -not -path '*/.lake/*' 2>/dev/null || true)"

restore_stash() {
  if [ -d "$STASHDIR" ]; then
    while IFS= read -r p; do
      [ -n "$p" ] || continue
      rel=${p#"$STASHDIR"/}
      if [ -f "$CANON/$rel" ]; then
        rm -f "$p"                                # agent 期间重建了 ⇒ 丢弃暂存副本，保留新的
      else
        mkdir -p "$(dirname "$CANON/$rel")" && mv "$p" "$CANON/$rel"
      fi
    done <<< "$(find "$STASHDIR" -name '*.lean' 2>/dev/null || true)"
    rm -rf "$STASHDIR"
  fi
}

NSTASH=$(echo $STASHED | wc -w)
if [ "$NSTASH" -gt 8 ]; then
  echo "✗ 需暂存文件数异常（$NSTASH > 5）：疑似模块名比对出错 ⇒ 立刻放回并**放弃暂存**"
  restore_stash
  STASHED=""
else
  trap restore_stash EXIT
  if [ -n "$STASHED" ]; then
    echo "ℹ️ 已暂存未登记的在建文件（验收后自动放回）：$STASHED"
  fi
fi

# ⑤/⑥ 两个既有脚本
bash "$CANON/scripts/check_file_imports.sh" || exit 1
bash "$CANON/scripts/list_star_claims.sh" | tail -3

# ⑦ git
cd "$CANON" || exit 1
echo '=== git status ==='
git status --short
echo '✓ guard 全绿'
