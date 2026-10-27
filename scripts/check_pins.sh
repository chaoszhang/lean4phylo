#!/bin/bash
# ============================================================================
#  check_pins.sh —— 依赖版本锁一致性门（W40 · 外部审计 audit-1 的「A+D」方案）
#
#  ★ 为什么需要它：可复现性有三个源头，缺一个就漂：
#      ① `lean-toolchain`        —— Lean 编译器版本
#      ② `lakefile.toml` 的 rev  —— 我们**声明**要哪个 mathlib
#      ③ `lake-manifest.json`    —— lake **实际**解析到的 commit
#    ①②③ 只要有一个不一致，别人 clone 下来就可能拿到不同的库。
#    最常见的漂法：有人跑了 `lake update`、或改了 lakefile 却忘了把 manifest 一起提交。
#
#  ★ 判据（三选一，全部硬性）：
#    · `lean-toolchain` 必须有内容，且**不许是浮动 ref**（`stable` / `latest` / 空）；
#    · lakefile 的 mathlib `rev` **不许是 `master` / `main` / `stable`** 这类浮动 ref；
#    · 若 lakefile 的 rev 是 40 位 commit hash ⇒ 必须**逐字等于** manifest 里 mathlib 的 `rev`。
#      （若用 tag，则只打印提示：tag 的解析值由 manifest 记录，两者无法离线互推。）
#
#  用法：  bash scripts/check_pins.sh          # 核（不一致 ⇒ EXIT 1）
#  前置：  无（纯静态解析，不需要 `lake`，Windows 下也能跑）
# ============================================================================
set -u

cd "$(dirname "$0")/.." || exit 2

TOOLCHAIN_F=lean-toolchain
LAKEFILE=lakefile.toml
MANIFEST=lake-manifest.json

bad=0
say() { printf '%s\n' "$*"; }

say "== 依赖版本锁一致性 =="

# ── ① lean-toolchain ────────────────────────────────────────────────────────
tc=""
if [ -f "$TOOLCHAIN_F" ]; then
  tc="$(tr -d ' \t\r\n' < "$TOOLCHAIN_F")"
fi
if [ -z "$tc" ]; then
  say "  ✗ $TOOLCHAIN_F 缺失或为空 ⇒ 编译器版本没有锁"
  bad=$((bad+1))
else
  case "$tc" in
    *:stable|*:latest|leanprover/lean4:stable)
      say "  ✗ $TOOLCHAIN_F = $tc（浮动 ref）⇒ 请钉到具体版本，如 leanprover/lean4:v4.35.0-rc3"
      bad=$((bad+1)) ;;
    *)
      say "  ✓ $TOOLCHAIN_F = $tc" ;;
  esac
fi

# ── ②③ 解析 lakefile 的 rev 与 manifest 的实际 rev ─────────────────────────
if ! command -v python3 >/dev/null 2>&1; then
  say "  ⚠ 无 python3 ⇒ 跳过 ②③（① 已查）"
  say ""
  [ "$bad" -eq 0 ] && { say "VERDICT: ✓（部分检查）"; exit 0; } || { say "VERDICT: ✗ 有 ${bad} 项不达标"; exit 1; }
fi

python3 - "$LAKEFILE" "$MANIFEST" <<'PY'
import json, re, sys

lakefile, manifest = sys.argv[1], sys.argv[2]
bad = 0
say = print

# lakefile 里 mathlib 段的 rev
rev = None
try:
    txt = open(lakefile, encoding='utf-8').read()
    # 找 [[require]] 段里 name = "mathlib" 的那块
    for blk in re.split(r'\[\[require\]\]', txt)[1:]:
        if re.search(r'name\s*=\s*"mathlib"', blk):
            m = re.search(r'rev\s*=\s*"([^"]*)"', blk)
            if m:
                rev = m.group(1)
            break
except FileNotFoundError:
    say("  ✗ %s 不存在" % lakefile)
    sys.exit(1)

if rev is None:
    say("  ✗ %s 里找不到 mathlib 的 `rev = \"…\"`" % lakefile)
    bad += 1
    rev = ""

FLOAT = {"master", "main", "stable", "latest", "nightly"}
if rev in FLOAT:
    say("  ✗ %s：mathlib rev = \"%s\"（浮动 ref）⇒ 换成一个具体 commit" % (lakefile, rev))
    bad += 1

# manifest 里 mathlib 的实际 rev
mrev = None
try:
    d = json.load(open(manifest, encoding='utf-8'))
    for p in d.get("packages", []):
        if p.get("name") == "mathlib":
            mrev = p.get("rev")
            minput = p.get("inputRev")
            break
except FileNotFoundError:
    say("  ✗ %s 不存在" % manifest)
    bad += 1

if mrev is None:
    say("  ✗ %s 里没有 mathlib 条目（或没有 rev）" % manifest)
    bad += 1
else:
    if not re.fullmatch(r'[0-9a-f]{40}', mrev or ''):
        say("  ✗ %s 里 mathlib rev 不是 40 位 commit：%r" % (manifest, mrev))
        bad += 1

if rev and mrev and bad == 0:
    if re.fullmatch(r'[0-9a-f]{40}', rev):
        if rev == mrev:
            say("  ✓ lakefile rev = manifest rev = %s" % rev[:12])
        else:
            say("  ✗ 不一致：lakefile = %s…，manifest = %s…" % (rev[:12], mrev[:12]))
            say("      ⇒ 改了 rev 就要跑 `lake update` 并把新 manifest **一起提交**")
            bad += 1
    else:
        say("  ⚠ lakefile rev = \"%s\"（非 commit）⇒ 无法离线与 manifest 互推；" % rev)
        say("      manifest 记录的实际 commit = %s…，请人工确认它是该 ref 的解析值" % mrev[:12])

say("")
if bad:
    say("VERDICT: ✗ 有 %d 项不达标" % bad)
    sys.exit(1)
say("VERDICT: ✓ 依赖版本锁一致")
PY
ec=$?
# python 段自己会打 VERDICT；非零就直接传上去，别重复打一遍
[ "$ec" -ne 0 ] && exit 1

if [ "$bad" -ne 0 ]; then
  say ""
  say "VERDICT: ✗ 有 ${bad} 项不达标"
  exit 1
fi
exit 0
