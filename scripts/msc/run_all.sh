#!/usr/bin/env bash
# scripts/msc/run_all.sh —— 一键跑本目录**全部**数值复核脚本，汇总 VERDICT
#
# 用法：  bash scripts/msc/run_all.sh
# 退出码：0 = 全部脚本 exit 0 且自报 PASS/PASS 类结论；1 = 有脚本失败或不自报通过
#
# ⚠️ 本脚本**动态扫描** `*.py`（不再硬编码清单）——
# 之前硬编码时漏掉了后来新增的 4 个脚本（`kingman_coalescent` / `empirical_convergence` /
# `stadler_degnan_ranked` / `trivial_split_count`），于是「全绿」是**假绿**。
set -u
cd "$(dirname "$0")" || exit 1
FAIL=0
N=0
TMP=$(mktemp)
for f in *.py; do
  [ -f "$f" ] || continue
  N=$((N + 1))
  echo "===== $f"
  if timeout 900 python3 "$f" > "$TMP" 2>&1; then
    if grep -qE 'PASS|通过|OK' "$TMP"; then
      grep -E 'PASS|通过|OK' "$TMP" | tail -2 | sed 's/^/    /'
    else
      echo "    ✗ 脚本退出 0 但**没有**自报 PASS —— 最后 5 行："
      tail -5 "$TMP" | sed 's/^/      /'
      FAIL=1
    fi
  else
    echo "    ✗ 脚本非零退出 —— 最后 8 行："
    tail -8 "$TMP" | sed 's/^/      /'
    FAIL=1
  fi
done
rm -f "$TMP"
echo
if [ "$FAIL" -eq 0 ]; then echo "✓ 全部复核脚本 PASS（共 $N 个）"; else echo "✗ 有脚本未通过"; fi
exit "$FAIL"
