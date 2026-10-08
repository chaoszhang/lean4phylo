#!/usr/bin/env bash
# scripts/msc/run_all.sh —— 一键跑本目录**全部**数值复核脚本，汇总 VERDICT
#
# 用法：  bash scripts/msc/run_all.sh
# 退出码：0 = 全部脚本 exit 0 且自报 PASS/PASS 类结论；1 = 有脚本失败或不自报通过
set -u
cd "$(dirname "$0")" || exit 1
FAIL=0
TMP=$(mktemp)
for f in kingman_check.py kingman_jumpchain.py msc_quartet_prob.py coalescent_stats.py \
         adr2011_identifiability.py adr2017_split.py degnansalter_puv.py zds2011_monophyly.py; do
  [ -f "$f" ] || { echo "— 跳过 $f（不存在）"; continue; }
  echo "===== $f"
  if timeout 900 python3 "$f" > "$TMP" 2>&1; then
    if grep -qE 'VERDICT: *PASS|=> *PASS|ALL OK|ALL PASS|全部通过' "$TMP"; then
      grep -E 'VERDICT|=> *PASS|ALL OK|ALL PASS|全部通过' "$TMP" | tail -2 | sed 's/^/    /'
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
if [ "$FAIL" -eq 0 ]; then echo "✓ 全部复核脚本 PASS"; else echo "✗ 有脚本未通过"; fi
exit "$FAIL"
