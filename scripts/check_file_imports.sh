#!/usr/bin/env bash
# 检查根模块 Phylo.lean 是否与 Phylo/ 下的 .lean 文件同步。
#
#   scripts/check_file_imports.sh
#
# 退出码：0 = 同步；1 = 有缺漏（列出未 import 的模块）。
set -u
cd "$(dirname "$0")/.." || exit 1

ROOT=Phylo.lean
[ -f "$ROOT" ] || { echo "缺少根模块 $ROOT"; exit 1; }

status=0
while IFS= read -r f; do
  mod="${f%.lean}"          # Phylo/Core.lean -> Phylo/Core
  mod="${mod//\//.}"        # Phylo/Core     -> Phylo.Core
  if ! grep -qx "import $mod" "$ROOT"; then
    echo "未 import：$mod"
    status=1
  fi
done < <(find Phylo -name '*.lean' | sort)

if [ "$status" -eq 0 ]; then
  echo "✓ 根模块与文件系统同步"
fi
exit "$status"
