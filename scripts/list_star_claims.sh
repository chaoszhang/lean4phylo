#!/usr/bin/env bash
# scripts/list_star_claims.sh
#
# 用途：**纪律 12**（docstring 里每个带 ★ 的条目必须对应**真实存在**的声明）的机器辅助检查。
# 本项目历史上「文档里写了、代码里没有 / 写错了」已发生 8 次，且 **`lake build` 抓不到**
# （错误的 docstring 照样编译通过）。本脚本把「★ 行里引用的名字」与
# 「库内在**非 ★ 行**里出现过的名字」做差集，输出**需要人工确认**的名单。
#
# 判定口径（保守，宁少报不错报）：
#   一个名字只在 ★ 行里出现过、在**任何非 ★ 行**里都没出现过 ⇒ 可疑。
#   ⇒ 类型变量（`X`、`T`）、结构字段（`core`、`fourPoint`）、Mathlib 名（`IsPath`、`edgeSet`）、
#     假设名（`hcore`、`htri`）都会在非 ★ 行出现，因此**不会**进名单。
#   名单里的通常只剩：文献名（`Weller2023`）、文件名（`Njst.lean`）、以及**真正写错的声明名**。
#
# 用法：  bash scripts/list_star_claims.sh
# 退出码：0 = 名单为空；1 = 有需要人工确认的名字（**不是**硬失败）

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# 1) 非 ★ 行里出现过的所有标识符
grep -rv '★' Phylo --include='*.lean' \
  | grep -oE '[A-Za-z_][A-Za-z0-9_]*' | sort -u > "$tmp/words"

# 2) 含 ★ 的行里被反引号引用的名字（取末段名，便于跨命名空间匹配）
#    以 `_` 开头的 token 是「同族后缀简写」（形如 `` `foo_bar` / `_baz` ``），跳过。
grep -rn '★' Phylo --include='*.lean' \
  | grep -oE '`[^`]+`' | tr -d '`' \
  | grep -E '^[A-Za-z][A-Za-z0-9_.]*$' \
  | sed -E 's/.*\.//' | sort -u > "$tmp/claims"

# 3) 差集
missing=$(comm -23 "$tmp/claims" "$tmp/words")

echo "★ 行引用的名字 $(wc -l < "$tmp/claims") 个；非 ★ 行出现过的标识符 $(wc -l < "$tmp/words") 个。"
if [ -z "$missing" ]; then
  echo "✓ ★ 行引用的每个名字都在库内（非 ★ 行）出现过 —— 没有可疑的「只有文档里才有」的名字。"
  exit 0
fi
echo "⚠ 下列名字**只在 ★ 行里出现过**，库内别处找不到（逐条人工确认；文献名/文件名属正常，"
echo "   但若是「本文件声称已证的声明名」就说明 docstring 写错了）："
echo "$missing" | sed 's/^/  /'
exit 1
