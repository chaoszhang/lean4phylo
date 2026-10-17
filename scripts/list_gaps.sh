#!/bin/bash
# ============================================================================
#  list_gaps.sh —— 「开放缺口清单 + 状态 + 卡点」的自动产出（W21 任务 C5-2 / 派单 D3）
#
#  ★ 口径（**写死在此，不再漂移**）：
#    一条「缺口」= 名字里含 gap / Gap **且** 用 `def ... : Prop` 落盘的声明。
#    （本库的缺口一律登记为 `def X : Prop`，**不是** `theorem`：见
#      PerfectPhylogeny.lean §6 的说明「以下两条只是把目标陈述写清楚，
#      非 theorem，不引入任何公理」。）
#
#  ★ 三套口径**同时输出并标差异**（回应协调侧「机械扫 36 条 vs 逐条读 docstring 25 条」的漂移）：
#    口径 A（机械）：`grep -nE '^def +[A-Za-z0-9_]*([Gg]ap|Gap)[A-Za-z0-9_]*'` 直出的条数；
#    口径 B（收口判定）：在 A 的基础上分成三个桶 ——
#            [已收口] 库内已有同名 `…_holds` / `…_proof` 定理（`def` 按纪律**逐字保留**，
#                     故 `def` 仍在库，但真值已证）；
#            [追溯]   名字以 `_legacy` 结尾 —— 这是**已证伪的旧形态的追溯登记**
#                     （W22 任务 A 引入，如 `fourPointOfSplitMetricSum_gap_legacy`），
#                     **不是待证的缺口**，**不计入开放**（★ W22 新增规则）；
#            [开放]   其余。
#    口径 C（陈述形状）：带参数的 `def … (args) : Prop` 是**谓词**，不是闭命题 ——
#            对它写 `theorem NAME_holds : NAME` **不合法**（`NAME` 还不是 `Prop`），
#            收口必须写成 `theorem NAME_holds : ∀ args, NAME args` 或对具体 `args` 陈述。
#            ⇒ 这些条目的「已收口」判定口径与闭命题**不同**，本脚本单列出来提醒。
#            （★ 这条**不**表示它们不可证；`…_correct_shape`、`(T : Phylogram X)` 等都在此列。）
#
#  ★ 诚实声明：本脚本**只做机械扫描**，**不**判定忠实性（那要逐条读文献，机器判不了）；
#    也不判定「卡点」（那要读 docstring）。它给的是**清单与收口状态**，
#    作为「别再把 36/25 两个数各说一遍」的**共同底账**。
#
#  用法：  cd lean4phylo && bash scripts/list_gaps.sh
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

echo "=== 口径 A：机械扫「def 名含 gap/Gap」==="
mapfile -t DEFS < <(grep -rnE '^def +[A-Za-z0-9_]*(gap|Gap)[A-Za-z0-9_]*' Phylo/ | sort)
printf '%s\n' "${DEFS[@]}" | sed 's/^/  /'
echo "  口径 A 条数 = ${#DEFS[@]}"

echo
echo "=== 口径 B：三桶（已收口 / 追溯 / 开放）==="
# ⚠️ 必须在**全库** Phylo/ 内搜（收口定理常落在**另一个模块**，如
#    SBD.two_parent_trees_gap 由 TwoParent.two_parent_trees_gap_holds 收口）；
#    并允许**命名空间前缀**（`TwoParent.` / `Split.` 等）。
open=0
closed=0
trace=0
for line in "${DEFS[@]}"; do
  file="${line%%:*}"
  rest="${line#*:}"
  name="$(printf '%s' "$rest" | sed -E 's/^[0-9]+:def +([A-Za-z0-9_]+).*/\1/')"
  case "$name" in
    *_legacy)
      printf '  [追溯  ] %-52s %s\n' "$name" "$file"
      trace=$((trace+1))
      continue ;;
  esac
  hit="$(grep -rnE "^(theorem|lemma) +([A-Za-z0-9_]+\.)*${name}(_holds|_proof)? *[:({]" Phylo/ 2>/dev/null | head -1)"
  if [ -n "$hit" ]; then
    printf '  [已收口] %-52s %s\n' "$name" "$file"
    printf '           ↳ %s\n' "$hit"
    closed=$((closed+1))
  else
    printf '  [开放  ] %-52s %s\n' "$name" "$file"
    open=$((open+1))
  fi
done
echo "  口径 B：开放 = ${open} · 已收口 = ${closed} · 追溯 = ${trace} · 合计 = $((open+closed+trace))"

echo
echo "=== 口径 C：陈述形状（带参数 = 谓词，收口需 ∀ 形式） ==="
pred=0
prop=0
for line in "${DEFS[@]}"; do
  file="${line%%:*}"
  rest="${line#*:}"
  ln="${rest%%:*}"
  name="$(printf '%s' "$rest" | sed -E 's/^[0-9]+:def +([A-Za-z0-9_]+).*/\1/')"
  # 取声明签名（def 行起 3 行内，截到 `:=` 之前），再看 `: Prop` 之前是否已有参数绑定
  sig="$(sed -n "${ln},$((ln+2))p" "$file" | tr '\n' ' ')"
  head="${sig%%:=*}"
  pre="${head%%: Prop*}"
  if printf '%s' "$pre" | grep -qF -e '(' -e '{' -e '['; then
    printf '  [谓词式] %-52s %s:%s\n' "$name" "$file" "$ln"
    pred=$((pred+1))
  else
    prop=$((prop+1))
  fi
done
echo "  口径 C：闭命题 = ${prop} · 谓词式 = ${pred} · 合计 = $((prop+pred))"

echo
echo "=== ★ 与协调侧记录的口径差异（须逐条解释，不要再各说一遍）==="
echo "  · 本脚本只数「def 名含 gap」的登记项；协调侧的 36 条可能含 _gap_correct_shape/_gap_false 等"
echo "    派生名与「结论位」扫法；25 条可能只数了「尚未收口」的。"
echo "  · ⇒ 用本脚本的 A/B/C 三个数作为底账，差异逐条对；★ 忠实性判定与卡点仍以各 def 的 docstring 为准。"
