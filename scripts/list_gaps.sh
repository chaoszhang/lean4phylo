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
#    口径 B（收口判定）：在 A 的基础上分成**四个**桶 ——
#            [已收口] 库内已有同名 `…_holds` / `…_proof` 定理（`def` 按纪律**逐字保留**，
#                     故 `def` 仍在库，但真值已证）；
#            [追溯]   名字以 `_legacy` 结尾 —— 这是**已证伪的旧形态的追溯登记**
#                     （W22 任务 A 引入，如 `fourPointOfSplitMetricSum_gap_legacy`），
#                     **不是待证的缺口**，**不计入开放**（★ W22 新增规则）；
#            [判定收档] 名字在**白名单**里 —— 经老师逐条认可「判定完成 / 任务完成」的梓位
#                     （**没有可证内容**：谓词式 ∨ 已判不忠实），**不计入开放**（★ W24 新增）；
#            [开放]   其余。
#    ★ W24：同一 gap 若同时有 `_holds` 与 `_proof`，**优先指 `_holds`**
#      （`_proof` 常带未证假设 = 条件收口）。
#    ⚠️ **口径 B 的已知局限（W22 发现，尚未修，判据待老师定）**：
#       「[已收口]」只检查**有没有同名** `…_holds`/`…_proof`，**不检查它是否带假设** ⇒
#       **条件收口会被误记成已收口**。
#       ★ W24 更新：**原先的唯一实例已消失** ✓ —— W23 证了 (★′)
#       `Split.noWRealizer_exists_gap_proof`，并新增了**无条件**收口
#       `notIsDSplit_of_splitMetricSum_gap_holds`；本脚本现优先指 `_holds` ⇒ 该行已指向无条件版 ✓。
#       ⇒ 读「已收口 = N」时**仍应**回看该行 `↳` 指向的定理是否吃假设。
#       修法不能只看「有没有括号参数」（隐式/实例参数也是括号）⇒ 判据需老师定。
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
echo "=== 口径 B：四桶（已收口 / 追溯 / 判定收档 / 开放）==="
# ===== 判定收档白名单（W24 新增；老师 2026-10-17 认可「任务完成」）=====
# 加入条件（**三条全须满足**）：
#   (a) **没有可证内容**—— 谓词式（带参数，→ 本脚本口径 C 会列出）或已被判**不忠实**；
#   (b) 库内已有**反空真见证**（否则连登记的意义都没有）；
#   (c) **老师明文认可**「判定完成 / 任务完成」（不是 dsh 自己说了算）。
# 现值（逐条留证）：
#   rStarConsensus_gap（ConsensusGreedy.lean）
#     (a) 谓词式（`R : (ι → Cladogram X) → Finset (Split X)`；口径 C 已确认）＋ W19 判**不忠实**；
#     (b) `rStarConsensus_gap_strictSplits`（严格共识满足全部四条）；
#     (c) W24 派单：「**A-10 任务完成，代码归档**」。
# ★ 「归档」的形式：`def` 本体**一字不改**（留在原处），只在台账里改归桶；理由见 HANDOVER W24 块 ——
#   脚本判定是**按名全库 grep**，因此「把代码挪到另一个文件/另一节」**不可能**改变它的结论。
ARCHIVED_JUDGED="rStarConsensus_gap"
# ⚠️ 必须在**全库** Phylo/ 内搜（收口定理常落在**另一个模块**，如
#    SBD.two_parent_trees_gap 由 TwoParent.two_parent_trees_gap_holds 收口）；
#    并允许**命名空间前缀**（`TwoParent.` / `Split.` 等）。
open=0
closed=0
trace=0
judged=0
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
  if printf '%s\n' $ARCHIVED_JUDGED | grep -qxF "$name"; then
    printf '  [判定收档] %-50s %s\n' "$name" "$file"
    judged=$((judged+1))
    continue
  fi
  # ★ 同名 _holds 优先于 _proof（_proof 常带未证假设 = 条件收口）
  hit="$(grep -rnE "^(theorem|lemma) +([A-Za-z0-9_]+\.)*${name}_holds *[:({]" Phylo/ 2>/dev/null | head -1)"
  if [ -z "$hit" ]; then
    hit="$(grep -rnE "^(theorem|lemma) +([A-Za-z0-9_]+\.)*${name}(_proof)? *[:({]" Phylo/ 2>/dev/null | head -1)"
  fi
  if [ -n "$hit" ]; then
    printf '  [已收口] %-52s %s\n' "$name" "$file"
    printf '           ↳ %s\n' "$hit"
    closed=$((closed+1))
  else
    printf '  [开放  ] %-52s %s\n' "$name" "$file"
    open=$((open+1))
  fi
done
echo "  口径 B：开放 = ${open} · 已收口 = ${closed} · 追溯 = ${trace} · 判定收档 = ${judged} · 合计 = $((open+closed+trace+judged))"
echo "  ⚠️ 口径 B 已知局限：「已收口」不检查收口定理是否带假设 ⇒ 条件收口会被误记（见脚本头）"
echo "     ★ W24：同名 _holds 已优先；原实例 notIsDSplit_of_splitMetricSum_gap 现指向无条件的 _holds ✓"
echo "     ★ 判定收档白名单 = ${ARCHIVED_JUDGED}（加入条件见脚本头；不计入开放）"

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
