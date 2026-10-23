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
#  ★ 三套口径**同时输出并标差异**：
#    口径 A（机械）：`grep` 直出的条数（= 67 行；★ **66 个不同名**，见下）。
#    口径 B（收口判定）：**七桶** —— 由 `scripts/gap_ledger.py` 产出（W25-B 重写；2026-10-23 加第七桶）：
#            [已证伪]   库内已有形式化反例（`not_N` / `N_refuted` / `N_false*` / `N_not_universal`）；
#            [已收口]   有**无条件、无特化**的收口定理（`_holds`/`_proved`/`_true`/`_of_isBinary`/`_proof`）；
#            [条件收口] 收口定理**多吃显式假设**，或只证明了 `def` 参数的一个**特化**；
#            [追溯]     名字以 `_legacy` 结尾（已证伪旧形态的追溯登记，W22 起，不计入开放）；
#            [判定收档] 老师明文认可「任务完成」的白名单（**无可证内容**，W24 起，不计入开放）；
#            [长期开放] 老师裁定「**Conjecture 不证**」的白名单（**有可证内容但不证**，2026-10-23 起，
#                       与「判定收档」的区别就在这一句；不计入开放）；
#            [真开放]   其余（= **我们要证的**）。
#            ★ 判据细节（后缀顺序、假设判据 = 与 `def` 自身绑定比对、特化判据、
#              12 条已证伪的**形态**表）全部写在 `scripts/gap_ledger.py` 文件头，
#              **以那里为准**；本脚本只调用它。
#            ⚠️ 旧版（W24）的四桶判据已被 W25-B 取代：旧版只认 `_holds`/`_proof`
#              ⇒ 把 **10 条 `_proved` 收口**误记成「开放」，且没有「已证伪」桶
#              ⇒ 旧版的「开放 = 50」**是台账错误**，不是真实状态。
#    口径 C（陈述形状）：带参数的 `def … (args) : Prop` 是**谓词**，不是闭命题 ——
#            对它写 `theorem NAME_holds : NAME` **不合法**（`NAME` 还不是 `Prop`），
#            收口必须写成 `theorem NAME_holds : ∀ args, NAME args` 或对具体 `args` 陈述。
#            ⇒ 这些条目的「已收口」判定口径与闭命题**不同**，本脚本单列出来提醒。
#            （★ 这条**不**表示它们不可证；`…_correct_shape`、`(T : Phylogram X)` 等都在此列。）
#
#  ★ 诚实声明：本脚本**只做机械扫描**，**不**判定忠实性（那要逐条读文献，机器判不了）；
#    也不判定「卡点」（那要读 docstring）。它给的是**清单与收口状态**，
#    作为「别再把 36/25/50 几个数各说一遍」的**共同底账**。
#
#  用法：  cd lean4phylo && bash scripts/list_gaps.sh
#         cd lean4phylo && python3 scripts/gap_ledger.py   # 只跑口径 B（带完整签名）
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

echo "=== 口径 A：机械扫「def 名含 gap/Gap」（★ 先剥 Lean 注释）==="
# ★ W28-D 修正：旧版是 `grep -rnE '^def …'`，会被**注释里**的 `def rankedTree_card_gap`
#   （`Phylo/Stat/CoalescentHistoryCount.lean` 的模块 docstring 代码围栏）骗到 ⇒ A 报 71 行，
#   而真实登记只有 70 个名字。改用与 gap_ledger.py 同一套 `strip_lean_comments()`，A 与 B 从此一致。
mapfile -t DEFS < <(python3 - <<'PYSCAN'
import io, os, re, sys
sys.path.insert(0, os.path.join(os.getcwd(), "scripts"))
from gap_ledger import strip_lean_comments
DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*def\s+([A-Za-z0-9_'.’]+)")
out = []
for root, _, fs in os.walk("Phylo"):
    for f in sorted(fs):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        raw = io.open(p, encoding="utf-8").read().replace("\r\n", "\n")
        for i, ln in enumerate(strip_lean_comments(raw).split("\n"), 1):
            m = DECL.match(ln)
            if m and re.search(r"(gap|Gap)", m.group(1)):
                out.append("%s:%d:%s" % (p.replace(os.sep, "/"), i, ln.strip()))
for l in sorted(out):
    print(l)
PYSCAN
)
printf '%s\n' "${DEFS[@]}" | sed 's/^/  /'
echo "  口径 A 条数 = ${#DEFS[@]}（**剥注释后**的行数；应与口径 B 的合计行相等）"
DUP="$(printf '%s\n' "${DEFS[@]}" | sed -E 's/.*:[0-9]+:def +([A-Za-z0-9_]+).*/\1/' | sort | uniq -d | tr '\n' ' ')"
if [ -n "${DUP// /}" ]; then
  echo "  ⚠️ 同名定义两次（行数 > 名字数）：**${DUP}** —— 真·同名同体落在两个文件；★ **不去重**（去重会破坏与历史数字的对账）。"
else
  echo "  ✓ 无同名重复（★ W28-D 修正：旧提示里的 rankedTree_card_gap「同名两次」其实是**注释里的幽灵**，已随剥注释消失）"
fi

echo
if ! command -v python3 >/dev/null 2>&1; then
  echo "  ✗ 需要 python3 才能跑口径 B（scripts/gap_ledger.py）" >&2
  exit 1
fi
python3 scripts/gap_ledger.py || exit 1

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
echo "=== ★ 三个口径之间的关系（读数字前先读这段）==="
echo "  · 口径 A = 登记条数（行）；口径 B = 这些登记项的**真实状态**（**七桶**加总必须 = A 的不同名数）；"
echo "  · 口径 C = 陈述形状，与 B 正交（谓词式也可以「已收口」——只要有 ∀ 形式的收口定理）。"
echo "  · ★ 括号中的「收口定理完整签名」由 gap_ledger.py 逐条打印，供人工核「有没有吃假设」。"
