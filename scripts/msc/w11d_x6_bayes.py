#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W11d / X6 —— 贝叶斯 MSC 的**精确有理数**对账脚本（**无 Monte Carlo**）。

伴随 `Phylo/Stat/MSCBayes.lean`（Lean 4，零 sorry/axiom/native_decide）。

## 文献

* Heled & Drummond (2010), *Bayesian Inference of Species Trees from Multilocus Data*,
  *Mol. Biol. Evol.* **27**(3):570–580 —— `references/md/HeledDrummond2010_...md`
  **496–510** 行 Eq. (1)：``P(S|D) ∝ ∫_G ∏ᵢ P(dᵢ|gᵢ) P(gᵢ|S) P(S) dG``
  （后验 ∝ 先验 × 似然，基因树被边缘化）；**615–637** 行：先验 `P(S) = fBD(S)·PN(S)`。
* Rannala & Yang (2003), *Genetics* **164**:1645–1656 ——
  **355–370** 行 (4)(5) 式：``f(Θ,G|D) ∝ f(D|G) f(G|Θ) f(Θ)``、``f(Θ|D) = ∫ f(Θ,G|D) dG``。

## 精确性口径（为什么可以「无 Monte Carlo」还精确）

4 叶 MSC 的全部概率都是 `x = e^{−t}` 的**有理函数**：

    P(一致拓扑)  = 1 − (2/3)·x        （`MSCProof.mscConcordant`，`pConcordant_eq`）
    P(不一致拓扑) = (1/3)·x            （`MSCProof.mscDiscordant`，`pDiscordant`）

故只要把 `x = e^{−t} ∈ (0, 1]` 取成**有理数**，一切计算都在 `fractions.Fraction` 里
**精确**完成，不引入任何浮点误差、也不抽样。（另附 `math.exp` 的浮点旁证，仅作对照。）

运行：`python3 scripts/msc/w11d_x6_bayes.py`
"""

from fractions import Fraction as F
import math
import sys

FAIL = []


def check(name, cond, extra=""):
    tag = "PASS" if cond else "FAIL"
    print(f"[{tag}] {name}{('  ' + extra) if extra else ''}")
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------
# §1 有限树空间上的贝叶斯后验：`evidence = Σ ρᵢLᵢ`、`posterior i = ρᵢLᵢ/Z`
# --------------------------------------------------------------------------
def evidence(prior, lik):
    return sum(p * l for p, l in zip(prior, lik))


def posterior(prior, lik):
    Z = evidence(prior, lik)
    return [p * l / Z if Z != 0 else F(0) for p, l in zip(prior, lik)]


print("=" * 72)
print("§1 有限树空间上的贝叶斯后验（精确有理数）")
print("=" * 72)

# 若干精确实例：先验归一、似然非负
cases = [
    ("均匀 2 树", [F(1, 2), F(1, 2)], [F(3, 4), F(1, 4)]),
    ("偏斜 3 树", [F(1, 2), F(1, 3), F(1, 6)], [F(1, 5), F(9, 10), F(2, 3)]),
    ("含零似然 4 树", [F(1, 4)] * 4, [F(1, 2), F(0), F(7, 8), F(1, 3)]),
]
for name, prior, lik in cases:
    assert sum(prior) == 1, "先验必须归一到 1"
    assert all(l >= 0 for l in lik)
    post = posterior(prior, lik)
    check(f"{name}：后验归一到 1", sum(post) == 1, f"Σposterior={sum(post)}")
    Z = evidence(prior, lik)
    check(
        f"{name}：后验 ∝ 先验×似然（交叉相乘）",
        all(post[i] * (prior[j] * lik[j]) == post[j] * (prior[i] * lik[i])
            for i in range(len(prior)) for j in range(len(prior))),
    )
    check(
        f"{name}：支撑(后验) = 支撑(先验) ∩ 支撑(似然)",
        all((post[i] > 0) == (prior[i] > 0 and lik[i] > 0) for i in range(len(prior))),
        f"Z={Z}",
    )

# --------------------------------------------------------------------------
# §2 ★B 反例一：后验支撑可以严格小于先验支撑
# --------------------------------------------------------------------------
print()
print("=" * 72)
print("§2 ★B 反例一：后验的支撑严格小于先验的支撑")
print("=" * 72)
prior = [F(1, 2), F(1, 2)]
lik = [F(1), F(0)]
post = posterior(prior, lik)
check("★B 先验在两个候选树上都严格正", all(p > 0 for p in prior))
check("★B 后验把第 2 棵树抹成 0", post[1] == 0, f"posterior={post}")
check("★B 第 1 棵树拿到全部后验质量", post[0] == 1, f"posterior[0]={post[0]}")
check("★B 支撑严格收缩（先验支撑 ≠ 后验支撑）",
      {i for i, p in enumerate(prior) if p > 0} != {i for i, p in enumerate(post) if p > 0})
print("    ⇒ 回答「后验一定与先验有相同支撑吗？」：**不一定**；")
print("      准确关系是 支撑(后验) = 支撑(先验) ∩ 支撑(似然)。")

# --------------------------------------------------------------------------
# §3 ★B 反例二：似然恒为零 ⇒ Z = 0 ⇒ 「后验」不是概率分布
# --------------------------------------------------------------------------
print()
print("=" * 72)
print("§3 ★B 反例二：似然恒为 0 时后验无定义（Z = 0）")
print("=" * 72)
prior = [F(1, 2), F(1, 2)]
lik = [F(0), F(0)]
Z = evidence(prior, lik)
post = posterior(prior, lik)
check("★B 证据 Z = 0", Z == 0)
check("★B 按 `_ / 0 = 0` 约定，Σ「后验」= 0 ≠ 1", sum(post) == 0 and sum(post) != 1,
      f"Σposterior={sum(post)}")
print("    ⇒ Lean 侧 `posterior_sum_one` 的假设 `Z ≠ 0` 是**必需的**；")
print("      但在 MSC 模型里 `e^{−a}e^{−b} > 0` 处处成立 ⇒ Z > 0 **恒成立**")
print("      （Lean: `kingmanMSCMeasure_deep_pos`），该病态不会发生。")

# --------------------------------------------------------------------------
# §4 ★C 端到端最小例：4 taxon、2 棵候选树
#     x = e^{−t} ∈ (0,1]；似然 = (1 − 2x/3, x/3)（第 2 棵树上观测到不一致拓扑）
# --------------------------------------------------------------------------
print()
print("=" * 72)
print("§4 ★C 端到端最小例：4 taxon、2 棵候选树、先验 (1/2, 1/2)")
print("=" * 72)
prior = [F(1, 2), F(1, 2)]
print(f"{'x = e^-t':>10} {'lik1':>10} {'lik2':>10} {'post1':>12} {'post2':>12} "
      f"{'Σpost':>6} {'post1>1/2':>10}")
for x in [F(1), F(9, 10), F(2, 3), F(1, 2), F(1, 3), F(1, 10)]:
    lik = [1 - F(2, 3) * x, F(1, 3) * x]
    post = posterior(prior, lik)
    check(f"x={x}：后验归一到 1", sum(post) == 1)
    check(f"x={x}：x<1 ⇒ 后验严格偏向一致树",
          (post[0] > F(1, 2)) == (x < 1))
    print(f"{str(x):>10} {str(lik[0]):>10} {str(lik[1]):>10} {str(post[0]):>12} "
          f"{str(post[1]):>12} {str(sum(post)):>6} {str(post[0] > F(1, 2)):>10}")

# 闭式核对：post1 = (1 − 2x/3) / (1 − x/3) = 1 − (x/3)/(1 − x/3)
for x in [F(1, 2), F(3, 7), F(5, 8)]:
    lik = [1 - F(2, 3) * x, F(1, 3) * x]
    post = posterior(prior, lik)
    closed = (1 - F(2, 3) * x) / (1 - F(1, 3) * x)
    check(f"x={x}：后验闭式 = (1−2x/3)/(1−x/3)", post[0] == closed,
          f"{post[0]} vs {closed}")

# 浮点旁证：x = exp(-t) 与有理数代理一致（仅对照，不参与判定）
print()
print("浮点旁证（不参与判定）：t ↔ x = exp(-t) 的单调对应")
for t in [0.0, 0.5, 1.0, 2.0]:
    xf = math.exp(-t)
    p1f = (1 - 2 * xf / 3) / (1 - xf / 3)
    print(f"    t={t:<4} x=exp(-t)={xf:.6f}  post1={p1f:.6f}  (>1/2: {p1f > 0.5})")
check("浮点旁证：t=0 ⇒ x=1 ⇒ post1=1/2（恰好不偏）",
      abs((1 - 2 * math.exp(0) / 3) / (1 - math.exp(0) / 3) - 0.5) < 1e-12)

# --------------------------------------------------------------------------
# §5 两棵树先验的加权和 (c, 1−c)：仍归一到 1；并与测度层边缘似然对接
# --------------------------------------------------------------------------
print()
print("=" * 72)
print("§5 两棵树先验的加权和 (c, 1−c)：归一 ＋ 与测度层 Z 对接")
print("=" * 72)
for c, x1, x2 in [(F(1, 2), F(1, 2), F(1, 4)),
                  (F(1, 4), F(1, 3), F(1, 2)),
                  (F(3, 5), F(1, 10), F(9, 10))]:
    prior = [c, 1 - c]
    lik = [x1, x2]
    post = posterior(prior, lik)
    Z = evidence(prior, lik)
    check(f"c={c}, x=({x1},{x2})：加权和先验 Σprior=1", sum(prior) == 1)
    check(f"c={c}, x=({x1},{x2})：后验归一到 1", sum(post) == 1)
    # 测度层：ρ = c·δ(u1) + (1−c)·δ(u2) ⇒ ν(deep) = ∫ e^{−a}e^{−b} dρ = c·x1 + (1−c)·x2
    check(f"c={c}：ν(deep) = c·x1 + (1−c)·x2（测度层加性）",
          Z == c * x1 + (1 - c) * x2, f"Z={Z}")
    # 后验权重 = c·x1 / Z
    check(f"c={c}：posterior1 = c·x1/Z", post[0] == c * x1 / Z,
          f"{post[0]} vs {c * x1 / Z}")

# --------------------------------------------------------------------------
# §6 Lean 侧同名条目的行号速查（供复核者按图索骥）
# --------------------------------------------------------------------------
print()
print("=" * 72)
print("§6 与 Lean 文件的对应（Phylo/Stat/MSCBayes.lean）")
print("=" * 72)
for line in [
    "FiniteBayesModel.evidence / posterior            —— §1（本脚本 §1）",
    "FiniteBayesModel.posterior_mul_eq                —— 「后验 ∝ 先验×似然」无除法形式",
    "FiniteBayesModel.posterior_sum_one               —— 归一到 1（需 Z ≠ 0）",
    "FiniteBayesModel.posterior_pos_iff               —— 支撑 = 先验支撑 ∩ 似然支撑",
    "FiniteBayesModel.posterior_support_lt_prior_support —— ★B 反例一（本脚本 §2）",
    "FiniteBayesModel.zeroLikModel_posterior_not_prob —— ★B 反例二（本脚本 §3）",
    "kingmanMSCMeasure_deep_pos                       —— MSC 里 Z > 0 恒成立（本脚本 §3 尾）",
    "twoTreeMSCModel_posterior_favors_concordant      —— ★C（本脚本 §4）",
    "kingmanMSCMeasure_dirac_add_deep                 —— 加权和（本脚本 §5）",
    "ContinuousPriorPosteriorConsistencyGap           —— §5 显式缺口（未证，超范围）",
    "MultiLocusPosteriorConcentrationGap              —— §5 显式缺口（未证，超范围）",
]:
    print("    " + line)

print()
print("=" * 72)
if FAIL:
    print(f"结果：**{len(FAIL)} 项 FAIL** -> {FAIL}")
    sys.exit(1)
print("结果：**全部 PASS**（精确有理数，无 Monte Carlo，无浮点判定）")
sys.exit(0)
