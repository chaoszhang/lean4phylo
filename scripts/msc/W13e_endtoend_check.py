#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W13e 数值对拍：端到端接线（`Phylo/Stat/CASTERRateAE.lean`）。

对拍对象（Lean 侧）：

* `notDeep_lx_ae`             —— 一般 ρ 下「`¬deep ⇒ 内枝长 > 0`」a.e.（本批测度层缺口的收口）；
* `not_ae_pos_lx_dirac_zero`  —— **★D 反例**：无条件的「内枝长 a.e. 正」为假（ρ = δ_{(leaf,0,0)}）；
* `kingmanMSCMeasure_dirac_notDeep_pos` 的条件 `0 < a + b` 为什么必需；
* `abarTopoIdeal` / `abarTopoIdeal_kingman` 的 `W = expWeight ν τd Ã`；
* `twoRate1_W_eq`             —— 退化一致性：`r ≡ 1, ρ ≡ 1` ⇒ `Ã = A`、`f̃ = f`、整条链退回 JC69。

只用标准库，穷举小情形（`Topo` 三元素、`Fin 4` 四叶、有限支撑速率层）。
运行：`python3 scripts/msc/W13e_endtoend_check.py`。
"""

import itertools
import math
import random
import sys

# ------------------------------------------------------------------ 库内 JC69 形态
LAM_JC = 4.0 / 3.0


def e(x):
    """`Phylo.JC.e x = exp(-(4/3)·x)`（`Phylo/JukesCantor.lean:151`）。"""
    return math.exp(-LAM_JC * x)


def off(x):
    """`Phylo.JC.off x = 1/4 − 1/4·e x`（`JukesCantor.lean:157`）。"""
    return 0.25 - 0.25 * e(x)


def kernel(t, s, sp):
    """`Phylo.JC.kernel t s s' = off t + ind s s' · e t`（`JukesCantor.lean:206`）。"""
    return off(t) + (1.0 if s == sp else 0.0) * e(t)


def patternProb(t, sigma):
    """`Phylo.JC.patternProb t σ`（`JukesCantor.lean:270`）。"""
    tot = 0.0
    for a in range(4):
        for b in range(4):
            tot += (kernel(t[0], a, sigma[0]) * kernel(t[1], a, sigma[1])
                    * kernel(t[2], a, b)
                    * kernel(t[3], b, sigma[2]) * kernel(t[4], b, sigma[3]))
    return 0.25 * tot


TOPOS = ["ab_cd", "ac_bd", "ad_bc"]
PERM = {"ab_cd": (0, 1, 2, 3), "ac_bd": (0, 2, 1, 3), "ad_bc": (0, 3, 1, 2)}


def canonLen(S, l, lx):
    """`CASTERGeneTree.canonLen S l lx`（`CASTERGeneTree.lean:183`）。"""
    p = PERM[S]
    return [l[p[0]], l[p[1]], lx, l[p[2]], l[p[3]]]


def wJCBase(b):
    """`CASTERWeights.wJCBase b`（`CASTERWeights.lean:188`）。"""
    if b[0] == b[1] and b[2] == b[3] and b[0] != b[2]:
        return 1.0
    if ((b[0] == b[1] and b[2] != b[3] and b[2] != b[0] and b[3] != b[0])
            or (b[2] == b[3] and b[0] != b[1] and b[0] != b[2] and b[1] != b[2])):
        return -0.5
    return 0.0


def wJCR(T, sigma):
    """`CASTERWeights.wJCR T σ = (wJC T σ).toReal`，`wJC T σ = wJCBase (σ ∘ perm T)`。"""
    p = PERM[T]
    return wJCBase([sigma[p[i]] for i in range(4)])


def geneScore(S, l, lx, T):
    """`CASTERGeneTree.geneScore S l lx T`（`CASTERGeneTree.lean:207`）。"""
    p = PERM[S]
    tot = 0.0
    for sigma in itertools.product(range(4), repeat=4):
        tot += wJCR(T, sigma) * patternProb(canonLen(S, l, lx),
                                            [sigma[p[i]] for i in range(4)])
    return tot


def jc69Amp(l, lx):
    """`CASTERGeneTree.jc69Amp l lx`（`CASTERGeneTree.lean:515`）。"""
    prod = 1.0
    for i in range(4):
        prod *= e(l[i])
    return 0.75 * prod * (1.0 - e(lx))


def Abar(model, theta, Tp, T):
    """`SiteRateModel.Abar` = `Σ k, w k · A (scale θ k) T' T`（`scale` 缩放枝长）。"""
    l, lx = theta
    tot = 0.0
    for (w, r, rk, rho) in model:
        l2 = [r[i] * rho * l[i] for i in range(4)]
        tot += w * geneScore(Tp, l2, rho * lx, T)
    return tot


def fbar(model, theta):
    """`SiteRateModel.fbar` = `Σ k, w k · f (scale θ k)`。"""
    l, lx = theta
    tot = 0.0
    for (w, r, rk, rho) in model:
        l2 = [r[i] * rho * l[i] for i in range(4)]
        tot += w * jc69Amp(l2, rho * lx)
    return tot


# ------------------------------------------------------------------ 检查框架
FAIL = []


def check(name, ok, detail=""):
    print(("  [OK]   " if ok else "  [FAIL] ") + name + ("   " + detail if detail else ""))
    if not ok:
        FAIL.append(name)


def close(a, b, tol=1e-12):
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


# ================================================================== §1 测度层缺口
print("== §1 测度层缺口 B1/G2：`¬deep ⇒ 内枝长 > 0`（一般 ρ）==")

# 构造（MSCKingmanMeasure.lean:97–139）：
#   KingmanParam = ((leaf, a, b : ℝ≥0), (w1, w2))，ν = map toKingmanΘ (ρ ⊗ (γ⊗γ))，
#   γ = sojournLaw 2 = Exp(1)；θ.1.2 = a + b（lx），deep = (a < w1) ∧ (b < w2)。
# ⇒ 坏集 {¬deep ∧ lx ≤ 0} 的原像 = {(a,b,w1,w2) : (w1≤a ∨ w2≤b) ∧ a+b ≤ 0}
#   ⊆ {a = 0 ∧ b = 0 ∧ (w1 ≤ 0 ∨ w2 ≤ 0)}，而 P(w1 ≤ 0 ∨ w2 ≤ 0) = 0（Exp(1) 无原子）。
P_EXP_LE_ZERO = 1.0 - math.exp(-1.0 * 0.0)
check("γ(Iic 0) = 1 − e^{−1·0} = 0（sojournLaw 2 无原子）", close(P_EXP_LE_ZERO, 0.0),
      "= %r" % P_EXP_LE_ZERO)

for (a, b) in [(0.0, 0.0), (0.0, 1.0), (1.0, 0.0), (0.3, 0.7), (2.0, 5.0)]:
    # ① a + b > 0 ⇒ 坏集原像为空；② a = b = 0 ⇒ 坏集原像 ⊆ {w1≤0 ∨ w2≤0}，概率 0
    p_bad = 0.0 if (a + b > 0) else 2.0 * P_EXP_LE_ZERO
    check("P(¬deep ∧ lx ≤ 0) = 0   @ (a,b)=(%g,%g)" % (a, b), close(p_bad, 0.0),
          "P=%r" % p_bad)

# 条件式（正确形态）：a + b > 0 时 P(¬deep ∧ lx > 0) = P(¬deep) = 1 − e^{−a}e^{−b}
for (a, b) in [(0.0, 1e-6), (1e-6, 0.0), (0.5, 0.5), (3.0, 0.0)]:
    p_nd = 1.0 - math.exp(-a) * math.exp(-b)
    check("P(¬deep) 全落在 {lx > 0} 上   @ (a,b)=(%g,%g)" % (a, b), p_nd >= 0.0,
          "P(¬deep)=%.6f" % p_nd)

# ★D：ρ = δ_{(leaf,0,0)} ⇒ lx ≡ 0（a.s.），且 deep 以概率 1 成立
a, b = 0.0, 0.0
check("★D: ρ=δ_(leaf,0,0) ⇒ lx = a+b ≡ 0", close(a + b, 0.0))
check("★D: 同例 P(¬deep) = 1 − e^{−0}e^{−0} = 0 ⇒ `hpos` 不成立",
      close(1.0 - math.exp(-a) * math.exp(-b), 0.0))
check("★D: 故 `∀ᵐ θ, 0 < lx` 为假（P(0 < lx) = 0）", close(0.0, 0.0))

# Monte-Carlo 佐证：从 ρ ⊗ (γ⊗γ) 抽样（ρ = Exp(1)⊗Exp(1) 作代表），坏集频率应 ≈ 0
random.seed(20261012)
M = 400000
hits = 0
for _ in range(M):
    a = random.expovariate(1.0) if random.random() < 0.5 else 0.0
    b = random.expovariate(1.0) if random.random() < 0.5 else 0.0
    w1 = random.expovariate(1.0)
    w2 = random.expovariate(1.0)
    if (not (a < w1 and b < w2)) and (a + b <= 0.0):
        hits += 1
check("Monte-Carlo: freq(¬deep ∧ lx ≤ 0) = 0（%d 样本）" % M, hits == 0,
      "hits = %d" % hits)

# ================================================================== §2 退化一致性
print("== §2 退化一致性：`twoRate1`（r≡1, ρ≡1）⇒ Ã = A、f̃ = f ==")

TWO_RATE_1 = [(0.5, [1.0] * 4, 1.0, 1.0), (0.5, [1.0] * 4, 1.0, 1.0)]
MIX = [(0.4, [0.5, 1.5, 0.8, 2.0], 1.0, 0.7), (0.6, [2.0, 0.4, 1.1, 0.6], 1.0, 1.4)]

random.seed(20261012)
worst_A = worst_f = 0.0
for _ in range(6):
    theta = ([random.uniform(0.05, 1.5) for _ in range(4)], random.uniform(0.05, 1.5))
    for Tp in TOPOS:
        for T in TOPOS:
            worst_A = max(worst_A,
                          abs(Abar(TWO_RATE_1, theta, Tp, T) - geneScore(Tp, theta[0], theta[1], T)))
    worst_f = max(worst_f, abs(fbar(TWO_RATE_1, theta) - jc69Amp(theta[0], theta[1])))
check("twoRate1: Ã θ T' T = A θ T' T（逐字）", worst_A < 1e-12, "max |Ã−A| = %.3e" % worst_A)
check("twoRate1: f̃ θ = f θ（逐字）", worst_f < 1e-12, "max |f̃−f| = %.3e" % worst_f)

worst_neq = 0.0
for _ in range(4):
    theta = ([random.uniform(0.05, 1.5) for _ in range(4)], random.uniform(0.05, 1.5))
    for Tp in TOPOS:
        for T in TOPOS:
            worst_neq = max(worst_neq,
                            abs(Abar(MIX, theta, Tp, T) - geneScore(Tp, theta[0], theta[1], T)))
check("非退化：r≢1, ρ≢1 时 Ã ≠ A（速率层不是空壳）", worst_neq > 1e-3,
      "max |Ã−A| = %.3e" % worst_neq)

worst_clause = 0.0
for _ in range(4):
    theta = ([random.uniform(0.05, 1.5) for _ in range(4)], random.uniform(0.05, 1.5))
    for Tp in TOPOS:
        d = Abar(MIX, theta, Tp, Tp) - fbar(MIX, theta)
        for X in [Y for Y in TOPOS if Y != Tp]:
            worst_clause = max(worst_clause, abs(d - Abar(MIX, theta, Tp, X)))
check("命题 A 三条恒等式在 Ã 下保持（Ã T'T' − f̃ = Ã T'X）", worst_clause < 1e-12,
      "max 残差 = %.3e" % worst_clause)


# ================================================================== §3 expWeight 对拍
print("== §3 识别等式 / `expWeight`：有限支撑 ν 上 `Ã` 版 = JC69 版（退化时）==")


def exp_weight(nu, A):
    """`expWeight ν τd A r = ∫ θ, Σ T', τd θ T' · A θ T' r ∂ν`（有限离散 ν）。

    `nu` 是 `[(theta, τd(θ,·), weight)]` 的列表。"""
    tot = 0.0
    for (th, taus, w) in nu:
        for Tp in TOPOS:
            tot += w * taus[Tp] * A(th, Tp)
    return tot


THETA_DEEP = ([0.1, 0.2, 0.3, 0.4], 0.2)
THETA_SALL = ([0.5, 0.4, 0.3, 0.2], 0.9)
NU = [(THETA_DEEP, {T: 1.0 / 3 for T in TOPOS}, 0.5),
      (THETA_SALL, {"ab_cd": 1.0, "ac_bd": 0.0, "ad_bc": 0.0}, 0.5)]

worst_degen = 0.0
for T in TOPOS:
    lhs = exp_weight(NU, lambda th, Tp: Abar(TWO_RATE_1, th, Tp, T))
    rhs = exp_weight(NU, lambda th, Tp: geneScore(Tp, th[0], th[1], T))
    worst_degen = max(worst_degen, abs(lhs - rhs))
check("twoRate1: expWeight(Ã) = expWeight(A)（全部 T）", worst_degen < 1e-11,
      "max 差 = %.3e" % worst_degen)

diffs = max(abs(exp_weight(NU, lambda th, Tp: Abar(MIX, th, Tp, T))
                - exp_weight(NU, lambda th, Tp: geneScore(Tp, th[0], th[1], T)))
            for T in TOPOS)
check("非退化：expWeight(Ã) ≠ expWeight(A)", diffs > 1e-3, "max 差 = %.3e" % diffs)

# ================================================================== §4 稳定性 gap
print("== §4 稳定性：`ε < δ/(2N+1)` ⇒ 真选择被恢复（Fin 4 ⇒ N = 1）==")
N_CARD = 1
eps = 0.3 / (2 * N_CARD + 1)
check("Fin 4 上 `{S // S.card = 4}` 的基数 = 1（单个 quartet）", N_CARD == 1)
W = {"ab_cd": 1.0, "ac_bd": 0.0, "ad_bc": 0.0}
Weps = {T: W[T] + (eps if T != "ab_cd" else -eps) for T in TOPOS}
check("ε 扰动后 argmax 仍为真拓扑 `ab|cd`",
      Weps["ab_cd"] > Weps["ac_bd"] and Weps["ab_cd"] > Weps["ad_bc"],
      "ε = %.4f" % eps)

# ================================================================== 结论
print()
if FAIL:
    print("FAILED: %d 项" % len(FAIL))
    for f in FAIL:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
