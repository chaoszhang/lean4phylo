#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W13b+c 数值对拍：有限支撑速率层 / `Ã` / `f̃` / 混合可交换性 / 箱体一致下界。

对拍对象（Lean 侧 `Phylo/Stat/SiteRateMixture.lean`）：

* `SiteRateModel.scale`          —— 枝长按 `(r k i · ρ k, ρ k)` 缩放；
* `SiteRateModel.ampScaled`      —— JC69 幅度在缩放后枝长上的值；
* `SiteRateModel.Abar` / `fbar`  —— `∑ k, w k · A (scale θ k)`；
* `SiteRateModel.ampBox` / `deltaBox` —— 箱体一致下界常数；
* `Abar_clause_*`                —— 命题 A 三条恒等式在 `Ã` 下保持；
* `siteWeightExpect_eq_expWeight` —— 识别等式（混合可交换性）。

本脚本**穷举小情形**（`Topo` 三个元素、`Fin 4` 四个叶、`Rate` 有限支撑），
只用标准库。运行：`python3 scripts/msc/W13b_rate_mixture_check.py`。
"""

import math
import random
import sys

# ---------------------------------------------------------------- 库内 JC69 形态
LAM_JC = 4.0 / 3.0


def e(x: float) -> float:
    """`Phylo.JC.e x = exp(-(4/3)·x)`（`Phylo/JukesCantor.lean:151`）。"""
    return math.exp(-LAM_JC * x)


def jc69Amp(leaf, lx: float) -> float:
    """`CASTERGeneTree.jc69Amp l lx = (3/4)·∏_i e(l i)·(1 - e lx)`（:515）。"""
    p = 1.0
    for v in leaf:
        p *= e(v)
    return 0.75 * p * (1.0 - e(lx))


TOPO = ("ab_cd", "ac_bd", "ad_bc")


def A_val(f: float, Tprime: str, r: str) -> float:
    """命题 A 的幅度形态：`T' = r` 时 `A = 2f`，否则 `A = f`。

    ⇒ `A θ T' T' - f = f = A θ T' (r ≠ T')`，即 `CASTERBridge.PropAData` 的三条子句。
    """
    return 2.0 * f if Tprime == r else f


# ---------------------------------------------------------------- 速率层
def scale(leaf, lx, rvec, rho):
    """`SiteRateModel.scale`：叶枝 `r k i · ρ k · l i`、内枝 `ρ k · lx`。"""
    return tuple(rvec[i] * rho * leaf[i] for i in range(4)), rho * lx


def ampScaled(leaf, lx, rvec, rho):
    """`SiteRateModel.ampScaled`（与 `jc69Amp (scale ...)` 逐字相等）。"""
    l2, lx2 = scale(leaf, lx, rvec, rho)
    return jc69Amp(l2, lx2)


def fbar(leaf, lx, w, rates):
    """`SiteRateModel.fbar θ = ∑ k, w k · f (scale θ k)`。"""
    return sum(w[k] * ampScaled(leaf, lx, rates[k][0], rates[k][1]) for k in range(len(w)))


def Abar(leaf, lx, w, rates, Tprime, r):
    """`SiteRateModel.Abar θ T' r = ∑ k, w k · A (scale θ k) T' r`。"""
    return sum(w[k] * A_val(ampScaled(leaf, lx, rates[k][0], rates[k][1]), Tprime, r)
               for k in range(len(w)))


def _fmt(x):
    return f"{x:.15g}"


def _rand_case(rng, nrate_max=4, ntheta_max=3):
    nrate = rng.randint(1, nrate_max)
    w = [rng.random() for _ in range(nrate)]
    s = sum(w)
    w = [x / s for x in w]
    rates = [([rng.uniform(0.4, 2.0) for _ in range(4)], rng.uniform(0.4, 2.0))
             for _ in range(nrate)]
    ntheta = rng.randint(1, ntheta_max)
    nu = [rng.random() for _ in range(ntheta)]
    sn = sum(nu)
    nu = [x / sn for x in nu]
    thetas = []
    for _ in range(ntheta):
        leaf = tuple(rng.uniform(0.0, 2.0) for _ in range(4))
        lx = rng.uniform(0.1, 2.0)
        t = [rng.random() for _ in range(3)]
        st = sum(t)
        thetas.append((leaf, lx, [x / st for x in t]))
    return w, rates, nu, thetas


def check_amp_scaled():
    """[1] `ampScaled_eq_jc69Amp`：乘以速率 ≡ 把速率乘到枝长上再算幅度。"""
    rng = random.Random(20261012)
    worst = 0.0
    n = 0
    for _ in range(4000):
        leaf = tuple(rng.uniform(0.0, 3.0) for _ in range(4))
        lx = rng.uniform(0.0, 3.0)
        rvec = [rng.uniform(0.5, 2.5) for _ in range(4)]
        rho = rng.uniform(0.5, 2.5)
        worst = max(worst, abs(ampScaled(leaf, lx, rvec, rho) - jc69Amp(*scale(leaf, lx, rvec, rho))))
        n += 1
    return n, worst


def check_clause_preservation():
    """[2] `Abar_clause_*`：`Ã θ T' T' - f̃ θ = Ã θ T' r`（r ≠ T'，且两支相等）。"""
    rng = random.Random(4242)
    worst = 0.0
    n = 0
    for _ in range(2000):
        w, rates, _, thetas = _rand_case(rng)
        leaf, lx, _ = thetas[0]
        fb = fbar(leaf, lx, w, rates)
        for Tprime in TOPO:
            others = [t for t in TOPO if t != Tprime]
            lhs = Abar(leaf, lx, w, rates, Tprime, Tprime) - fb
            for r in others:
                worst = max(worst, abs(lhs - Abar(leaf, lx, w, rates, Tprime, r)))
                n += 1
            worst = max(worst, abs(Abar(leaf, lx, w, rates, Tprime, others[0])
                                   - Abar(leaf, lx, w, rates, Tprime, others[1])))
    return n, worst


def check_mixture_commutes():
    """[3] 识别等式的**实质**内容：速率混合与 `(θ, T')` 期望可交换。

    LHS（生成过程序：k 在最内层）
        `∑_θ ν ∑_T' τd_{θT'} ∑_k w_k · A(scale θ k) T' r`
    RHS（库内序：先合成 `Ã`，再 `expWeight ν τd Ã r`）
        `∑_θ ν ∑_T' τd_{θT'} · Ã θ T' r`
    """
    rng = random.Random(7)
    worst = 0.0
    worst_fact = 0.0
    n = 0
    for _ in range(2000):
        w, rates, nu, thetas = _rand_case(rng)
        for r in TOPO:
            lhs = 0.0
            for idx, (leaf, lx, t) in enumerate(thetas):
                inner = 0.0
                for j, Tprime in enumerate(TOPO):
                    s = 0.0
                    for k in range(len(w)):  # k 在最内层：真正的「生成过程」顺序
                        s += w[k] * A_val(ampScaled(leaf, lx, rates[k][0], rates[k][1]), Tprime, r)
                    inner += t[j] * s
                lhs += nu[idx] * inner
            rhs = 0.0
            for idx, (leaf, lx, t) in enumerate(thetas):
                inner = 0.0
                for j, Tprime in enumerate(TOPO):
                    inner += t[j] * Abar(leaf, lx, w, rates, Tprime, r)
                rhs += nu[idx] * inner
            # 再把 k 提到最外层（联合律因子化：k ⊥ (θ, T')）
            outer = 0.0
            for k in range(len(w)):
                acc = 0.0
                for idx, (leaf, lx, t) in enumerate(thetas):
                    inner = 0.0
                    for j, Tprime in enumerate(TOPO):
                        inner += t[j] * A_val(ampScaled(leaf, lx, rates[k][0], rates[k][1]), Tprime, r)
                    acc += nu[idx] * inner
                outer += w[k] * acc
            worst = max(worst, abs(lhs - rhs), abs(lhs - outer))
            n += 1
    return n, worst


def check_degenerate():
    """[4] 退化一致性：`r ≡ 1, ρ ≡ 1` ⇒ `Ã = A`、`f̃ = f`（逐字）。"""
    rng = random.Random(99)
    wa = wf = 0.0
    for _ in range(3000):
        leaf = tuple(rng.uniform(0.0, 3.0) for _ in range(4))
        lx = rng.uniform(0.0, 3.0)
        w = [0.5, 0.5]                                    # Rate = Fin 2
        rates = [([1.0] * 4, 1.0), ([1.0] * 4, 1.0)]      # r ≡ 1, ρ ≡ 1
        for Tprime in TOPO:
            for r in TOPO:
                wa = max(wa, abs(Abar(leaf, lx, w, rates, Tprime, r)
                                 - A_val(jc69Amp(leaf, lx), Tprime, r)))
        wf = max(wf, abs(fbar(leaf, lx, w, rates) - jc69Amp(leaf, lx)))
    return wa, wf


def check_box_bound():
    """[5] 箱体一致下界：叶长 ∈ [0, lmax]、内枝长 ≥ lx0 ⇒ `deltaBox ≤ f̃`。

    `ampBox = (3/4)·e(rU·ρU·lmax)^4·(1 - e(ρL·lx0))`、`deltaBox = wRef·ampBox`
    （`wRef = w kRef`，`twoRate1` 下 = 1/2）。
    """
    rng = random.Random(2026)
    wRef, lmax, lx0 = 0.5, 2.0, 0.25
    rU, rhoU, rhoL = 2.0, 2.0, 0.5
    deltaBox = wRef * 0.75 * (e(rU * rhoU * lmax) ** 4) * (1.0 - e(rhoL * lx0))
    min_slack = float("inf")
    n = 0
    for _ in range(20000):
        leaf = tuple(rng.uniform(0.0, lmax) for _ in range(4))
        lx = rng.uniform(lx0, 6.0)
        rvec = [rng.uniform(0.4, rU) for _ in range(4)]
        rho = rng.uniform(rhoL, rhoU)
        min_slack = min(min_slack, ampScaled(leaf, lx, rvec, rho) - deltaBox)
        n += 1
    # 边角：叶长全 0 时 ∏e = 1（乘积最大）⇒ 仍应满足；但 rU·ρU·lmax 项给出的是下界
    min_slack = min(min_slack, ampScaled((0.0,) * 4, lx0, [rhoL] * 4, rhoL)
                    - 0.75 * (e(rU * rhoU * lmax) ** 4) * (1 - e(rhoL * lx0)))
    return n, deltaBox, min_slack


def check_unrestricted_bound_false():
    """[6] ★D 反例：无限制量化域的一致下界为假 —— 内枝长 = 0 时 `f̃ = 0`。"""
    return ampScaled((1.0, 1.0, 1.0, 1.0), 0.0, [1.0] * 4, 1.0)


def main():
    print("=== W13b+c 数值对拍（穷举小情形 / 有限支撑速率层） ===")
    fails = []

    n, worst = check_amp_scaled()
    print(f"[1] ampScaled == jc69Amp(scale θ k)      : n={n:5d}  max|diff| = {_fmt(worst)}")
    if not worst < 1e-12:
        fails.append(1)

    n, worst = check_clause_preservation()
    print(f"[2] Ã 下命题 A 三条恒等式保持            : n={n:5d}  max|diff| = {_fmt(worst)}")
    if not worst < 1e-12:
        fails.append(2)

    n, worst = check_mixture_commutes()
    print(f"[3] 混合可交换（识别等式的实质）         : n={n:5d}  max|diff| = {_fmt(worst)}")
    if not worst < 1e-12:
        fails.append(3)

    wa, wf = check_degenerate()
    print(f"[4] 退化 r≡1,ρ≡1 ⇒ Ã=A / f̃=f            : max|Ã-A| = {_fmt(wa)}  max|f̃-f| = {_fmt(wf)}")
    if not (wa < 1e-12 and wf < 1e-12):
        fails.append(4)

    n, dbox, slack = check_box_bound()
    print(f"[5] 箱体一致下界 deltaBox ≤ f̃            : n={n:5d}  deltaBox = {_fmt(dbox)}  "
          f"min slack = {_fmt(slack)}")
    if not slack >= -1e-12:
        fails.append(5)

    zero = check_unrestricted_bound_false()
    print(f"[6] ★D 反例：内枝长=0 ⇒ f̃ = {_fmt(zero)}  （故无限制一致下界为假）")
    if not (zero == 0.0):
        fails.append(6)

    print("--- 结论 ---")
    if fails:
        print(f"  FAIL: {fails}")
        return 1
    print("  [1][2][3][4] 偏差 ~1e-15（浮点级）⇒ 定义性恒等式 / 保持 / 混合可交换 / 退化一致性成立。")
    print("  [5] min slack > 0 ⇒ 箱体一致下界成立（量化域被 lmax / lx0 限制，这是诚实形态）。")
    print("  [6] = 0 ⇒ 与 Lean 侧 fbar_pos 需「内枝长 > 0」一致；无限制一致下界确为假。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
