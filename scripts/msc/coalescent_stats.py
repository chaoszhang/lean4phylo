#!/usr/bin/env python3
"""
scripts/msc/coalescent_stats.py —— `Phylo/Stat/CoalescentStats.lean` 的独立精确复核

全部用 `fractions.Fraction`（**精确有理数**，误差恒为 0；不用 Monte Carlo）：
  ① `k · E[τ_k] = 2/(k−1)`（`E[τ_k] = 2/(k(k−1))`）
  ② `E[L_n] = Σ_{k=2}^{n} 2/(k−1) = 2·H_{n−1}`
  ③ `Σ_{j=0}^{m−1} E[τ_{j+2}]·d_{j+2} = m`（Tajima 的核心恒等式；`d_k = k(k−1)/2`）
  ④ `Σ_{i=1}^{n−1} θ/i = θ·H_{n−1}`（SFS 求和记账）
  ⑤ Watterson 估计量无偏：`(θ·H_{n−1}) / H_{n−1} = θ`
"""
from fractions import Fraction as F

def sojournMean(k):          # E[τ_k] = 2/(k(k-1))
    return F(2, k * (k - 1))

def kingmanRate(k):          # d_k = k(k-1)/2
    return F(k * (k - 1), 2)

def harmonic(m):             # H_m
    return sum((F(1, j) for j in range(1, m + 1)), F(0))

def main():
    print("=" * 74)
    print("① k·E[τ_k] = 2/(k−1)")
    for k in range(2, 13):
        assert k * sojournMean(k) == F(2, k - 1), k
    print("   k = 2..12 全部**精确**成立 ✓")

    print("=" * 74)
    print("② E[L_n] = Σ_{k=2}^{n} 2/(k−1) = 2·H_{n−1}")
    for n in range(2, 13):
        lhs = sum((F(2, k - 1) for k in range(2, n + 1)), F(0))
        rhs = 2 * harmonic(n - 1)
        assert lhs == rhs, (n, lhs, rhs)
        print(f"   n={n:>3}  E[L]={lhs}  = 2·H_{n-1} ✓")
    print("   ⇒ 误差**恒为 0** ✓")

    print("=" * 74)
    print("③ Σ_{{j=0}}^{{m−1}} E[τ_{{j+2}}]·d_{{j+2}} = m   （Tajima 核心恒等式）")
    for m in range(1, 13):
        s = sum((sojournMean(j + 2) * kingmanRate(j + 2) for j in range(m)), F(0))
        assert s == m, (m, s)
    print("   m = 1..12 全部**精确**成立 ✓（每段时期恰贡献 1）")

    print("=" * 74)
    print("④ Σ_{{i=1}}^{{n−1}} θ/i = θ·H_{{n−1}}   （SFS 求和记账，θ 取有理数）")
    theta = F(3, 7)
    for n in range(2, 13):
        lhs = sum((theta / i for i in range(1, n)), F(0))
        rhs = theta * harmonic(n - 1)
        assert lhs == rhs, (n, lhs, rhs)
    print("   n = 2..12、θ = 3/7 全部**精确**成立 ✓")

    print("=" * 74)
    print("⑤ Watterson 估计量无偏：(θ·H_{{n−1}})/H_{{n−1}} = θ")
    for n in range(2, 13):
        H = harmonic(n - 1)
        assert (theta * H) / H == theta
    print("   n = 2..12 全部**精确**成立 ✓")

    print("=" * 74)
    print("VERDICT: PASS")

if __name__ == "__main__":
    main()
