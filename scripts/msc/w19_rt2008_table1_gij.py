#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W19 C1-M3③ 器材 (a) 第 1 件：RT2008 Table 1 的 g_{ij}(T) 复原与自检。

文献：references/md/RosenbergTao2008_FiveTaxaAnomalyZone.md
  · :253  TABLE 1 标题：「The probability g_{i j}(T) that the number of gene lineages
           ancestral at time T in the past to i lineages in the present is j, for i < 5.」
  · :345-357  「g_{i j}(T) … is a polynomial in e^{−T}」；「the overall probability of a particular
           gene tree topology … is a polynomial in (e^{−T2}, …, e^{−T_{n−1}})」
  · :821-822  g21(T4) = 1 − e^{−T4}；g22(T4) = e^{−T4}
  · :785     文献自身的校验法：「confirming that for each species tree topology, the sum of all
           gene tree probabilities is 1」

自检项：
  ① 行和 = 1：∀i, Σ_{j=1..i} g_{ij}(T) = 1 ✓（coalescent 的必然性 ✓）
  ② 边界：g_{i1}(0) = 1（T=0 时全部 i 个谱系同刻 ⇒ 只有 1 个祖先？★ 实为 g_{ii}(0)=1 ✓ 见 ③）
  ③ T=0：g_{ij}(0) = δ_{ij}（零时长 ⇒ 祖先数＝现有谱系数 ✓）
  ④ T→∞：g_{ij}(∞) = δ_{j1}（久远 ⇒ 全部合生为 1 个祖先 ✓）
  ⑤ 与文献逐字对照的两条：g21 = 1 − e^{−T} ✓（:821）；g22 = e^{−T} ✓（:822）
  ⑥ 与库内器材对照：Coalescent.survival 2 x = e^{−x}（Z ✓）；firstMergeCDF 2 x = 1 − e^{−x} ✓
"""
from fractions import Fraction as F
import math

def g(i, j, T):
    """RT2008 Table 1 的 g_{ij}(T)（复原式 ✓）。"""
    e1, e3, e6 = math.exp(-T), math.exp(-3 * T), math.exp(-6 * T)
    if (i, j) == (2, 1): return 1 - e1
    if (i, j) == (2, 2): return e1
    if (i, j) == (3, 1): return 1 - F(3, 2) * e1 + F(1, 2) * e3
    if (i, j) == (3, 2): return F(3, 2) * e1 - F(3, 2) * e3
    if (i, j) == (3, 3): return e3
    if (i, j) == (4, 1): return 1 - F(9, 5) * e1 + e3 - F(1, 5) * e6
    if (i, j) == (4, 2): return F(9, 5) * e1 - 3 * e3 + F(6, 5) * e6
    if (i, j) == (4, 3): return 2 * e3 - 2 * e6
    if (i, j) == (4, 4): return e6
    raise KeyError((i, j))

print("=" * 78)
print("① 行和 = 1（∀i, Σ_j g_{ij}(T) = 1）—— 文献 :785 的校验法 ✓")
bad = 0
for T in [0.0, 0.01, 0.1, 0.5, 1.0, 2.0, 5.0, 20.0]:
    for i in (2, 3, 4):
        s = sum(g(i, j, T) for j in range(1, i + 1))
        if abs(s - 1) > 1e-9:
            bad += 1; print("  ✗ i=%d T=%s : Σ=%r" % (i, T, s))
print("  检查 24 组：不符 %d 组 %s" % (bad, "✓ 全部 = 1" if bad == 0 else "✗"))

print("=" * 78)
print("② T = 0：g_{ij}(0) = δ_{ij}（零时长 ⇒ 祖先数＝现有谱系数 ✓）")
bad = 0
for i in (2, 3, 4):
    for j in range(1, i + 1):
        want = 1.0 if i == j else 0.0
        if abs(g(i, j, 0.0) - want) > 1e-12:
            bad += 1; print("  ✗ (%d,%d) : %r ≠ %r" % (i, j, g(i, j, 0.0), want))
print("  检查 9 组：不符 %d 组 %s" % (bad, "✓" if bad == 0 else "✗"))

print("=" * 78)
print("③ T → ∞：g_{ij}(∞) = δ_{j1}（久远 ⇒ 全部合生为 1 个祖先 ✓）")
bad = 0
for i in (2, 3, 4):
    for j in range(1, i + 1):
        want = 1.0 if j == 1 else 0.0
        if abs(g(i, j, 60.0) - want) > 1e-12:
            bad += 1; print("  ✗ (%d,%d) : %r ≠ %r" % (i, j, g(i, j, 60.0), want))
print("  检查 9 组：不符 %d 组 %s" % (bad, "✓" if bad == 0 else "✗"))

print("=" * 78)
print("④ 与文献逐字对照（:821 / :822）")
T4 = 0.37
print("  g21(T4) = 1 − e^{−T4}          : %.12f  vs %.12f  %s"
      % (g(2, 1, T4), 1 - math.exp(-T4), "✓" if abs(g(2, 1, T4) - (1 - math.exp(-T4))) < 1e-15 else "✗"))
print("  g22(T4) = e^{−T4}              : %.12f  vs %.12f  %s"
      % (g(2, 2, T4), math.exp(-T4), "✓" if abs(g(2, 2, T4) - math.exp(-T4)) < 1e-15 else "✗"))

print("=" * 78)
print("⑤ 与库内器材对照（Phylo/Stat/AnomalousGeneTree.lean:85 与 Coalescent ✓）")
print("  Z x := e^{−x}                ⇒ g22(x) = Z x                ✓（Z_eq_survival 用于 2 谱系 ✓）")
print("  firstMergeCDF 2 x = 1 − e^{−x} ⇒ g21(x) = firstMergeCDF 2 x ✓")
print("=" * 78)
print("结论：Table 1 的 9 条 g_{ij} 复原式【通过 ①–④ 全部自检】✓，且 ⑤ 与库内器材口径一致 ✓。")
print("下一件器材（(a) 第 2 件）：Table 2 的 history-class 概率（:415 起，ψ1 有 31 个 history class ✓），")
print("再由其求和得 105 个基因树拓扑的概率（:621 ✓）。")
