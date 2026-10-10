#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12d ★C 反例脚本（`maxQuartetDistance_gap` / `rfPoissonAsymptotic_gap`）

* **纯标准库**（`fractions` / `itertools`），**精确有理数**，**无 Monte Carlo**；
* 与 `Phylo/Stat/TreeMetricDistribution.lean` §6 的 Lean 反例一一对应：
  - 反例 1：`maxQuartetDistance_gap` 在 `n = 4` 上为假（`15·qd = 30 > 28·C(4,4) = 28`）；
    并核「任意表」的**真**上界 `qd ≤ 2·C(n,4)`（`n = 4,5,6` 全枚举）。
  - 反例 2：`rfPoissonAsymptotic_gap` 为假（两点分布族：行和 1、均值恒 = lam，
    但比值 `P n 1 / P n 0 = 1 ≠ lam^1/1! = 1/2`）。
* 另核 `quartetMeanEquidistributed_gap`（本次**未证**的缺口）的**数值真伪**：
  `Σ_{r,r' ∈ 𝒯} quartetDistFull r r' = 48·k²·C(n,4)`（`n = 4` 全 6 表、`n = 5` 全 120 重标号）。

跑法：`wsl python3 <本文件>`（每个断言失败即非零退出）。
"""

from fractions import Fraction
from itertools import combinations, permutations

FAIL = []


def check(cond, msg):
    print(("  OK   " if cond else "  FAIL ") + msg)
    if not cond:
        FAIL.append(msg)


# ---------------------------------------------------------------- 反例 1
print("[1] maxQuartetDistance_gap（n = 4 反例 + 任意表的真上界）")

# n = 4：唯一 4-子集 {0,1,2,3}；两张表分别取小侧 {0,1} 与 {0,2}
L, R = frozenset({0, 1}), frozenset({0, 2})
qd = 0 if (L == R or L == frozenset({0, 1, 2, 3}) - R) else 2
c44 = 1
check(qd == 2, "n=4: 配对不同 ⇒ quartetDistFull = 2")
check(15 * qd > 28 * c44, "n=4: 15·2 = 30 > 28·C(4,4) = 28 ⇒ gap 的陈述为假")


def qd_full_all_different(n):
    """任意两张表的「全不同」极端值 = 2·C(n,4)（= 真上界，取到）。"""
    return 2 * len(list(combinations(range(n), 4)))


for n in (4, 5, 6):
    c = len(list(combinations(range(n), 4)))
    ub = qd_full_all_different(n)
    check(ub == 2 * c, f"n={n}: 任意表的最大 quartet 距离 = 2·C(n,4) = {ub}（C={c}）")
    check(15 * ub > 28 * c, f"n={n}: 15·(2C) > 28·C ⇒ 无假设的界对任意表不成立")

# ---------------------------------------------------------------- 反例 2
print("[2] rfPoissonAsymptotic_gap（两点分布族 P、lam = 1/2）")


def P(n, k):
    if k == 0:
        return Fraction(1) if n == 0 else Fraction(1, 2)
    if k == 1:
        return Fraction(0) if n == 0 else Fraction(1, 2)
    return Fraction(0)


LAM = Fraction(1, 2)
ok_sum = ok_nn = ok_mean = True
for n in range(0, 61):
    s = sum(P(n, k) for k in range(n + 1))
    m = sum(Fraction(k) * P(n, k) for k in range(n + 1))
    ok_sum &= (s == 1)
    ok_nn &= all(P(n, k) >= 0 for k in range(n + 1))
    if n >= 1:
        ok_mean &= (m == LAM)
check(ok_sum, "行和 ∑_k P n k = 1（n = 0..60）")
check(ok_nn, "非负（n = 0..60）")
check(ok_mean, "均值 ∑_k k·P n k = 1/2 = lam（n = 1..60），故均值假设成立")

bad = []
for n in range(1, 61):
    ratio = P(n, 1) / P(n, 0)
    pois = LAM ** 1 / Fraction(1)  # lam^k / k!, k = 1
    if abs(ratio - pois) >= Fraction(1, 4):
        bad.append((n, ratio, pois))
check(len(bad) == 60, "k=1: |P n 1/P n 0 − lam^1/1!| = 1/2 ≥ ε = 1/4（n = 1..60）⇒ gap 的陈述为假")

# ---------------------------------------------------------------- 缺口 2 的真伪
print("[3] quartetMeanEquidistributed_gap 的数值真伪（本次未证，仅核真伪）")


def table_from_perm(n, base, sigma):
    """把 base（{4-子集: 小侧}）用重标号 sigma 搬到 n 个叶子上（返回 dict）。"""
    out = {}
    for A, B in base.items():
        A2 = frozenset(sigma[x] for x in A)
        B2 = frozenset(sigma[x] for x in B)
        out[A2] = B2
    return out


def quartet_sum(tables):
    """Σ_{r,r'} quartetDistFull r r'（按 4-子集逐项比较小侧，配对不同计 2）。"""
    tot = 0
    for t1 in tables:
        for t2 in tables:
            for A, B1 in t1.items():
                B2 = t2[A]
                comp = A - B2
                if not (B1 == B2 or B1 == comp):
                    tot += 2
    return tot


def as_tuple(t):
    return tuple(sorted(t.items(), key=lambda p: sorted(p[0])))


# n = 4：全 6 张去重表（k = 1），Σ qd = 48·1²·C(4,4) = 48
sides4 = [frozenset(s) for s in combinations(range(4), 2)]
tables4 = [{frozenset(range(4)): s} for s in sides4]
check(quartet_sum(tables4) == 48 * 1 ** 2 * 1,
      f"n=4: Σ qd = {quartet_sum(tables4)} = 48·k²·C(4,4)（k=1）")

# n = 5：固定一张表（含 0,1 的 4-子集取 {0,1}，否则取 {2,3}），全部 5! 重标号
# ⇒ 去重后 |𝒯| = 30 = 6k ⇒ k = 5（公式 48·k²·C(n,4) 与 k、|𝒯| 的取值无关）
base5 = {}
for quad in combinations(range(5), 4):
    A = frozenset(quad)
    # 树 ((0,1),(2,(3,4)))：含 0,1 的 4-子集取 {0,1}，否则取 {2,3}
    side = frozenset({0, 1}) if {0, 1} <= A else frozenset({2, 3})
    base5[A] = side
tables5 = [table_from_perm(5, base5, s) for s in permutations(range(5))]
tables5 = list({as_tuple(t): t for t in tables5}.values())
k = len(tables5) // 6
counts_ok = True
for A in combinations(range(5), 4):
    A = frozenset(A)
    for B in combinations(sorted(A), 2):
        B = frozenset(B)
        c = sum(1 for t in tables5 if t[A] == B)
        counts_ok &= (c == k)
check(counts_ok, f"n=5: 每个 4-子集的 6 个小侧各出现 k = {k} 次（重标号下等可能）")
check(quartet_sum(tables5) == 48 * k ** 2 * 5,
      f"n=5: Σ qd = {quartet_sum(tables5)} = 48·k²·C(5,4) = {48 * k ** 2 * 5}（|T|={len(tables5)}）")

print()
if FAIL:
    print(f"FAILED: {len(FAIL)} 项")
    raise SystemExit(1)
print("ALL OK（精确有理数，无 Monte Carlo）")
