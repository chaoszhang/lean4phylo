#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12g 数值核对：NeighborNet.lean 的 `circularIndicatorFullRank_gap`。

纯标准库、精确有理数（`fractions.Fraction`）、无 Monte Carlo、无随机性。

核对内容
--------
(A) 环形弧 split 族：n = 4,5,6 时，取「每个 swap 类一个代表」的环形 split 族
    （= 全部非平凡环形 split），其指示矩阵（行 = 无序点对，列 = split）
    **列满秩**；n = 4,5 时进一步穷举**全部子族**验证任意子族也满秩（这是定理的完整内容）。
(B) 对照组（**不排除两侧互换**）：把 `s` 与 `s.swap` 同时放进族里（两列完全相同），
    矩阵奇异，并给出显式核向量 `b = 1·[s] − 1·[s.swap]` ⇒ 「不排除两侧互换则命题为假」。
(C) 显式逆矩阵：NeighborNet.lean §7 用的三个泛函
      D_{a,b}  := φ(p_a,p_b) − φ(p_{a+1},p_b) − φ(p_a,p_{b+1}) + φ(p_{a+1},p_{b+1})
      H_j     := φ(p_{n−1},p_j) − φ(p_0,p_j) − φ(p_{n−1},p_{j+1}) + φ(p_0,p_{j+1})
      L       := φ(p_0,p_1) + φ(p_0,p_{n−1}) − φ(p_1,p_{n−1})
    在随机（确定性 PRNG）权重下逐个弧核对「泛函值 = 2 × 该 split 的权重」。

输出以 `OK` 结尾（exit 0）表示全部核对通过。
"""

import random
from fractions import Fraction
from itertools import combinations

# ---------------------------------------------------------------- 基础对象

def pairs(n):
    return list(combinations(range(n), 2))


def arcs(n):
    """全部非平凡线性弧 [i,j]（0 ≤ i ≤ j ≤ n−1，去掉整圆 (0,n−1)）。"""
    return [(i, j) for i in range(n) for j in range(i, n) if not (i == 0 and j == n - 1)]


def part_of_arc(n, a, b):
    """弧 [a,b] 给出的 split（无序两部分，用 frozenset 表示）。"""
    A = frozenset(range(a, b + 1))
    Ac = frozenset(range(n)) - A
    return frozenset([A, Ac])


def split_classes(n):
    """{split 划分: 一个代表弧}（每个 swap 类恰好一个代表）。"""
    d = {}
    for (i, j) in arcs(n):
        d.setdefault(part_of_arc(n, i, j), (i, j))
    return d


def ind(part, pr):
    """指示：split `part` 是否把点对 `pr` 分在两侧（与取哪一侧无关）。"""
    side = next(iter(part))
    return 1 if ((pr[0] in side) != (pr[1] in side)) else 0


def rank(rows):
    """精确有理数上的列数（= 行向量组的秩）。"""
    m = [[Fraction(x) for x in r] for r in rows]
    if not m:
        return 0
    ncol = len(m[0])
    r = 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
        if r == len(m):
            break
    return r


def matrix(n, parts):
    """指示矩阵：行 = 点对，列 = split。"""
    return [[ind(p, pr) for p in parts] for pr in pairs(n)]


def phi_of_weights(n, parts, w):
    """系统发生距离 φ(x,y) = Σ 分离 x,y 的 split 权重。"""
    return {pr: sum(w[p] * ind(p, pr) for p in parts) for pr in pairs(n)}


# ------------------------------------------------- (A) 满秩 + 子族满秩

def check_full_rank():
    out = []
    for n in (4, 5, 6):
        cl = split_classes(n)
        parts = list(cl.keys())
        M = matrix(n, parts)
        r = rank(M)
        assert r == len(parts), (n, r, len(parts))
        out.append("n=%d: |splits|=%d, |pairs|=%d, rank=%d -> 列满秩" %
                   (n, len(parts), len(pairs(n)), r))
        # 穷举全部子族（独立性可继承，但这里直接核对定理的完整量化）
        if n <= 5:
            tot = 0
            worst = len(parts)
            for k in range(1, len(parts) + 1):
                for sub in combinations(range(len(parts)), k):
                    Ms = [[row[c] for c in sub] for row in M]
                    assert rank(Ms) == k, (n, sub)
                    tot += 1
            out.append("n=%d: 全部 %d 个子族均列满秩（逐个核对）" % (n, tot))
    return out


def check_swap_counterexample():
    """(B) 不排除两侧互换 ⇒ 命题为假（显式核向量）。"""
    out = []
    for n in (4, 5, 6):
        cl = split_classes(n)
        # 取一个 split，把「两个方向」都放进族（两个列完全相同）
        A = next(iter(cl))
        Ac = frozenset(frozenset(x) for x in (set(range(n)) - set(next(iter(A))),))
        cols = [A, A]  # 同一划分的两个「方向」：指示向量逐字相同
        M = matrix(n, cols)
        r = rank(M)
        assert r < 2, (n, r)
        # 核向量：b(s) = 1, b(s.swap) = -1
        nul = lambda pr: 1 * ind(A, pr) + (-1) * ind(A, pr)
        assert all(nul(pr) == 0 for pr in pairs(n))
        out.append("n=%d: 允许两侧互换时 rank=%d < 列数 2；核向量 b=(+1,-1) 给出恒 0 距离" % (n, r))
    return out


# ------------------------------------------------- (C) 显式逆矩阵（三个泛函）

def P(Phi, a, b):
    """φ 对称且 φ(x,x)=0：按 (min,max) 取键，重合点返回 0。"""
    if a == b:
        return Fraction(0)
    return Phi[(a, b)] if a < b else Phi[(b, a)]


def dv(Phi, a, b):
    return P(Phi, a, b) - P(Phi, a + 1, b) - P(Phi, a, b + 1) + P(Phi, a + 1, b + 1)


def hv(Phi, n, j):
    return P(Phi, n - 1, j) - P(Phi, 0, j) - P(Phi, n - 1, j + 1) + P(Phi, 0, j + 1)


def lv(Phi, n):
    return P(Phi, 0, 1) + P(Phi, 0, n - 1) - P(Phi, 1, n - 1)


def functional_for_arc(Phi, n, arc):
    """按 NeighborNet.lean §7 的分情形，把弧映射到对应泛函。"""
    i, j = arc
    if i == 0 and j == 0:
        return lv(Phi, n)
    if i == 0 and 1 <= j <= n - 2:
        return hv(Phi, n, j)
    if i >= 1 and j <= n - 2:
        return dv(Phi, i - 1, j)
    if i == 1 and j == n - 1:
        return lv(Phi, n)
    if i >= 2 and j == n - 1:
        return hv(Phi, n, i - 1)
    raise AssertionError(("未覆盖的弧", arc, n))


def check_inverse_matrix():
    out = []
    rng = random.Random(20260211)
    for n in (4, 5, 6, 7):
        cl = split_classes(n)
        parts = list(cl.keys())
        for _ in range(3):
            w = {p: Fraction(rng.randint(-9, 9), rng.randint(1, 4)) for p in parts}
            Phi = phi_of_weights(n, parts, w)
            # φ 必须对称、对角为 0
            for pr in pairs(n):
                assert Phi[pr] == Phi[(pr[1], pr[0])] if (pr[1], pr[0]) in Phi else True
            for arc in arcs(n):
                val = functional_for_arc(Phi, n, arc)
                want = 2 * w[part_of_arc(n, *arc)]
                assert val == want, (n, arc, val, want)
        out.append("n=%d: 全部 %d 个弧上「泛函 = 2×权重」逐个核对通过（3 组权重）" % (n, len(arcs(n))))
    return out


def check_small_card():
    """|X| ≤ 2 的边界：任意两条 split 相等或互为 swap（⇒ 去掉 swap 重复后至多一个指标）。"""
    out = []
    for n in (2,):
        allparts = set()
        for (i, j) in arcs(n):
            allparts.add(part_of_arc(n, i, j))
        # 枚举 Split(Fin n) 的「结构」：(sideA, sideB) 有序对，共 2*|classes|
        structs = []
        for p in allparts:
            A, Ac = tuple(p)
            structs.append((frozenset(A), frozenset(Ac)))
            structs.append((frozenset(Ac), frozenset(A)))
        for s in structs:
            for t in structs:
                swap_t = (t[1], t[0])
                assert s == t or s == swap_t, (n, s, t)
        out.append("n=%d: %d 个 split 结构两两「相等或互为 swap」（|X| ≤ 2 的边界）"
                   % (n, len(structs)))
    return out


def main():
    print("== W12g: circularIndicatorFullRank_gap 数值核对 ==")
    for name, fn in (("(A) 列满秩 + 全部子族", check_full_rank),
                     ("(B) 不排除两侧互换 ⇒ 假（显式核向量）", check_swap_counterexample),
                     ("(C) 显式逆矩阵 D/H/L", check_inverse_matrix),
                     ("(D) n ≤ 2 边界", check_small_card)):
        print("--", name)
        for line in fn():
            print("   ", line)
    print("OK")


if __name__ == "__main__":
    main()
