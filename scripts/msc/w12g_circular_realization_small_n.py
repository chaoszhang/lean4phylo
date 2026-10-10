#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12g 第三轮：`circularDistanceRealization_gap_corrected` 的 n = 3,4,5 实例核对。

路线（★D：先核命题再动手）
--------------------------
对环序 `f = id`（`X = Fin n`），取**代表弧** `[i,j]`（`0 ≤ i ≤ j ≤ n−2`）——
它们一个一个 partition 类（每个环形 split 恰一个代表）。权重用 §7 的**显式逆矩阵行**：

  L（`i=0,j=0`）：  2w = φ(0,1) + φ(0,n−1) − φ(1,n−1)
  H（`i=0,j≥1`）：  2w = φ(n−1,j) − φ(0,j) − φ(n−1,j+1) + φ(0,j+1)
  D（`i≥1`）：      2w = φ(i−1,j) − φ(i,j) − φ(i−1,j+1) + φ(i,j+1)

核对内容（(A) 验证逆公式；(B) 验证**主命题**；(C) 给非负性的**证明路线**）
--------------------------------------------------------------------------
(A) 对**由随机非负权重生成的**环形距离（构造上 circular）：解出的 `w` 恰等于生成权重
    （⇒ 逆矩阵正确），且 `w ≥ 0`。
(B) **拒绝采样 / 网格穷尽**：均匀采样对称零对角 `d`，用 Kalmanson 不等式**筛选**
    （circular 是筛选结果而非构造前提），只对通过者核对 `w ≥ 0` 与 `phyleticDist = d`。
    ⚠️ (B) 必须如此设计：若像星形度量那样**构造** `d`，就等于把它预先放进代表弧张成的空间，
    检验退化成 (A)（循环论证）。
(C) 把非负性对应的 Kalmanson 四元组**显式列出**：D → 不等式 (2) 于 `(i−1,i,j,j+1)`；
    H → 不等式 (1) 于 `(0,j,j+1,n−1)`；L → 三角不等式（`i=j` 情形）。
"""

import random
from fractions import Fraction
from itertools import combinations

def pairs(n):
    return list(combinations(range(n), 2))

def reps(n):
    """代表弧：0 ≤ i ≤ j ≤ n−2。"""
    return [(i, j) for i in range(n) for j in range(i, n - 1)]

def side_of_rep(n, i, j):
    """代表弧的 sideA（作为 frozenset），与其余集。"""
    A = frozenset(range(i, j + 1))
    return A, frozenset(range(n)) - A

def kalmanson_holds(n, d):
    """IsCircularDist (f = id) 的两条不等式（对称 d）。"""
    for i, j, k, l in [(a, b, c, e) for a in range(n) for b in range(a, n)
                       for c in range(b, n) for e in range(c, n)]:
        if d[i][j] + d[k][l] > d[i][k] + d[j][l]:
            return False
        if d[i][l] + d[j][k] > d[i][k] + d[j][l]:
            return False
    return True

def phyletic(n, w):
    """由代表弧权重得到的距离（对称、零对角）。"""
    out = [[Fraction(0)] * n for _ in range(n)]
    for (i, j), wij in w.items():
        A, Ac = side_of_rep(n, i, j)
        for x in range(n):
            for y in range(x + 1, n):
                if (x in A) != (y in A):
                    out[x][y] += wij
                    out[y][x] += wij
    return out

def solve_weights(n, d):
    """用 §7 的显式逆矩阵行解出代表弧权重。"""
    def phi(a, b):
        return Fraction(0) if a == b else d[min(a, b)][max(a, b)]

    w = {}
    for (i, j) in reps(n):
        if i == 0 and j == 0:
            v = phi(0, 1) + phi(0, n - 1) - phi(1, n - 1)
        elif i == 0:
            v = phi(n - 1, j) - phi(0, j) - phi(n - 1, j + 1) + phi(0, j + 1)
        else:
            v = phi(i - 1, j) - phi(i, j) - phi(i - 1, j + 1) + phi(i, j + 1)
        w[(i, j)] = v / 2
    return w

def kalmanson_witness(n, i, j):
    """非负性对应的 Kalmanson 四元组（用于报告）。"""
    if i == 0 and j == 0:
        return ("triangle", (0, 0, 1, n - 1))
    if i == 0:
        return ("ineq1", (0, j, j + 1, n - 1))
    return ("ineq2", (i - 1, i, j, j + 1))

def check_generated(n, rng, trials=5):
    """(A) 由随机非负权重生成 → 逆矩阵应精确还原。"""
    for _ in range(trials):
        w0 = {p: Fraction(rng.randint(0, 12), rng.randint(1, 3)) for p in reps(n)}
        d = phyletic(n, w0)
        w = solve_weights(n, d)
        assert w == w0, (n, w, w0)
        assert all(v >= 0 for v in w.values())
        assert phyletic(n, w) == d
    return "n=%d: %d 个代表弧；逆矩阵精确还原随机非负权重（%d 组），且 w ≥ 0" % (
        n, len(reps(n)), trials)

def check_sampled(n, rng, trials=200000, grid=(0, 1, 2, 3), exhaustive_limit=4):
    """(B) **拒绝采样 / 穷尽**：均匀采样对称零对角 `d`（有理网格），
    用 `kalmanson_holds` **筛选**（circular 是筛选出来的结果，不是构造前提），
    只对通过筛选者检验 `w = solve_weights(d)` 的 `w ≥ 0` 与 `phyletic(w) == d`。

    ⇒ 一旦某个通过的 `d` 给出负权重或恒等式不成立，就是**主命题的反例**。
    `n ≤ exhaustive_limit` 时改用**网格全枚举 + 筛选**（比随机更有说服力）。"""
    facts = [(x, y) for (x, y) in pairs(n)]
    def check(d):
        w = solve_weights(n, d)
        assert all(v >= 0 for v in w.values()), (n, d, w)
        assert phyletic(n, w) == d, (n, d, w)

    if n <= exhaustive_limit:
        total = 0
        passed = 0
        vals = range(grid[0], grid[-1] + 1)
        for combo in __import__('itertools').product(vals, repeat=len(facts)):
            d = [[Fraction(0)] * n for _ in range(n)]
            for (x, y), v in zip(facts, combo):
                d[x][y] = d[y][x] = Fraction(v)
            total += 1
            if kalmanson_holds(n, d):
                passed += 1
                check(d)
        return ("n=%d: **网格 {%s} 全枚举 %d 个对称零对角 d，其中 %d 个通过 Kalmanson 筛选"
                "（命中率 %.1f%%），全部通过「w ≥ 0 且 phyleticDist = d」**"
                % (n, ",".join(str(v) for v in vals), total, passed,
                   100.0 * passed / total))

    passed = 0
    tried = 0
    while passed < 40 and tried < trials:
        tried += 1
        d = [[Fraction(0)] * n for _ in range(n)]
        for (x, y) in facts:
            v = Fraction(rng.randint(0, 6), rng.randint(1, 2))
            d[x][y] = d[y][x] = v
        if kalmanson_holds(n, d):
            passed += 1
            check(d)
    assert passed > 0, n
    return ("n=%d: 拒绝采样 %d 次、%d 个通过 Kalmanson 筛选（命中率 %.2f%%），"
            "全部通过「w ≥ 0 且 phyleticDist = d」" % (n, tried, passed, 100.0 * passed / tried))


def check_witness_list(n):
    lines = []
    for (i, j) in reps(n):
        kind, quad = kalmanson_witness(n, i, j)
        lines.append("   弧[%d,%d] ← %s %s" % (i, j, kind, quad))
    return lines

def main():
    print("== W12g-3: circularDistanceRealization（修复形态）n = 3,4,5 核对 ==")
    rng = random.Random(20260212)
    for n in (3, 4, 5):
        print("--", check_generated(n, rng))
        print("--", check_sampled(n, rng))
        print("   非负性对应的 Kalmanson 见证：")
        for line in check_witness_list(n):
            print(line)
    print("OK")

if __name__ == "__main__":
    main()
