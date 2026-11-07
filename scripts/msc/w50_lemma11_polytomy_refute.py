#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A ★D：`atteson_lemma11_gap_quantitative` 在**多叉**树上被推翻（精确有理数）。

背景
----
`Phylogram`（`Phylo/Core.lean:157`）只要求 `no_degree_two`（无度 2 顶点），
**允许 polytomy**（内点度 ≥ 3 任意）。而 Atteson Lemma 11
（`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md:1989`）
的前提是 “a weighted **binary** tree”；证明里 case 1（`:2034–2043`）显式用到
「每个内点恰关联 3 条边」（“since the tree is binary and every internal node is
incident with three edges”）。

本脚本给出**具体的多叉反例**：双星（double-star）`v1`（度 4）—`v2`（度 4），
两侧各挂 3 片叶，全边权 1，`n = 6`。取 `(k,l)` 为两侧各一片（非樱桃），
则**任何**樱桃 `(i,j)` 的间隙都只有 `4`，而两个分支要求的最小间隙分别是
`3(n−4) = 6`（`DisjointPairs`）与 `2(n−3) = 6`（`SharesOneLabel`）—— 全不满足。

判据逐字对 Lean：
* `NJ.Dissimilarity.IsCherry`（`Phylo/Algorithm/NJ.lean:78`）四点条件式；
* `NJ.Dissimilarity.Q`（`:88`）`= (n−2)δ_ij − S_i − S_j`；
* `DisjointPairs`／`SharesOneLabel`（`AttesonRadius.lean:112/119`）；
* `IsCherrySeparated`（`:132`）的两分支。

用法：`python3 scripts/msc/w50_lemma11_polytomy_refute.py`
"""

from fractions import Fraction as F
from itertools import combinations
from collections import deque

UNIT = F(1)


# ---------------------------------------------------------------- 树构造
def build(path, weights=None):
    """无向树：`path` 为边表（顶点名任意），`weights` 缺省全 1。"""
    adj = {}
    w = {}
    for idx, (u, v) in enumerate(path):
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
        w[frozenset((u, v))] = UNIT if weights is None else F(weights[idx])
    return adj, w


def double_star(m):
    """`v1` 挂 `k,x_1..x_{m-1}` 与 `v2`；`v2` 挂 `l,a_1..a_{m-1}` 与 `v1`。

    内点度 `= m+1`；`m = 2` 即**二叉**（4 叶），`m >= 3` 即多叉（`2m` 叶）。"""
    edges = [("v1", "k"), ("v1", "v2"), ("v2", "l")]
    left = ["k"] + ["x%d" % i for i in range(1, m)]
    right = ["l"] + ["a%d" % i for i in range(1, m)]
    for y in left[1:]:
        edges.append(("v1", y))
    for y in right[1:]:
        edges.append(("v2", y))
    leaves = sorted(left + right)
    return edges, leaves


def dist_table(adj, w, verts):
    """全对加权距离（树：BFS 即精确）。"""
    d = {}
    for s in verts:
        seen = {s: F(0)}
        q = deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in seen:
                    seen[v] = seen[u] + w[frozenset((u, v))]
                    q.append(v)
        d[s] = seen
    return d


# ------------------------------------------------------- Cladogram 公理
def check_cladogram(adj, leaves):
    verts = list(adj)
    ok = True
    # 连通
    seen = {verts[0]}
    q = deque([verts[0]])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                q.append(v)
    if len(seen) != len(verts):
        print("  ✗ 不连通"); ok = False
    # 无环：边数 = 点数 − 1
    nedges = sum(len(a) for a in adj.values()) // 2
    if nedges != len(verts) - 1:
        print("  ✗ 有环（边数 %d ≠ 点 −1）" % nedges); ok = False
    # no_degree_two
    bad2 = [v for v in verts if len(adj[v]) == 2]
    if bad2:
        print("  ✗ 度 2 顶点:", bad2); ok = False
    # 叶（度 1）↔ 标签集
    deg1 = sorted(v for v in verts if len(adj[v]) == 1)
    if deg1 != sorted(leaves):
        print("  ✗ 度 1 顶点 ≠ 标签集:", deg1, leaves); ok = False
    return ok


# ------------------------------------------------------ Lean 侧的判据
def make_metric(adj, w, leaves):
    verts = list(adj)
    d = dist_table(adj, w, verts)
    n = len(leaves)
    S = {x: sum(d[x][y] for y in leaves) for x in leaves}
    Q = {(x, y): F(n - 2) * d[x][y] - S[x] - S[y] for x in leaves for y in leaves}
    dmin = min(w.values())

    def IsCherry(a, b):
        """`NJ.Dissimilarity.IsCherry`：四点条件式（对任意异于 a,b 的 k,l）。"""
        if a == b:
            return False
        others = [z for z in leaves if z != a and z != b]
        for k, l in combinations(others, 2):
            if not (d[a][b] + d[k][l] <= d[a][k] + d[b][l]):
                return False
            if not (d[a][b] + d[k][l] <= d[a][l] + d[b][k]):
                return False
        return True

    return d, dmin, n, S, Q, IsCherry


def DisjointPairs(i, j, k, l):
    return i != k and i != l and j != k and j != l


def SharesOneLabel(i, j, k, l):
    return ((i == k and j != k and j != l) or (i == l and j != k and j != l)
            or (j == k and i != k and i != l) or (j == l and i != k and i != l))


def check_def(leaves, dmin, n, Q, IsCherry):
    """`IsCherrySeparated δ dmin` 逐字：任一 `k ≠ l`、非樱桃 ⇒ 存在樱桃 `(i,j)` 满足一支。"""
    cherries = [(i, j) for i, j in combinations(leaves, 2) if IsCherry(i, j)]
    rows = []
    ok = True
    for k, l in combinations(leaves, 2):
        if IsCherry(k, l):
            continue
        best = None
        for i, j in cherries:
            gap = Q[(k, l)] - Q[(i, j)]
            hits = []
            if DisjointPairs(i, j, k, l):
                hits.append(("Disjoint", 3 * (n - 4) * dmin))
            if SharesOneLabel(i, j, k, l):
                hits.append(("Share1", 2 * (n - 3) * dmin))
            for tag, need in hits:
                if need <= gap:
                    best = (i, j, tag, gap, need)
                    break
            if best:
                break
        if best is None:
            # 记录该 (k,l) 上的**最大**间隙（用以说明差多少）
            top = max(((Q[(k, l)] - Q[(i, j)]), i, j) for i, j in cherries) if cherries else None
            rows.append((k, l, top))
            ok = False
    return ok, cherries, rows


def main():
    print(__doc__)
    for m in (2, 3):
        edges, leaves = double_star(m)
        adj, w = build(edges)
        n = len(leaves)
        print("=" * 72)
        print("双星 m = %d：内点度 = %d，叶 = %s，n = %d，全边权 = 1"
              % (m, m + 1, leaves, n))
        if not check_cladogram(adj, leaves):
            print("  ✗ 不是合法 Cladogram"); continue
        print("  ✓ Cladogram 公理全过（连通、无环、无度 2 点、叶 = 标签集）")
        d, dmin, n, S, Q, IsCherry = make_metric(adj, w, leaves)
        print("  minEdgeWeight = %s > 0" % dmin)
        print("  d(k,l) = %s，S_k = %s，S_l = %s，Q(k,l) = %s"
              % (d["k"]["l"], S["k"], S["l"], Q[("k", "l")]))
        ok, cherries, rows = check_def(leaves, dmin, n, Q, IsCherry)
        print("  樱桃（%d 个）：%s" % (len(cherries), cherries))
        print("  各樱桃的间隙 Q(k,l) − Q(i,j)：%s"
              % [(ij, Q[("k", "l")] - Q[ij]) for ij in cherries])
        print("  两支要求：DisjointPairs ≥ %s，SharesOneLabel ≥ %s"
              % (3 * (n - 4) * dmin, 2 * (n - 3) * dmin))
        if ok:
            print("  ✓ IsCherrySeparated 成立（本 m 不是反例）")
        else:
            print("  ✗✗ IsCherrySeparated **不成立**（反例）：")
            for k, l, top in rows:
                print("     (k,l) = (%s,%s) 非樱桃；最大间隙 = %s（樱桃 %s,%s），远小于要求"
                      % (k, l, top[0], top[1], top[2]))
    print("=" * 72)
    print("结论：m = 2（二叉，n = 4）与 m = 3（多叉，n = 6）的差别就是**内点度**。")
    print("      多叉时 `2(n−3) = 3(n−4) = 6`，而实际最大间隙只有 4 ⇒ 缺口定义被推翻。")
    print("      ⇒ 定量版必须带 `T.toCladogram.IsBinary`（Atteson 原文 `:1989` 的 “binary tree”）。")


if __name__ == "__main__":
    main()
