#!/usr/bin/env python3
"""W12e13 ★D：`bme_pauplin_identity_gap`（`Phylo/BMELeastSquares.lean:372`）的**语义核查**。

命题 (3)（Pauplin 归一化，DesperGascuel2004 式 (9)，`:2027`）：

    ∀ 边 e,  Σ_{x ∈ plane} bmeCoeff (p x.1 x.2) · S x.1 x.2 e = 2

其中 `plane = univ × univ`（**有序对**，含对角）、`bmeCoeff p = 2·(1/2)^p`、
`S i j e = 1 ⟺ e ∈ P_ij`（`P_ij` = 树上唯一路径）、`p i j = #(P_ij 的边)`（拓扑距离）。

本脚本**穷举**所有 `n` 个标号叶的**无根二叉拓扑**（叶插入法生成 + split 系统去重），
对**每条边**用精确有理数验证：

    (无序版)  Σ_{i<j, e ∈ P_ij} 2^{1−p_ij} = 1
    (有序版)  Σ_{(i,j) ∈ plane, e ∈ P_ij} 2^{1−p_ij} = 2      ← 即命题 (3) 的形式
    (对角)    S i i e = 0 对每条边成立（故对角项贡献 0）

`plane` 上有序对 = 无序对的两倍，故两者等价；同时验证 `S` 的 0/1 性与路径条数
`Σ_e S i j e = p i j`（命题 (2)）在真树上成立（这是「可加性 + 关联计数」的一致性检查）。

只使用标准库 + 精确有理数（`Fraction`），无随机、无浮点。
"""
from fractions import Fraction
from itertools import combinations
import sys


def edges_of(adj):
    out = []
    for u in sorted(adj):
        for v in sorted(adj[u]):
            if u < v:
                out.append((u, v))
    return out


def copy_adj(adj):
    return {u: set(nb) for u, nb in adj.items()}


def split_key(adj, n):
    """去重键：所有边切出的叶集（取两侧中字典序较小者）。"""
    key = []
    for (u, v) in edges_of(adj):
        a = adj[u] - {v}
        seen = {u}
        stack = [u]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if (x == u and y == v) or (x == v and y == u):
                    continue
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        side = frozenset(x for x in seen if x < n)
        other = frozenset(range(n)) - side
        key.append(tuple(min(sorted(side), sorted(other))))
    return tuple(sorted(key))


def gen_trees(nmax):
    """叶插入法枚举 n=3..nmax 的全部标号无根二叉拓扑（按 split 去重），返回 {n: [树]}。"""
    out = {3: [{0: {100}, 1: {100}, 2: {100}, 100: {0, 1, 2}}]}
    trees = out[3]
    for n in range(3, nmax):
        nxt = []
        for adj in trees:
            nid = max(adj) + 1
            for (u, v) in edges_of(adj):
                a = copy_adj(adj)
                a[u].discard(v)
                a[v].discard(u)
                a[nid] = {u, v, n}
                a[u].add(nid)
                a[v].add(nid)
                a[n] = {nid}
                nxt.append(a)
        seen = {}
        for a in nxt:
            seen.setdefault(split_key(a, n + 1), a)
        trees = list(seen.values())
        out[n + 1] = trees
    return out


def side_of(adj, e, start):
    """删掉边 e 后，从 start 出发可达的顶点集。"""
    u, v = e
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if (x == u and y == v) or (x == v and y == u):
                continue
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen


def distances(adj, n):
    """叶间拓扑距离 p[i][j]（BFS，边权 1）。"""
    p = [[0] * n for _ in range(n)]
    for s in range(n):
        dist = {s: 0}
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    stack.append(y)
        for t in range(n):
            p[s][t] = dist[t]
    return p


def dists_from(adj, s):
    """从顶点 s 到各顶点的距离（BFS，边权 1）——「子树倍增和」接口用。"""
    dist = {s: 0}
    stack = [s]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1
                stack.append(y)
    return dist


def main():
    nmax = 6
    trees = gen_trees(nmax)
    total_edges = 0
    bad = 0
    for n in range(3, nmax + 1):
        ts = trees[n]
        for adj in ts:
            p = distances(adj, n)
            for e in edges_of(adj):
                total_edges += 1
                A = frozenset(x for x in side_of(adj, e, e[0]) if x < n)
                B = frozenset(range(n)) - A
                if not A or not B:
                    print("BAD: 边不该切出空侧", e)
                    bad += 1
                    continue
                # 命题 (3) 的有序版
                ordered = Fraction(0)
                unordered = Fraction(0)
                for i in range(n):
                    for j in range(n):
                        if i == j:
                            continue
                        # e ∈ P_ij ⟺ i、j 分属 e 两侧
                        if (i in A) != (j in A):
                            ordered += 2 * Fraction(1, 2) ** p[i][j]
                            if i < j:
                                unordered += 2 * Fraction(1, 2) ** p[i][j]
                if ordered != 2 or unordered != 1:
                    print(f"BAD n={n} edge={e} ordered={ordered} unordered={unordered}")
                    bad += 1
                # (d) 的**子树倍增和**形式：每一侧 Σ_{x ∈ 该侧叶} 2^{−d(端点, x)} = 1
                # （等价于上式：交叉对的和 = 2 · D_A · D_B，而 D_A = D_B = 1。）
                dA = dists_from(adj, e[0])
                dB = dists_from(adj, e[1])
                DA = sum(Fraction(1, 2) ** dA[x] for x in A)
                DB = sum(Fraction(1, 2) ** dB[x] for x in B)
                if DA != 1 or DB != 1:
                    print(f"BAD doubling n={n} edge={e} DA={DA} DB={DB}")
                    bad += 1
                # 命题 (2)：Σ_e S i j e = p i j，且 S i i e = 0
                for i in range(n):
                    for j in range(n):
                        cnt = sum(1 for ee in edges_of(adj)
                                  if (i in frozenset(x for x in side_of(adj, ee, ee[0]) if x < n))
                                  != (j in frozenset(x for x in side_of(adj, ee, ee[0]) if x < n)))
                        if i == j:
                            if cnt != 0:
                                print(f"BAD diag n={n} i={i} cnt={cnt}")
                                bad += 1
                        elif cnt != p[i][j]:
                            print(f"BAD count n={n} i={i} j={j} cnt={cnt} p={p[i][j]}")
                            bad += 1
    per_n = {}
    for n in range(3, nmax + 1):
        per_n[n] = len(trees[n])
    print("树数:", per_n)
    print("边检查总数:", total_edges)
    print("反例数:", bad)
    sys.exit(0 if bad == 0 else 1)


main()
