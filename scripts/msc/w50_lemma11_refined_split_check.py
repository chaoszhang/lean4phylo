#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A round 13：**精化分类**的机器核验（全枚举，n ≤ 7）

★ 背景（`W50_A_MATH.md` §7.7 ★D④）：上一轮「按起点第三邻边分支侧叶数 `S_c` 分两支」的
算术被 n = 7 反例推翻。本脚本检验**精化后的分类**（按「`k` 或 `l` 是否在樱桃里」分）：

* **Case S**：`k`（或 `l`）在樱桃里 ⇒ 取 `(k, x)` 为证人，断言间隙 `≥ 2(n−3)`，
  且 `SharesOneLabel k x k l` 成立。这条在 Lean 里已按**起点几何**收口（`ad2d58c`）：
  `k` 在樱桃里 ⟺ 起点 `v` 的第三邻边通向樱桃的另一片叶 ⟺ `S_c = 1`。
* **Case D**：`k`、`l` 都**不在**任何樱桃里 ⇒ 取**起点分支 `B_c` 内**的樱桃（§27.6 的
  `exists_cherry_of_start_side_two_le`），断言间隙 `≥ 3(n−4)`（`DisjointPairs` 支）。
  ★ 这一支正是 ★D④ 反例**不覆盖**的（那个反例里 `l` 在樱桃 `(l,m)` 里）。

若两支在全枚举下都成立，则 `DisjointPairs` 支的正确证人 = **起点分支内的樱桃**，
但**只在 `k,l` 都不在樱桃里时**才允许这么取 —— 这就是 ★D④ 之后该走的路。

用法：`python3 scripts/msc/w50_lemma11_refined_split_check.py [n]`
退出码 0 = 所有检查通过。
"""

import sys
from itertools import combinations

_counter = [0]


def _new_internal():
    _counter[0] += 1
    return f"i{_counter[0]}"


def trees(n):
    """所有 n 片叶（带标签 0..n−1）的无根二叉树的邻接表（每个同构类恰一个）。"""
    if n == 3:
        h = _new_internal()
        return [{0: {h}, 1: {h}, 2: {h}, h: {0, 1, 2}}]
    out = []
    for adj in trees(n - 1):
        edges = [(a, b) for a in adj for b in adj[a] if str(a) < str(b)]
        for (a, b) in edges:
            h = _new_internal()
            nd = {k: set(v) for k, v in adj.items()}
            nd[a].discard(b)
            nd[b].discard(a)
            nd[a].add(h)
            nd[b].add(h)
            nd[h] = {a, b, n - 1}
            nd[n - 1] = {h}
            out.append(nd)
    return out


def is_leaf(x):
    return isinstance(x, int)


def leaves_of(adj):
    return sorted(x for x in adj if is_leaf(x))


def check_binary(adj, n):
    assert len(adj) == 2 * n - 2, (len(adj), 2 * n - 2)  # |V| = 2n−2
    for x, nb in adj.items():
        assert len(nb) == (1 if is_leaf(x) else 3), (x, nb)
    # 连通
    seen = {0}
    st = [0]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                st.append(v)
    assert len(seen) == len(adj)


def bfs(adj, src):
    d = {src: 0}
    par = {src: None}
    st = [src]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in d:
                d[v] = d[u] + 1
                par[v] = u
                st.append(v)
    return d, par


def path(adj, a, b):
    _, par = bfs(adj, a)
    out = [b]
    while out[-1] != a:
        out.append(par[out[-1]])
    return list(reversed(out))


def side_leaves(adj, e, side):
    """删去边 e 后与 side 连通的叶集。"""
    a, b = e
    seen = {side}
    st = [side]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v in seen:
                continue
            if {u, v} == {a, b}:
                continue
            seen.add(v)
            st.append(v)
    return {x for x in seen if is_leaf(x)}


def cherries(adj, L):
    out = []
    for x, y in combinations(L, 2):
        s = adj[x] & adj[y]
        if s:
            out.append((x, y, next(iter(s))))
    return out


def qmat(adj, L):
    d = {x: bfs(adj, x)[0] for x in L}
    r = {x: sum(d[x][y] for y in L) for x in L}
    return lambda i, j: (len(L) - 2) * d[i][j] - r[i] - r[j]


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    TS = trees(n)
    L = list(range(n))
    nS = nD = 0
    badS, badD = [], []
    for adj in TS:
        check_binary(adj, n)
        ch = cherries(adj, L)
        chset = {x: (y, w) for (x, y, w) in ch}
        chset.update({y: (x, w) for (x, y, w) in ch})
        Q = qmat(adj, L)
        for k, l in combinations(L, 2):
            # 非樱桃对才有意义
            if l in chset.get(k, ()):
                continue
            if adj[k] & adj[l]:
                continue
            qkl = Q(k, l)

            def gap(i, j):
                return qkl - Q(i, j)

            if k in chset or l in chset:
                nS += 1
                a = k if k in chset else l
                x = chset[a][0]
                need = 2 * (n - 3)
                g = gap(a, x)
                if g < need:
                    badS.append((adj, k, l, a, x, g, need))
            else:
                nD += 1
                # 起点：leaf k 的邻居 v；路径方向 z；第三邻边通向 c
                v = next(iter(adj[k]))
                p = path(adj, k, l)
                z = p[2]  # p = [k, v, …] ⇒ 路径方向是 p[2]
                c = next(u for u in adj[v] if u != k and u != z)
                Bc = side_leaves(adj, (v, c), c)
                # 起点分支内的樱桃：两片叶都落在 Bc 里
                inner = [(x, y) for (x, y, w) in ch if x in Bc and y in Bc]
                assert inner, "起点分支内居然没有樱桃（与 §27.6 矛盾）"
                need = 3 * (n - 4)
                best = max(gap(x, y) for (x, y) in inner)
                if best < need:
                    badD.append((adj, k, l, sorted(Bc), inner, best, need))

    print(f"n = {n}：二叉树 {len(TS)} 棵；Case S（k 或 l 在樱桃里）= {nS} 个对，"
          f"Case D（都不在）= {nD} 个对")
    if badS:
        print(f"  ✗ Case S 反例 {len(badS)} 个；首例：k,l = {badS[0][1]},{badS[0][2]}，"
              f"证人 ({badS[0][3]},{badS[0][4]}) gap = {badS[0][5]} < {badS[0][6]}")
    else:
        print("  ✓ Case S：`(k,x)` / `(l,x)` 的间隙恒 ≥ 2(n−3)")
    if badD:
        print(f"  ✗ Case D 反例 {len(badD)} 个；首例：k,l = {badD[0][1]},{badD[0][2]}，"
              f"B_c = {badD[0][3]}，分支内樱桃 {badD[0][4]}，最好的 gap = {badD[0][5]} < {badD[0][6]}")
    else:
        print("  ✓ Case D：起点分支内樱桃的间隙恒 ≥ 3(n−4)")
    return 0 if (not badS and not badD) else 1


if __name__ == "__main__":
    raise SystemExit(main())
