#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A ★D④：起点分支樱桃**不是** `DisjointPairs` 支的合格证人（精确整数，n = 7）

背景
----
`W50_A_MATH.md` §7.6 的路线是：把 Lemma 11 的证明挂到 `P_{k,l}` 的**起点** `v`（`leaf k`
的邻居）上，按 `v` 的第三条邻边 `s(v,c)` 的**分支侧叶数** `S_c` 分两支：

* ②B `S_c = 1`   ⇒ `c` 是叶，`(k, x)` 是樱桃且与 `(k,l)` **恰交一个标签**
                    ⇒ `SharesOneLabel`，起点边单独给 `2(n−3)`。**已收口**（commit `ad2d58c`）。
* ②A `2 ≤ S_c`   ⇒ 分支内必有樱桃（§22 `cherry_in_component`），与 `(k,l)` **不交**
                    ⇒ 计划：`cherry 附着边 2(n−4)` ＋ `起点边 ≥ n − 4` ⇒ `3(n−4)`。
                    其中「起点边 `≥ n−4`」等价于 `2·S_c ≤ n`。

本脚本用一棵**精确的 n = 7 二叉 Cladogram** 证明：②A 的算术**不成立** ——
分支内樱桃的间隙只有 `2(n−3) = 8`，而 `DisjointPairs` 支要 `3(n−4) = 9`。
（定理本身仍真：同一棵树上 `(l,m)` 是与 `(k,l)` **共享标签**的樱桃，间隙 8 = `2(n−3)`，取等。）

树（全边权 1）
--------------
    内部点 v, u, p, q, z；叶 k, l, m, a, b, d, e
    v: k  z  u        u: v  a  p        p: u  b  q
    q: p  d  e        z: v  l  m
    路径 k → l = k–v–z–l（长 3）；`leaf k` 的邻居是 v，其第三条邻边 s(v,u) 的分支侧
    B_c = {a, b, d, e} ⇒ S_c = 4，而 2·S_c = 8 > n = 7 ⇒ `2·S_c ≤ n` **假**。

用法
----
    python3 scripts/msc/w50_lemma11_branch_witness_refute.py
退出码 0 = 所有断言成立（即反例确证）。
"""

from itertools import combinations

LEAVES = ["k", "l", "m", "a", "b", "d", "e"]
INTERNAL = ["v", "u", "p", "q", "z"]
EDGES = [
    ("k", "v"), ("v", "z"), ("v", "u"), ("u", "a"), ("u", "p"),
    ("p", "b"), ("p", "q"), ("q", "d"), ("q", "e"), ("z", "l"), ("z", "m"),
]
N = len(LEAVES)
KL = ("k", "l")


def build_adj():
    adj = {x: set() for x in LEAVES + INTERNAL}
    for a, b in EDGES:
        assert a in adj and b in adj
        assert b not in adj[a], "重复边"
        adj[a].add(b)
        adj[b].add(a)
    return adj


def check_cladogram(adj):
    """连通、|E| = |V| − 1（无环且连通 ⇒ 树）、无度 2 点、叶 = 标签集、内点度 = 3（二叉）。"""
    nodes = LEAVES + INTERNAL
    assert len(EDGES) == len(nodes) - 1, "边数不等于点数 − 1"
    seen = {"k"}
    stack = ["k"]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    assert seen == set(nodes), "不连通"
    for x in LEAVES:
        assert len(adj[x]) == 1, f"叶 {x} 的度不是 1"
    for x in INTERNAL:
        assert len(adj[x]) == 3, f"内点 {x} 的度不是 3（二叉性）"
    # 叶 = 标签集：内点中不得有度 1 者
    for x in INTERNAL:
        assert len(adj[x]) != 1
    return True


def dists(adj):
    d = {}
    for src in LEAVES:
        dd = {src: 0}
        stack = [src]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in dd:
                    dd[y] = dd[x] + 1
                    stack.append(y)
        d[src] = dd
    assert all(len(d[s]) == len(LEAVES) + len(INTERNAL) for s in LEAVES)
    return d


def cherries(adj):
    """樱桃 = 两片叶共邻居。"""
    out = []
    for x, y in combinations(LEAVES, 2):
        shared = adj[x] & adj[y]
        if shared:
            assert len(shared) == 1
            out.append((x, y, next(iter(shared))))
    return out


def side_leaves(adj, edge, side_vertex):
    """删去 edge 后与 side_vertex 连通的叶数（边的侧叶数）。"""
    a, b = edge
    cnt = 0
    for x in LEAVES:
        dd = {x: 0}
        stack = [x]
        while stack:
            cur = stack.pop()
            for y in adj[cur]:
                if y in dd:
                    continue
                if {cur, y} == {a, b}:
                    continue  # 删去的边
                dd[y] = dd[cur] + 1
                stack.append(y)
        if side_vertex in dd:
            cnt += 1
    return cnt


def q_criterion(d, i, j):
    """NJ 判据 Q(i,j) = (n−2)·d(i,j) − Σ_x d(i,x) − Σ_x d(j,x)，整数。"""
    return (N - 2) * d[i][j] - sum(d[i][x] for x in LEAVES) - sum(d[j][x] for x in LEAVES)


def main():
    adj = build_adj()
    check_cladogram(adj)
    d = dists(adj)
    ch = cherries(adj)
    print(f"n = {N}；樱桃 = {[(x, y, w) for x, y, w in ch]}")

    # ---- 起点几何：leaf k 的邻居 v，第三条邻边 s(v,u)，分支侧 B_c
    v = next(iter(adj["k"]))
    assert v == "v", v
    others = sorted(adj[v] - {"k"})
    assert others == ["u", "z"], others
    z_edge, c_edge = "z", "u"  # z 方向 = 路径方向（叶 l 在 z 一侧）；u 方向 = 分支方向
    S_c = side_leaves(adj, ("v", "u"), "u")
    S_k_start = side_leaves(adj, ("v", "z"), "v")
    print(f"起点 v 的三条邻边：s(k,v) / s(v,z) / s(v,u)；"
          f"分支侧 S_c = {S_c}，起点边 k 侧 S_k = {S_k_start}")
    print(f"2·S_c = {2 * S_c} > n = {N}  ⇒ 『2·S_c ≤ n』为假")

    # 起点边的系数（§19 情形②）：c = 2(n − S_k) − 2
    c_start = 2 * (N - S_k_start) - 2
    print(f"起点边系数 c_e = 2(n − S_k) − 2 = {c_start}；DisjointPairs 支要求 ≥ n − 4 = {N - 4}")
    assert c_start < N - 4, "起点边居然够了"

    # ---- 分支内樱桃：与 (k,l) 不交，需要 3(n−4)
    k, l = KL
    qkl = q_criterion(d, k, l)
    need_disjoint = 3 * (N - 4)
    need_share = 2 * (N - 3)
    print(f"Q(k,l) = {qkl}；DisjointPairs 支需 gap ≥ {need_disjoint}，"
          f"SharesOneLabel 支需 gap ≥ {need_share}")
    disjoint_ok = False
    share_ok = False
    for x, y, w in ch:
        gap = qkl - q_criterion(d, x, y)
        share = bool({x, y} & {k, l})
        ok = (gap >= need_share) if share else (gap >= need_disjoint)
        print(f"  樱桃 ({x},{y})（中心 {w}）：gap = {gap}；"
              f"{'共享标签' if share else '不交'} ⇒ 需 ≥ {need_share if share else need_disjoint}"
              f" ⇒ {'满足' if ok else '不满足'}")
        if share:
            share_ok = share_ok or ok
        else:
            disjoint_ok = disjoint_ok or ok

    # ---- 断言：不交支的证人**不存在**（这就是 ②A 算术为假的机器证据）
    assert not disjoint_ok, "竟然存在满足 3(n−4) 的不交樱桃 —— 反例不成立"
    assert share_ok, "定理本身被推翻了（共享支也不满足）—— 这是更大的发现，需立刻上报"
    print("\n结论：")
    print("  ✗ 分支内（与 (k,l) 不交）的樱桃间隙 = 8 < 9 = 3(n−4) ⇒ ②A 的算术是**假的**。")
    print("  ✓ 定理本身成立，见证是共享标签的樱桃 (l,m)，间隙 8 = 2(n−3)，**取等**。")
    print("  ⇒ §27.6 的几何引理可用，但『分支樱桃 ⇒ 3(n−4)』这条路线必须放弃；")
    print("    `DisjointPairs` 支的证人不能取起点分支内部，须按 Atteson case 1（`:2030–2043`）")
    print("    用 `P_{k,l}` 上的**配对边**＋`e*` 最小性给出的 `ℓ_k(e_{p*}) ≥ n/2`。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
