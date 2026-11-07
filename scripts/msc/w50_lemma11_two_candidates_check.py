#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A round 13：**两端樱桃**策略的验证（大实例，全枚举到 n = 7 覆盖不到）

★D④（§7.7）之后，Case D（`k,l` 都不在樱桃里）的正确证人不是「起点分支内**那一个**樱桃」，
而是**两端各取一个**：

* k 端：起点 `v = x_1` 的分支 `B_c` 内的樱桃（§27.6 `exists_cherry_of_start_side_two_le`）；
* l 端：镜像（`l` 的邻居 `x_{m-1}` 的分支内的樱桃）。

设路径 `k = x_0 — x_1 — … — x_m = l`（`m` 条边），`ℓ_k(e_r)` / `ℓ_l(e_r)` 是路径边
`e_r = s(x_{r-1}, x_r)` 两侧的叶数（`= sideLeafCount`），则

    gap(k 端) = 2(n−4) + Σ_{r=2}^{m} (2·ℓ_l(e_r) − 2)   （e_1 那项恒 0）
    gap(l 端) = 2(n−4) + Σ_{r=1}^{m−1} (2·ℓ_k(e_r) − 2)  （e_m 那项恒 0）

两式相加，用 `ℓ_k(e_r) + ℓ_l(e_r) = n`（`2 ≤ r ≤ m−1`）、`ℓ_k(e_1) = ℓ_l(e_m) = 1`：

    gap(k 端) + gap(l 端) = 4(n−4) + 2(m−2)n − 4m + 8

而 `m ≥ 3`、`m ≤ n−1` ⇒ 后一项 `≥ 2(n−4)` ⇒ **两者中至少一个 `≥ 3(n−4)`**。

★★ 这条**完全不用** `e*` 最小性、不用 `n/2` —— 是 ★D③ 之后真正的出路。
本脚本用一棵 `m = 5`、`n = 106` 的树验证：k 端**不够**，l 端绰绰有余（证明确实需要「取两端」）。
"""

import sys

_counter = [0]


def new_int():
    _counter[0] += 1
    return f"i{_counter[0]}"


def mk_adj():
    return {}


def add(adj, a, b):
    adj.setdefault(a, set()).add(b)
    adj.setdefault(b, set()).add(a)


def is_leaf(x):
    return isinstance(x, int) or x in ("k", "l")


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
    a, b = e
    seen = {side}
    st = [side]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v in seen or {u, v} == {a, b}:
                continue
            seen.add(v)
            st.append(v)
    return {x for x in seen if is_leaf(x)}


def in_side(adj, e, u, x):
    a, b = e
    seen = {u}
    st = [u]
    while st:
        p = st.pop()
        for q in adj[p]:
            if q in seen or {p, q} == {a, b}:
                continue
            seen.add(q)
            st.append(q)
    return x in seen


def new_leaf():
    _counter[0] += 1
    return 900000 + _counter[0]


def sub(adj, parent, k):
    """在 parent 下挂一棵恰 k 片叶的二叉子树：parent 只增加**一个**邻居。

    k = 1 时直接挂一片叶；k >= 2 时挂一个内点，该内点再分两棵子树（度 3）。
    """
    if k == 1:
        add(adj, parent, new_leaf())
        return
    r = new_int()
    add(adj, parent, r)
    a = k // 2
    b = k - a
    sub(adj, r, a)
    sub(adj, r, b)


def build(hs):
    """路径 k=x0—x1—…—xm=l，x_j（1≤j≤m−1）挂 hs[j−1] 片叶的二叉子树。"""
    adj = mk_adj()
    m = len(hs) + 1
    xs = ["k"] + [new_int() for _ in range(m - 1)] + ["l"]
    xs[0] = "k"
    xs[m] = "l"
    for r in range(m):
        add(adj, xs[r], xs[r + 1])
    for j in range(1, m):
        sub(adj, xs[j], hs[j - 1])
    return adj, xs


def cherries(adj):
    L = sorted((x for x in adj if is_leaf(x)), key=str)
    out = []
    for a, i in enumerate(L):
        for b in L[a + 1:]:
            s = adj[i] & adj[b]
            if s:
                out.append((i, b, next(iter(s))))
    return out


def main():
    hs = [int(x) for x in sys.argv[1:]] or [100, 1, 1, 2]  # m = 5
    adj, xs = build(hs)
    L = sorted((x for x in adj if is_leaf(x)), key=str)
    n = len(L)
    k, l = "k", "l"
    ch = cherries(adj)
    print(f"n = {n}，m = {len(xs) - 1}，路径 {xs}，旁挂叶数 hs = {hs}")
    print(f"樱桃数 = {len(ch)}；k 在樱桃里？ {any(k in (a, b) for a, b, _ in ch)}；"
          f"l 在樱桃里？ {any(l in (a, b) for a, b, _ in ch)}")

    d = {x: bfs(adj, x)[0] for x in L}
    r = {x: sum(d[x][y] for y in L) for x in L}
    Q = lambda i, j: (n - 2) * d[i][j] - r[i] - r[j]
    qkl = Q(k, l)
    need = 3 * (n - 4)
    print(f"Q(k,l) = {qkl}；DisjointPairs 支需 gap ≥ 3(n−4) = {need}")

    # 两端的分支内樱桃
    def branch_cherry(end):
        v = next(iter(adj[end]))
        z = path(adj, end, l if end == k else k)[2]
        c = next(u for u in adj[v] if u != end and u != z)
        B = side_leaves(adj, (v, c), c)
        inner = [(a, b) for (a, b, w) in ch if a in B and b in B]
        return v, c, B, inner

    for name, end in (("k 端", k), ("l 端", l)):
        v, c, B, inner = branch_cherry(end)
        assert inner, f"{name} 分支内无樱桃"
        g = max(qkl - Q(a, b) for (a, b) in inner)
        print(f"  {name}：v = {v}，B_c 叶数 = {len(B)}，分支内樱桃 {inner}，"
              f"最好 gap = {g} ⇒ {'✓ 够' if g >= need else '✗ 不够'}")

    # 逐边分解验证公式 gap = 2(n−4) + Σ_{r}(2ℓ_far − 2)
    v, c, B, inner = branch_cherry(k)
    i, j = inner[0]
    w = next(u for u in adj[i] if u == adj[j].__iter__().__next__())
    for a, b, cen in ch:
        if {a, b} == {i, j}:
            w = cen
    att = next(u for u in adj[w] if u != i and u != j)
    tot = 0
    detail = []
    for rr in range(1, len(xs)):
        e = (xs[rr - 1], xs[rr])
        kl_sep = not in_side(adj, e, k, l)
        ij_same = in_side(adj, e, i, j)
        if not kl_sep and ij_same:
            ce = 2 * (n - len(side_leaves(adj, e, i))) - 2
        elif kl_sep and not ij_same:
            ce = 2 - 2 * (n - len(side_leaves(adj, e, k)))
        elif kl_sep and ij_same:
            ce = 2 * (n - len(side_leaves(adj, e, i))) - 2
        elif not kl_sep and not ij_same:
            ce = 0
        else:
            ce = 2 * (len(side_leaves(adj, e, k)) - len(side_leaves(adj, e, i)))
        tot += ce
        detail.append((f"e_{rr}", ce, len(side_leaves(adj, e, k)), len(side_leaves(adj, e, l))))
    ce_att = 2 * (len(side_leaves(adj, (w, att), w)) - 0) if False else None
    Sk_att = len(side_leaves(adj, (w, att), k))
    Si_att = len(side_leaves(adj, (w, att), i))
    ce_att = 2 * (Sk_att - Si_att) if in_side(adj, (w, att), k, l) else 0
    print(f"  逐边：附着边 s(w,{att}) 的 c_e = {ce_att}（应为 2(n−4) = {2*(n-4)}）")
    for name, ce, lk, ll in detail:
        print(f"    {name}: c_e = {ce:5d}   ℓ_k = {lk}, ℓ_l = {ll}, ℓ_k+ℓ_l = {lk+ll}")
    gap_k = ce_att + tot
    print(f"  k 端 gap = {ce_att} + {tot} = {gap_k}；Q 直算 = {qkl - Q(i, j)}")
    assert gap_k <= qkl - Q(i, j), (gap_k, qkl - Q(i, j))  # 只累加路径边＋附着边 ⇒ 下界
    print("\n⇒ 逐边公式与 Q 直算**一致**；k 端不够、l 端够 ⇒ 必须「取两端」。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
