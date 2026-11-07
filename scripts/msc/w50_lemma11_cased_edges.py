#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A round 13：Case D 的**逐边分解**诊断 —— 找出 `3(n−4)` 到底由哪些边承担

给定一棵二叉树的 Case D 实例（`k,l` 都不在任何樱桃里），取起点分支 `B_c` 内的樱桃
`(i,j)`（中心 `w`），打印每条边的 `c_e = w_e(k,l) − w_e(i,j)` 与端点，按 `c_e` 降序。
目标：看出 `3(n−4)` 是由「附着边 `2(n−4)` ＋ 哪一类边给的 `n−4`」组成。
"""

import sys
from itertools import combinations

_counter = [0]


def _new_internal():
    _counter[0] += 1
    return f"i{_counter[0]}"


def trees(n):
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
    """inSide e u x：删去 e 后 u、x 是否连通。"""
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


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    want = int(sys.argv[2]) if len(sys.argv) > 2 else 1  # 第几个 Case D 实例
    mins = int(sys.argv[3]) if len(sys.argv) > 3 else 0  # 只要 |B_c| ≥ mins 的实例
    L = list(range(n))
    seen_D = 0
    for adj in trees(n):
        ch = []
        for x, y in combinations(L, 2):
            s = adj[x] & adj[y]
            if s:
                ch.append((x, y, next(iter(s))))
        chset = {}
        for (x, y, w) in ch:
            chset.setdefault(x, (y, w))
            chset.setdefault(y, (x, w))
        for k, l in combinations(L, 2):
            if adj[k] & adj[l] or k in chset or l in chset:
                continue
            seen_D += 1
            if seen_D != want:
                continue
            v = next(iter(adj[k]))
            p = path(adj, k, l)
            z = p[2]  # p = [k, v, …] ⇒ 路径方向是 p[2]
            c = next(u for u in adj[v] if u != k and u != z)
            Bc = side_leaves(adj, (v, c), c)
            if len(Bc) < mins:
                continue
            inner = [(x, y) for (x, y, w) in ch if x in Bc and y in Bc]
            i, j = inner[0]
            w = chset[i][1]
            u_att = next(u2 for u2 in adj[w] if u2 != i and u2 != j)
            print(f"n = {n}，Case D 实例 #{want}（k = {k}, l = {l}）")
            print(f"  P_(k,l) = {[str(t) for t in p]}")
            print(f"  起点 v = {v}，第三邻边 s(v,{c})，B_c = {sorted(Bc)}")
            print(f"  樱桃 (i,j) = ({i},{j})，中心 w = {w}，附着边 s(w,{u_att})")
            print(f"  需要 gap ≥ 3(n−4) = {3*(n-4)}")
            rows = []
            for a in adj:
                for b in adj[a]:
                    if str(a) < str(b):
                        e = (a, b)
                        kl = in_side(adj, e, k, l)
                        ij = in_side(adj, e, i, j)
                        a_, b_ = a, b
                        if kl:
                            Sk = len(side_leaves(adj, e, a_))
                        else:
                            Sk = None
                        if ij:
                            Si = len(side_leaves(adj, e, a_)) if kl else None
                        # c_e 按 §19 四情形（a 侧为准）
                        if not kl and not ij:
                            ce = 0
                        elif not kl and ij:
                            ce = 2 * (n - len(side_leaves(adj, e, i))) - 2
                        elif kl and not ij:
                            ce = 2 - 2 * (n - len(side_leaves(adj, e, k)))
                        else:
                            ce = 2 * (len(side_leaves(adj, e, k)) - len(side_leaves(adj, e, i)))
                        rows.append((ce, a, b, kl, ij))
            rows.sort(key=lambda r: -r[0])
            tot = 0
            for ce, a, b, kl, ij in rows:
                tot += ce
                mark = "  ← 附着边" if {a, b} == {w, u_att} else ""
                print(f"    c_e = {ce:4d}  s({a},{b})   [k,l {'同侧' if kl else '分离'}, "
                      f"i,j {'同侧' if ij else '分离'}]{mark}")
            print(f"  合计 Σ c_e = {tot}")
            raise SystemExit(0)
    print("没有找到 Case D 实例")


if __name__ == "__main__":
    main()
