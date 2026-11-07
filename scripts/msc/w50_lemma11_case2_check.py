#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W50-A 机械诊断：Atteson Lemma 11 的「逐边系数 ≥ 0 ＋ 系数和」在**小树上全枚举**地核一遍。

背景：`atteson_lemma11_gap_quantitative`（`Phylo/AttesonRadius.lean:919`）的证明要按 Atteson
`:2008–2070` 的选法取 `e* ∈ E − P_{k,l}`（`ℓ_k` 最小）与 `k,l` 侧分支里的一对邻居 `(i,j)`，
然后逐边比较 `c_e := w_e(k,l) − w_e(i,j)`。本脚本检查四件事（**精确有理数**，无浮点）：

  ① 逐边非负：所有真边 `e` 上 `c_e ≥ 0`；
  ② 系数和：`Σ_e c_e ≥ 3(n−4)`（`{i,j} ∩ {k,l} = ∅`）或 `≥ 2(n−3)`（恰交一标签）；
  ③ 情形②（`e ∈ P_{i,k} − P_{k,l}`）的**每一对**是否满足 `hbig : n ≤ 2·ℓ_k(e)`
     —— 这是 `attesonW_sub_nonneg_of_sep_ik`（`AttesonRadius.lean` §20）的唯一外部输入；
  ④ 报表：`ℓ_k(e*)` 是否落在 `[3, n−2]`（W50 派单的风险提示）。

树是随机二叉（内点度 3、无度 2 点，即 `Cladogram` 的形状），叶全标号。

用法： python3 scripts/msc/w50_lemma11_case2_check.py [n_min] [n_max] [trials]
"""
import sys
import random
from fractions import Fraction

random.seed(20261107)


def random_binary_tree(n):
    """返回 (adj, leaves)：二叉（内点度 3）、n 片叶、无度 2 点。"""
    if n < 2:
        raise ValueError('n >= 2')
    adj = {0: {1}, 1: {0}}
    nxt = 2
    for _ in range(n - 2):
        leaves = [v for v in adj if len(adj[v]) == 1]
        x = random.choice(sorted(leaves))
        y = next(iter(adj[x]))
        adj[x] = set()
        adj[y].discard(x)
        m = nxt
        nl = nxt + 1
        nxt += 2
        adj[x].add(m)
        adj[m] = {x, y, nl}
        adj[y].add(m)
        adj[nl] = {m}
    return adj, sorted(v for v in adj if len(adj[v]) == 1)


def comp_without(adj, e, start):
    """删边 e 后 start 所在分量。"""
    a, b = e
    seen = {start}
    stack = [start]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if (v == a and w == b) or (v == b and w == a):
                continue
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return seen


def side_count(adj, e, u, leaves):
    c = comp_without(adj, e, u)
    return sum(1 for x in leaves if x in c)


def bfs_path(adj, s, t):
    par = {s: None}
    stack = [s]
    while stack:
        v = stack.pop()
        if v == t:
            break
        for w in adj[v]:
            if w not in par:
                par[w] = v
                stack.append(w)
    path, v = [], t
    while v is not None:
        path.append(v)
        v = par[v]
    return path[::-1]


def path_edges(path):
    return {(min(path[i], path[i + 1]), max(path[i], path[i + 1])) for i in range(len(path) - 1)}


def main():
    nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 40

    bad = hbig_fail = 0
    bounds_fail = []
    cnt = {'pairs': 0, 'cherries': 0, 'checks': 0, 'case2': 0}

    for n in range(nmin, nmax + 1):
        for _ in range(trials):
            adj, leaves = random_binary_tree(n)
            if len(leaves) != n:
                continue
            dist = {}
            for s in leaves:
                d = {s: 0}
                st = [s]
                while st:
                    v = st.pop()
                    for w in adj[v]:
                        if w not in d:
                            d[w] = d[v] + 1
                            st.append(w)
                for t2 in leaves:
                    dist[(s, t2)] = Fraction(d[t2])
            S = {x: sum(dist[(x, y)] for y in leaves) for x in leaves}
            Q = {(x, y): (n - 2) * dist[(x, y)] - S[x] - S[y] for x in leaves for y in leaves}
            cherry = {(x, y) for x in leaves for y in leaves
                      if x < y and (set(adj[x]) & set(adj[y]))}
            real_edges = {(min(v, w), max(v, w)) for v in adj for w in adj[v]}

            for k in leaves:
                for l in leaves:
                    if k >= l or (k, l) in cherry:
                        continue
                    cnt['pairs'] += 1
                    Pkl = path_edges(bfs_path(adj, k, l))
                    ellk = {e: side_count(adj, e, k, leaves) for e in real_edges}
                    off = [e for e in real_edges if e not in Pkl]
                    if not off:
                        continue
                    estar = min(off, key=lambda e: ellk[e])
                    Cleaves = {x for x in leaves if x in comp_without(adj, estar, k)}
                    if not (k in Cleaves and l in Cleaves):
                        continue
                    cand = [(x, y) for (x, y) in cherry if x in Cleaves and y in Cleaves]
                    if not cand:
                        continue
                    if not (3 <= ellk[estar]):
                        bounds_fail.append((n, k, l, ellk[estar], 'lower'))
                    elif n >= 5 and not (ellk[estar] <= n - 2):
                        bounds_fail.append((n, k, l, ellk[estar], 'upper'))
                    for (i, j) in cand:
                        cnt['cherries'] += 1
                        kind = 3 if ({i, j} & {k, l}) else 2
                        csum = Fraction(0)
                        nonneg = True
                        for e in real_edges:
                            ell = ellk[e]
                            kl_sep = l not in comp_without(adj, e, k)
                            ij_sep = j not in comp_without(adj, e, i)
                            w_kl = Fraction(-2) if kl_sep else Fraction(-2) * (n - ell)
                            elli = side_count(adj, e, i, leaves)
                            w_ij = Fraction(-2) if ij_sep else Fraction(-2) * (n - elli)
                            c = w_kl - w_ij
                            csum += c
                            if c < 0:
                                nonneg = False
                            # 情形②：kl 同侧、ij 同侧、i 与 k 异侧
                            if (not kl_sep) and (not ij_sep) and (k not in comp_without(adj, e, i)):
                                cnt['case2'] += 1
                                if n > 2 * ell:
                                    hbig_fail += 1
                        cnt['checks'] += 1
                        need = Fraction(3 * (n - 4)) if kind == 2 else Fraction(2 * (n - 3))
                        if (not nonneg) or csum < need:
                            bad += 1
                            if bad <= 5:
                                print(f"[FAIL] n={n} (k,l)=({k},{l}) (i,j)=({i},{j}) kind={kind} "
                                      f"csum={csum} need={need} nonneg={nonneg}")

    print('== 计数：', cnt)
    print(f'== ①+② 违反数（逐边非负 与 系数和）= {bad}')
    print(f'== ③ hbig (n ≤ 2·ℓ_k(e)) 反例数 = {hbig_fail}（case2 边总数 {cnt["case2"]}）')
    print(f'== ④ ℓ_k(e*) 越界数 = {len(bounds_fail)}（n ≥ 5 用 [3, n−2]；n = 4 只查下界）')
    if bounds_fail[:5]:
        print('   例：', bounds_fail[:5])


if __name__ == '__main__':
    main()
