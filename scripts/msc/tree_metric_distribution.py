#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/tree_metric_distribution.py —— W11h / X8 + Q2-① 的独立穷举复核

**纯标准库、精确整数/有理数、无 Monte Carlo。** 目的：在相信 Lean 之前，
先把「随机树下 RF 距离 / quartet 距离的**精确分布**」从**树的完全穷举**里算出来。

文献：
* Steel & Penny 1993, *Syst. Biol.* 42(2):126-141
  （=`references/md/SteelPenny1993_DistributionsTreeComparisonMetrics.md`）
  - 第 293 行 Eq.(4)：    d_p(T1,T2) = i(T1) + i(T2) - 2 v_p(T1,T2)
  - 第 316 行：           partition metric 的直径 = 2n - 6
  - 第 325-331 行：       对**任意** label-invariant D，μ_D(d_p) = 2[μ_D(i) - μ_D(v_p)]
  - 第 456-458 行：       两棵不同 n 叶树的最小 d_q = n - 3
  - 第 486-490 行 (Eq.11)：label-invariant binary 分布下 μ_D(d_q)/C(n,4) = 2/3
* Alon, Naves & Sudakov 2016, *On the maximum quartet distance between phylogenetic trees*
  - 第 124-131 行：qd(T1,T2) = C(n,4) - #{两个树都相容的 quartet}
  - 第 341-345 行 Prop 2.2：随机重标号下，任意 quartet 集 Q 的期望满足数 = |Q|/3
  - 第 347-353 行 Prop 2.3：两棵均匀随机树的 E[qd] = (2/3)·C(n,4)
  - 第 199 行 Thm 1.1：max qd <= (0.69+o(1))·C(n,4)；第 12 行 Bandelt-Dress 猜想 2/3

自检（本脚本自己先证明自己）：穷举得到的**无根 binary 树棵数**必须等于 (2n-5)!!。
"""
import sys
from itertools import combinations
from fractions import Fraction

FAIL = []


def check(name, got, want):
    ok = (got == want)
    print(f"  [{'OK ' if ok else 'FAIL'}] {name}: got={got} want={want}")
    if not ok:
        FAIL.append(name)
    return ok


# ---------------------------------------------------------------- 树的穷举
# 无根 binary 树用**嵌套 tuple** 表示（degree-2 的根 = 被抑制的内部边两侧）。
# 叶 = 标签 (int)，内部结点 = (左, 右)。n=3 起：((1,2),3)。
def leaves(t):
    if not isinstance(t, tuple):
        return {t}
    return leaves(t[0]) | leaves(t[1])


def nodes(t):
    """t 的**全部真子树**（含叶）—— 即「可插入新叶」的结点（不含根）。"""
    if not isinstance(t, tuple):
        return [t]
    return [t[0], t[1]] + nodes(t[0]) + nodes(t[1])


def insert_leaf(t, target, new):
    if t == target:
        return (t, new)
    if not isinstance(t, tuple):
        return t
    return (insert_leaf(t[0], target, new), insert_leaf(t[1], target, new))


def canonical(t):
    if not isinstance(t, tuple):
        return t
    a, b = canonical(t[0]), canonical(t[1])
    return (a, b) if repr(a) <= repr(b) else (b, a)


def edge_splits(t):
    """无根 binary 树的**非平凡 split** 集。

    规范化：每个 split 表示成「不含最小叶的那一侧」的 frozenset —— 唯一代表元。
    于是 RF 距离（两棵树的非平凡 split 之对称差）就是两个 frozenset 的对称差大小。
    """
    allv = leaves(t)
    mn = min(allv)
    out = set()
    for sub in nodes(t):
        A = leaves(sub)
        B = allv - A
        if len(A) == 1 or len(B) == 1:
            continue
        out.add(frozenset(A if mn not in A else B))
    return frozenset(out)


def gen_trees(n):
    """穷举 n 叶无根 binary 树：从 n=3 起，把新叶插到每条边上，按 split 集去重。"""
    trees = {edge_splits(((1, 2), 3)): ((1, 2), 3)}
    for k in range(4, n + 1):
        nxt = {}
        for t in trees.values():
            for target in nodes(t):
                nt = canonical(insert_leaf(t, target, k))
                nxt[edge_splits(nt)] = nt
        trees = nxt
    return sorted(trees.items(), key=lambda kv: repr(kv[1]))


def double_factorial(m):
    r = 1
    for i in range(1, m + 1, 2):
        r *= i
    return r


# ---------------------------------------------------------------- 距离
def to_graph(t):
    """嵌套 tuple -> 邻接表；返回 (adj, leaf2node)。"""
    adj = {}
    cnt = [0]

    def new():
        cnt[0] += 1
        adj[cnt[0]] = []
        return cnt[0]

    lab = {}

    def build(x):
        if not isinstance(x, tuple):
            nid = new()
            lab[x] = nid
            return nid
        nid = new()
        for ch in x:
            cid = build(ch)
            adj[nid].append(cid)
            adj[cid].append(nid)
        return nid

    build(t)
    return adj, lab


def pairwise_dist(t):
    adj, lab = to_graph(t)
    out = {}
    for a, sa in lab.items():
        d = {sa: 0}
        stack = [sa]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in d:
                    d[v] = d[u] + 1
                    stack.append(v)
        out[a] = {b: d[sb] for b, sb in lab.items()}
    return out


def quartet_topo(dist, a, b, c, d):
    """4-子集 {a,b,c,d} 在树上的 pairing（单位边长下用距离比较判定）。"""
    if dist[a][b] + dist[c][d] < dist[a][c] + dist[b][d]:
        return frozenset([frozenset([a, b]), frozenset([c, d])])
    if dist[a][c] + dist[b][d] < dist[a][d] + dist[b][c]:
        return frozenset([frozenset([a, c]), frozenset([b, d])])
    return frozenset([frozenset([a, d]), frozenset([b, c])])


def main():
    print("=" * 78)
    print("W11h / X8 + Q2-① —— 树比较度量的精确分布（穷举，非 Monte Carlo）")
    print("=" * 78)

    NS = [4, 5, 6, 7]
    data = {}
    for n in NS:
        trees = gen_trees(n)
        print(f"\n--- n = {n}：穷举 binary 树 {len(trees)} 棵 ---")
        check(f"n={n} 无根 binary 树棵数 = (2n-5)!!", len(trees), double_factorial(2 * n - 5))

        splits = [s for s, _ in trees]
        dists = [pairwise_dist(t) for _, t in trees]
        m = len(trees)

        # ---- RF 距离（非平凡 split 的对称差）
        rfd = {}
        for i in range(m):
            for j in range(m):
                rfd[(i, j)] = len(splits[i] ^ splits[j])
        mean = Fraction(sum(rfd.values()), m * m)
        var = Fraction(sum(v * v for v in rfd.values()), m * m) - mean * mean

        # Steel-Penny Eq.(4)：μ = 2[μ(i) - μ(v_p)]
        internal = sum(len(s) for s in splits)
        shared = sum(len(splits[i] & splits[j]) for i in range(m) for j in range(m))
        mu_i = Fraction(internal, m)
        mu_v = Fraction(shared, m * m)
        check(f"n={n} 每棵树内部边数 = n-3 = {n-3}", all(len(s) == n - 3 for s in splits), True)
        check(f"n={n} RF 均值 = 2[μ(i)-μ(v_p)]", mean, 2 * (mu_i - mu_v))
        check(f"n={n} RF 直径 <= 2n-6", max(rfd.values()) <= 2 * n - 6, True)
        prof = {}
        for v in rfd.values():
            prof[v] = prof.get(v, 0) + 1
        print(f"  RF 分布 (距离: 有序对数) = {dict(sorted(prof.items()))}")
        print(f"  RF mean = {mean} = {float(mean):.6f}   var = {var} = {float(var):.6f}")
        print(f"  RF μ(i) = {mu_i},  μ(v_p) = {mu_v},  2(μi-μv) = {2*(mu_i-mu_v)}")

        # ---- quartet 距离（Alon 定义：resolved pairing 不同的 4-子集个数）
        quads = list(combinations(range(1, n + 1), 4))
        C4 = len(quads)
        qsets = [{q: quartet_topo(d, *q) for q in quads} for d in dists]
        qd = {}
        for i in range(m):
            for j in range(m):
                qd[(i, j)] = sum(1 for q in quads if qsets[i][q] != qsets[j][q])
        qmean = Fraction(sum(qd.values()), m * m)
        qvar = Fraction(sum(v * v for v in qd.values()), m * m) - qmean * qmean
        check(f"n={n} E[qd] = (2/3)C(n,4)", qmean, Fraction(2 * C4, 3))
        check(f"n={n} 最小 qd（不同树）= n-3（Steel-Penny 456 行）",
              min(v for (i, j), v in qd.items() if i != j), n - 3)
        qprof = {}
        for v in qd.values():
            qprof[v] = qprof.get(v, 0) + 1
        print(f"  qd 分布 = {dict(sorted(qprof.items()))}")
        print(f"  qd mean = {qmean} = {float(qmean):.6f}   var = {qvar} = {float(qvar):.6f}")
        print(f"  qd: min(不同树) = {min(v for (i,j),v in qd.items() if i!=j)}, "
              f"max = {max(qd.values())}, C(n,4) = {C4}, "
              f"归一化 max = {Fraction(max(qd.values()), C4)}")
        # Bandelt-Dress：n >= 6 时 max qd <= (14/15)C(n,4)（Alon 等第 137-141 行原文限定 n >= 6）
        if n >= 6:
            check(f"n={n} Bandelt-Dress 上界 max qd <= (14/15)C(n,4)",
                  max(qd.values()) <= Fraction(14 * C4, 15), True)
            check(f"n={n} Bandelt-Dress 上界是否取等（n=6 时 14 = (14/15)·15）",
                  max(qd.values()) == Fraction(14 * C4, 15), n == 6)
        else:
            print(f"  (n={n} < 6：Bandelt-Dress 上界不适用 —— 原文限定 n >= 6；"
                  f"此处 max qd = {max(qd.values())} > (14/15)C(n,4) = {Fraction(14 * C4, 15)})")

        data[n] = dict(m=m, rfd=rfd, qd=qd, splits=splits, qsets=qsets, quads=quads)

    # ---- ★B 反例检查
    print("\n" + "=" * 78)
    print("★B 反例检查")
    print("=" * 78)
    print("(1) 三角不等式对**任意** Finset 成立吗？—— 成立。Phylo/Distance.lean 的")
    print("    symmDiffCard_triangle 对任意 [DecidableEq β] 与任意 S R T 已证，无集合假设。")
    print("(2) 「quartet 距离 <= RF 距离」在真实树上成立吗？—— **不成立**：")
    for n in NS:
        d = data[n]
        print(f"    n={n}: max RF = {max(d['rfd'].values())} (<= 2n-6 = {2*n-6}), "
              f"max qd = {max(d['qd'].values())}")
    n = 6
    d = data[n]
    mx = max(d['qd'].values())
    pair = [k for k, v in d['qd'].items() if v == mx][0]
    i, j = pair
    print(f"    n=6 具体反例：树#{i} vs 树#{j}: qd = {mx} > max RF = {max(d['rfd'].values())}"
          f"，同一对 RF = {d['rfd'][pair]}")
    print(f"    树#{i} 的 split 集 = {sorted(map(sorted, d['splits'][i]))}")
    print(f"    树#{j} 的 split 集 = {sorted(map(sorted, d['splits'][j]))}")
    print("    => 「quartet 距离 <= RF 距离」**不能**写成一般定理；")
    print("       可证的只是「共用同一个 symmDiffCard 骨架 + 各自基数上界」。")

    # ---- n=4 的最小具体例子（Lean 里也要端到端算一遍）
    print("\n" + "=" * 78)
    print("★C 最小具体例子 n = 4（3 棵 binary 树）")
    print("=" * 78)
    d = data[4]
    print(f"  3 棵树的 split 集 = {sorted(map(lambda s: sorted(map(sorted, s)), d['splits']))}")
    prof = {}
    for v in d['rfd'].values():
        prof[v] = prof.get(v, 0) + 1
    print(f"  RF 分布 = {dict(sorted(prof.items()))}  (有序对共 9)")
    print(f"  μ(i) = {Fraction(3,3)} = 1,  μ(v_p) = {Fraction(3,9)} = 1/3,"
          f"  μ(d_p) = 2(1-1/3) = {2*(Fraction(1)-Fraction(1,3))} = 4/3")
    print(f"  方差 = {Fraction(sum(v*v for v in d['rfd'].values()), 9) - Fraction(4,3)**2} = 8/9")
    qprof = {}
    for v in d['qd'].values():
        qprof[v] = qprof.get(v, 0) + 1
    print(f"  qd 分布 = {dict(sorted(qprof.items()))}，max qd = {max(d['qd'].values())}"
          f"（= 1 组「不同 resolution」，即 |对称差| = 2）")

    # ---- ★D 分布无关性：Alon 等 Prop 2.2/2.3 的**原 setting**（固定树 + 随机重标号）
    print("\n" + "=" * 78)
    print("★D 分布无关性（Alon-Naves-Sudakov 2016 Prop 2.2 第 341-345 行 / Prop 2.3 第 347-353 行）")
    print("=" * 78)
    print("setting：固定一棵 n 叶 binary 树 T，两棵树都取 T 的**均匀随机重标号** σ ∈ S_n。")
    print("Prop 2.2 的引擎 =「每个 4-子集的 6 个配对**小侧**在 𝒯 = {σ·T} 中出现次数相同」。")
    print("本段直接穷举 σ ∈ S_n 验证：纤维次数、Σ_{r,r'} qdFull = 48·k²·C(n,4)")
    print("（这正是 Lean 里 quartetMeanEquidistributed_gap 的常数），以及 E[qd] = (2/3)C(n,4)。")
    from itertools import permutations as _perms
    for n in (4, 5, 6):
        t0 = data[n]['qsets'][0]              # 树 #0 的 quartet pairing（键 = 4-子集的 tuple）
        quads = list(combinations(range(1, n + 1), 4))
        A_of = {frozenset(q): q for q in quads}
        # 固定表：每个 4-子集取「含最小叶的那一侧」作为小侧
        base = {}
        for q in quads:
            sides = list(t0[q])
            base[frozenset(q)] = sides[0] if min(q) in sides[0] else sides[1]
        # σ 的作用：A ↦ σ(A)、B ↦ σ(B)
        orbit = []
        for p in _perms(range(1, n + 1)):
            sigma = {i + 1: p[i] for i in range(n)}
            orbit.append({frozenset(sigma[x] for x in A): frozenset(sigma[x] for x in B)
                          for A, B in base.items()})
        # 自检 1：轨道（去重后）大小整除 n!（标号表的稳定化子有限）
        dedup = {tuple(sorted((tuple(sorted(A)), tuple(sorted(B))) for A, B in t.items()))
                 for t in orbit}
        check(f"n={n} 去重轨道大小 | n!", len(list(_perms(range(1, n + 1)))) % len(dedup), 0)
        # 小侧索引化（每个 4-子集 6 个小侧；互补关系）
        idx = []
        comp = []
        for q in quads:
            qs = frozenset(q)
            sides = []
            for pair in combinations(sorted(qs), 2):
                sides.append(frozenset(pair))
            pos = {B: i for i, B in enumerate(sides)}
            assert len(sides) == 6
            idx.append(pos)
            comp.append([pos[frozenset(qs - B)] for B in sides])
        tables = []
        for t in orbit:
            tables.append(tuple(idx[j][t[frozenset(quads[j])]] for j in range(len(quads))))
        N4 = len(quads)
        # 自检 2：纤维次数之和 = |𝒯|·N4，且每个 (A, B) 的纤维次数相同（= k = |𝒯|/6）
        cnt = {}
        for t in tables:
            for j in range(N4):
                cnt[(j, t[j])] = cnt.get((j, t[j]), 0) + 1
        ks = set(cnt.values())
        check(f"n={n} 纤维次数之和 = |𝒯|·C(n,4)", sum(cnt.values()), len(tables) * N4)
        check(f"n={n} 每个 4-子集的每个小侧出现次数相同（等分布 ⇔ Prop 2.2 的引擎）",
              len(ks) == 1, True)
        k = ks.pop() if len(ks) == 1 else None
        if k is not None:
            check(f"n={n} 纤维次数 k = |𝒯|/6（= n!/6，用全部重标号）", k, len(tables) // 6)
            # Σ_{r,r'} qdFull
            tot = 0
            for t1 in tables:
                for t2 in tables:
                    for j in range(N4):
                        x, y = t1[j], t2[j]
                        if not (x == y or x == comp[j][y]):
                            tot += 2
            check(f"n={n} Σ qdFull = 48·k²·C(n,4)", tot, 48 * k * k * N4)
            check(f"n={n} E[qd] = Σ/(2·|𝒯|²) = (2/3)C(n,4)",
                  Fraction(tot, 2 * len(tables) ** 2), Fraction(2 * N4, 3))
            print(f"  |𝒯| = {len(tables)}, k = {k}, Σ qdFull = {tot}, "
                  f"E[qd] = {Fraction(tot, 2*len(tables)**2)}")

    print("\n" + "=" * 78)
    if FAIL:
        print(f"VERDICT: FAIL —— {len(FAIL)} 项不符：{FAIL}")
        return 1
    print("VERDICT: PASS —— 全部穷举自检与文献公式对齐")
    return 0


if __name__ == "__main__":
    sys.exit(main())
