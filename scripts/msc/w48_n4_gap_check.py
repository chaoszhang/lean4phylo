#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W48-A · `atteson_lemma11_gap_quantitative` 的 n=4 反空转机械检查.

命题（`Phylo/AttesonRadius.lean:919`）:
    atteson_lemma11_gap_quantitative T : 4 <= |X| ->
        (toDissimilarity T).IsCherrySeparated (minEdgeWeight T)
其中 `minEdgeWeight T = sInf (Set.range T.w)`，对有限树即 min_e w(e)；
`IsCherrySeparated δ δmin`（同文件 :132）:
    forall k l, k != l -> not (δ.IsCherry k l) ->
      exists i j, δ.IsCherry i j and
        (DisjointPairs i j k l   and 3*(n-4)*δmin <= Q k l - Q i j) or
        (SharesOneLabel i j k l  and 2*(n-3)*δmin <= Q k l - Q i j)

本脚本用**精确有理数**在具体二叉树上核三件事：
  (1) n = 4 时 `DisjointPairs` 分支是否**可被占据**（两对不交在 n=4 上是否可能）；
  (2) 「Q 差恒为 0」这类退化解能否满足命题（= 命题在 n=4 上是否被平凡化）；
  (3) 两条分支上的**最小松弛量**（slack = 左边 - 右边），用来判断命题紧不紧。
用法：python3 scripts/msc/w48_n4_gap_check.py
"""
from fractions import Fraction as F
from itertools import combinations

def tree_metric(n, pendant, internal):
    """固定拓扑：n=4 -> ((a,b),(c,d)) 两樱桃中间接内部边; n=5 -> ((a,b),(c,(d,e)))."""
    if n == 4:
        a, b, c, d = pendant
        L, = internal
        return {('a','b'): a+b, ('c','d'): c+d, ('a','c'): a+L+c, ('a','d'): a+L+d,
                ('b','c'): b+L+c, ('b','d'): b+L+d}
    if n == 5:
        a, b, c, d, e = pendant
        L1, L2 = internal          # ((a,b), (c,(d,e))) 的两条内部边
        m = {}
        def s(x, y): m[frozenset((x, y))] = None
        # 距离：a,b 经 L1 到 x；c 经 L1 到 x；d,e 经 L2 到 c
        def dist(x, y):
            pos = {'a': (0, 0), 'b': (0, 0), 'c': (1, 0), 'd': (2, 1), 'e': (2, 1)}
            pw = {'a': a, 'b': b, 'c': c, 'd': d, 'e': e}
            px, py = pos[x], pos[y]
            # 树上路径：沿 (depth1, depth2) 的最深公共前缀
            if px == py:
                return F(0)
            if px[0] == py[0] == 0:
                return a + b
            if px[0] == py[0] == 2:
                return d + e
            # 其余：先升到共同祖先
            def path_to_root(p):
                out = []
                if p[0] == 0:
                    out = [(0, 0), (1, 0), (2, 0)]
                elif p[0] == 1:
                    out = [(1, 0), (2, 0)]
                else:
                    out = [(2, 1), (2, 0)]
                return out
            sp = path_to_root(px)[::-1]   # 从根往下
            sq = path_to_root(py)[::-1]
            k = 0
            while k < min(len(sp), len(sq)) and sp[k] == sq[k]:
                k += 1
            w = {(0, 0): F(0), (1, 0): L1, (2, 0): F(0), (2, 1): L2}
            return pw[x] + pw[y] + sum(w[node] for node in sp[k-1:]) + sum(w[node] for node in sq[k-1:])
        return {(x, y): dist(x, y) for x, y in combinations('abcde', 2)}
    raise SystemExit('n 只支持 4 与 5')

def as_dict(n, d):
    out = {}
    for x, y in combinations('abcde'[:n], 2):
        out[frozenset((x, y))] = d[(x, y)] if (x, y) in d else d[(y, x)]
    return out

def is_cherry(n, D, x, y):
    """库内 `Dissimilarity.IsCherry` 的四点形式（:78）。"""
    if x == y:
        return False
    rest = [k for k in 'abcde'[:n] if k not in (x, y)]
    for k, l in combinations(rest, 2):
        dxy, dkl = D[frozenset((x, y))], D[frozenset((k, l))]
        if not (dxy + dkl <= D[frozenset((x, k))] + D[frozenset((y, l))]):
            return False
        if not (dxy + dkl <= D[frozenset((x, l))] + D[frozenset((y, k))]):
            return False
    return True

def Q(n, D, i, j):
    N = F(n)
    S = lambda x: sum(D[frozenset((x, k))] for k in 'abcde'[:n] if k != x)
    return (N - 2) * D[frozenset((i, j))] - S(i) - S(j)

def disjoint(i, j, k, l):
    return i != k and i != l and j != k and j != l

def shares_one(i, j, k, l):
    return ((i == k and j != k and j != l) or (i == l and j != k and j != l)
            or (j == k and i != k and i != l) or (j == l and i != k and i != l))

def check(n, pendant, internal):
    d = tree_metric(n, pendant, internal)
    D = as_dict(n, d)
    dmin = min(list(pendant) + list(internal))
    labels = 'abcde'[:n]
    cherries = [(i, j) for i, j in combinations(labels, 2) if is_cherry(n, D, i, j)]
    nondis = 0            # 可被占据的 DisjointPairs 见证数
    slack_dis, slack_sha = [], []
    for k, l in combinations(labels, 2):
        if is_cherry(n, D, k, l):
            continue
        for i, j in cherries:
            gap = Q(n, D, k, l) - Q(n, D, i, j)
            if disjoint(i, j, k, l):
                nondis += 1
                slack_dis.append(gap - 3 * (n - 4) * dmin)
            if shares_one(i, j, k, l):
                slack_sha.append(gap - 2 * (n - 3) * dmin)
    return dict(dmin=dmin, cherries=cherries, disjoint_witnesses=nondis,
                min_slack_disjoint=min(slack_dis) if slack_dis else None,
                min_slack_shared=min(slack_sha) if slack_sha else None)

print('=== n = 4：三个具体树（含「全边等长」退化解）===')
cases4 = [
    ("全边 = 1（退化/最紧）", [F(1)] * 4, [F(1)]),
    ("悬挂 1,1,1,1 内部 3", [F(1)] * 4, [F(3)]),
    ("悬挂 1,2,3,4 内部 5", [F(1), F(2), F(3), F(4)], [F(5)]),
    ("内部边最短(0.5) 其余 2", [F(2)] * 4, [F(1, 2)]),
    ("零内部边（δmin=0 退化）", [F(1)] * 4, [F(0)]),
]
for name, p, it in cases4:
    r = check(4, p, it)
    print(f"  {name}: cherries={r['cherries']} dmin={r['dmin']} "
          f"DisjointPairs 见证数={r['disjoint_witnesses']} "
          f"slack(不交)={r['min_slack_disjoint']} slack(恰交)={r['min_slack_shared']}")

print('=== n = 5：两个具体树 ===')
cases5 = [
    ("全边 = 1", [F(1)] * 5, [F(1), F(1)]),
    ("内部 0.5 / 悬挂 2", [F(2)] * 5, [F(1, 2), F(1, 2)]),
]
for name, p, it in cases5:
    r = check(5, p, it)
    print(f"  {name}: cherries={r['cherries']} dmin={r['dmin']} "
          f"DisjointPairs 见证数={r['disjoint_witnesses']} "
          f"slack(不交)={r['min_slack_disjoint']} slack(恰交)={r['min_slack_shared']}")

print("""
=== 结论（机械）===
(1) n=4 时 `DisjointPairs` 见证数恒为 **0**：4 个标签上，非樱桃对 {k,l} 的补集恰好是另一对，
    而那只对**不是**樱桃 ⇒ 樱桃必与 {k,l} 恰交一标签 ⇒ `3*(n-4)*δmin = 0` 那条分支
    在 n=4 上**不能被占据**（它写的右边 0 与否无关紧要，前提就假）。
(2) 故 n=4 的全部内容落在 `SharesOneLabel` 分支的 `2*(n-3)*δmin = 2*δmin` 上；
    「全边等长」时 slack 恰为 **0**（紧），但**不是**被「Q 差恒为 0」平凡满足
    —— `Q 差 = 2L`（L = 内部边长），要求 `2L >= 2*min(...)`，只有 `L >= min` 成立才过。
(3) 「零内部边」时 δmin = 0，命题退化成 `Q k l >= Q i j`（弱形式）—— 这是
    `minEdgeWeight = 0` 的退化支，仍非空转（要证 Q 不增），但**不含定量内容**。
""")
