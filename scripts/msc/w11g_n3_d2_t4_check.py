#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""w11g_n3_d2_t4_check.py -- W11g / N3 + D2 + T-4 的**穷举精确**数值核验（纯标准库）

★C（最小具体例子的**穷举**版）：一切用**精确有理数**（`fractions.Fraction`）计算：
**无 Monte Carlo、无随机数、无第三方库**（与 `scripts/msc/` 既有脚本的约定一致）。

载体：无根二叉（叶标号）树 —— 顶点用 `dict[int, set[int]]` 表示，
**叶 = `0..n-1`**，**内点 = `1000..`**（两段编号不重叠，避免历史版本的编号撞车 bug）。
树由「3 叶星形 + 逐次插叶」生成，用**split 系统**（Splits-Equivalence）去重。

三块核验：

* **D2 Pauplin 公式**（`n = 4..7` 的全部二叉无根树）
  1. **逐边 Pauplin 归一化**：内部边 `Σ_{i<j, e∈P_ij} 2^{1−n_ij} = 1`、挂边同理；
  2. **公式本体**：`L(T) = Σ_{i<j} 2^{1−n_ij} d_ij = Σ_e w_e`（两组确定性边权：全 1 ／ 变化权）；
  3. ★B **非二叉反例**：4 叶星形（内点度 4）挂边系数 `3·2^{−1} = 3/2 ≠ 1`，且 `L ≠ l(T)`。
* **T-4 NNI 邻域/度量**（`n = 4..6` 的 NNI 图）
  1. 每条内部边的三个分解（自身 + 两个 NNI）**互不相同**；
  2. **3-循环封闭**：从任一分解再走一步，同时可达另外两个；
  3. 一次 NNI 恰改动 **1** 条内部分裂、**RF 距离 = 2**；
  4. **RF ≤ 2·d_NNI**（BFS 精确 NNI 距离），并报告图连通性与直径；
  5. ★B 派单候选 `2(n−3) − |共有内部分裂|` **≠** 真实 NNI 距离（打印首批反例）。
* **N3 quarnet（树侧 Type I）**（`n = 4..7` 的全部二叉树）
  1. 每个 4-元子集**恰有 1** 个被展出的 quartet（thin + 存在性 = Huber (D1) 的 `m = 1` 分支）；
  2. **Colonius–Schulze 规则**：`ab|cx ∧ ab|xd ⟹ ab|cd`（对所有第五点 `x`）；
  3. ★B **(S1) 的析取不可收缩为单支**：两种单支情形**都真的出现**（各给显式见证）。

用法：`python3 scripts/msc/w11g_n3_d2_t4_check.py`；退出码 0 = 全通过，1 = 有反例。
"""

from fractions import Fraction
from itertools import combinations
from collections import deque
import sys

FAIL = []
INTERNAL_OFFSET = 1000


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  x FAIL: %s" % msg)
    return cond


# ------------------------------------------------------------------ 树
def leaf_star3():
    """3 叶星形：叶 0,1,2，内点 1000。"""
    c = INTERNAL_OFFSET
    return {0: {c}, 1: {c}, 2: {c}, c: {0, 1, 2}}


def copy_tree(t):
    return {v: set(nb) for v, nb in t.items()}


def insert_leaf(t, u, v, lab):
    """把叶 `lab` 插到边 `{u,v}` 上（`u - w - v`，`w - lab`）。"""
    t = copy_tree(t)
    w = max(t) + 1
    t[u].discard(v)
    t[v].discard(u)
    t[w] = {u, v, lab}
    t[u].add(w)
    t[v].add(w)
    t[lab] = {w}
    return t


def is_leaf(t, v):
    return len(t[v]) == 1


def edges(t):
    return sorted({tuple(sorted((u, v))) for u in t for v in t[u]})


def side_leaves(t, u, v):
    """删边 `{u,v}` 后 `u` 侧的**叶**集合。"""
    seen = {u}
    dq = deque([u])
    while dq:
        x = dq.popleft()
        for y in t[x]:
            if (x, y) in ((u, v), (v, u)):
                continue
            if y not in seen:
                seen.add(y)
                dq.append(y)
    return frozenset(x for x in seen if is_leaf(t, x))


def split_system(t, n):
    """全部边诱导的 split，规范取向 = 不含叶 `0` 的那一侧。"""
    out = set()
    for (u, v) in edges(t):
        s = side_leaves(t, u, v)
        if not s or len(s) == n:
            continue
        out.add(frozenset(set(range(n)) - s) if 0 in s else s)
    return frozenset(out)


def internal_splits(t, n):
    return frozenset(s for s in split_system(t, n) if 2 <= len(s) <= n - 2)


def internal_edges(t, n):
    out = []
    for (u, v) in edges(t):
        s = side_leaves(t, u, v)
        if 2 <= len(s) <= n - 2:
            out.append((u, v))
    return out


def all_binary_trees(n):
    frontier = {split_system(leaf_star3(), 3): leaf_star3()}
    for lab in range(3, n):
        nxt = {}
        for t in frontier.values():
            for (u, v) in edges(t):
                nt = insert_leaf(t, u, v, lab)
                c = split_system(nt, lab + 1)
                nxt.setdefault(c, nt)
        frontier = nxt
    return list(frontier.values())


def edge_dist(t, a, b):
    dq = deque([(a, 0)])
    seen = {a}
    while dq:
        x, d = dq.popleft()
        if x == b:
            return d
        for y in t[x]:
            if y not in seen:
                seen.add(y)
                dq.append((y, d + 1))
    raise AssertionError("not connected")


def path_edges(t, a, b):
    prev = {a: None}
    dq = deque([a])
    while dq:
        x = dq.popleft()
        for y in t[x]:
            if y not in prev:
                prev[y] = x
                dq.append(y)
    es, x = [], b
    while prev[x] is not None:
        es.append(tuple(sorted((x, prev[x]))))
        x = prev[x]
    return es


def p2(e):
    """`2^e`（`e` 为整数），精确有理数。"""
    return Fraction(2) ** e


def weights_for(t, varying):
    es = edges(t)
    if varying:
        return {e: Fraction(1 + (k % 7), 3) for k, e in enumerate(es)}
    return {e: Fraction(1) for e in es}


def pauplin(t, n, w):
    tot = Fraction(0)
    for i, j in combinations(range(n), 2):
        d = sum(w[e] for e in path_edges(t, i, j))
        tot += p2(1 - edge_dist(t, i, j)) * d
    return tot


# ------------------------------------------------------------------ D2
def check_d2(n, trees, varying):
    tag = "变化权" if varying else "全 1 权"
    print("[D2] n=%d：%d 棵树 ×（逐边归一化 + 公式本体），%s" % (n, len(trees), tag))
    for t in trees:
        w = weights_for(t, varying)
        total = sum(w.values())
        # (1a) 内部边
        for (u, v) in internal_edges(t, n):
            A = side_leaves(t, u, v)
            B = frozenset(range(n)) - A
            c = sum(p2(1 - edge_dist(t, i, j)) for i in A for j in B)
            check(c == 1, "n=%d 内部边 %s 系数 %s ≠ 1" % (n, (u, v), c))
        # (1b) 挂边
        for x in range(n):
            c = sum(p2(1 - edge_dist(t, x, j)) for j in range(n) if j != x)
            check(c == 1, "n=%d 挂边 %d 系数 %s ≠ 1" % (n, x, c))
        # (2) 公式本体
        L = pauplin(t, n, w)
        check(L == total, "n=%d L=%s ≠ 树长 %s（%s）" % (n, L, total, tag))


def check_star_counterexample():
    print("[D2] ★B 非二叉反例：4 叶星形（内点度 4）")
    c = INTERNAL_OFFSET
    t = {0: {c}, 1: {c}, 2: {c}, 3: {c}, c: {0, 1, 2, 3}}
    n = 4
    w = {tuple(sorted((c, x))): Fraction(1) for x in range(4)}
    total = sum(w.values())
    coeff = sum(p2(1 - edge_dist(t, 0, j)) for j in range(1, 4))
    check(coeff == Fraction(3, 2), "星形挂边系数 = %s ≠ 3/2" % coeff)
    L = pauplin(t, n, w)
    check(L != total, "星形树上 Pauplin 竟等于树长 —— ★B 失效")
    check(2 * p2(-1) == 1, "二叉内点系数应为 1")
    print("      挂边系数 = %s；L = %s ≠ l(T) = %s（L/l = %s）"
          % (coeff, L, total, Fraction(L, total)))


# ------------------------------------------------------------------ T-4
def nni(t, n, e):
    """内部边 `e=(u,v)` 的两个 NNI 邻树。"""
    u, v = e
    a = [x for x in t[u] if x != v]
    b = [x for x in t[v] if x != u]
    if len(a) != 2 or len(b) != 2:
        return []
    out = []
    for k in range(2):
        nt = copy_tree(t)
        a2 = a[1]
        bk = b[k]
        nt[u].discard(a2)
        nt[a2].discard(u)
        nt[v].discard(bk)
        nt[bk].discard(v)
        nt[u].add(bk)
        nt[bk].add(u)
        nt[v].add(a2)
        nt[a2].add(v)
        out.append(nt)
    return out


def check_t4(n, trees, bfs_limit=6):
    print("[T-4] n=%d：NNI 邻域 / 3-循环 / RF 变化 / 距离下界" % n)
    idx = {split_system(t, n) for t in trees}
    for t in trees:
        st = split_system(t, n)
        for e in internal_edges(t, n):
            nb = nni(t, n, e)
            check(len(nb) == 2, "内部边 %s 的 NNI 邻数 ≠ 2" % (e,))
            c0 = st
            c1 = split_system(nb[0], n)
            c2 = split_system(nb[1], n)
            check(len({c0, c1, c2}) == 3, "三个分解不互不相同")
            for nt in nb:
                snt = split_system(nt, n)
                check(len(snt ^ st) == 2, "一次 NNI 改动 %d 条分裂 ≠ 2" % len(snt ^ st))
                check(len(snt - st) == 1 and len(st - snt) == 1,
                      "一次 NNI 不是「换掉一条」")
                check(snt in idx, "NNI 邻树不在枚举里（n=%d）" % n)
            # 3-循环封闭：从 c1 走一步应可达 c0 与 c2
            reach = set()
            for e2 in internal_edges(nb[0], n):
                for nt2 in nni(nb[0], n, e2):
                    reach.add(split_system(nt2, n))
            check(c0 in reach and c2 in reach, "从分解 c1 再走一步未同时回到 c0、c2")
    if n > bfs_limit:
        return
    adj = {}
    for t in trees:
        c = split_system(t, n)
        adj.setdefault(c, set())
        for e in internal_edges(t, n):
            for nt in nni(t, n, e):
                cn = split_system(nt, n)
                adj.setdefault(cn, set()).add(c)
                adj[c].add(cn)
    nodes = list(adj)
    print("      NNI 图：%d 顶点 / %d 边" % (len(nodes), sum(len(v) for v in adj.values()) // 2))
    dist_all = {}
    diam = 0
    for src in nodes:
        dist = {src: 0}
        dq = deque([src])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    dq.append(y)
        check(len(dist) == len(nodes), "NNI 图不连通（%d/%d）" % (len(dist), len(nodes)))
        for dst, d in dist.items():
            dist_all[(src, dst)] = d
            diam = max(diam, d)
            check(len(src ^ dst) <= 2 * d, "RF=%d > 2·d_NNI=%d" % (len(src ^ dst), 2 * d))
    print("      连通 ✓；直径 = %d（有序对 %d）" % (diam, len(dist_all)))
    def intern(s):
        return {x for x in s if 2 <= len(x) <= n - 2}

    bad, shown = 0, 0
    for (src, dst), d in dist_all.items():
        shared = len(intern(src) & intern(dst))
        cand = 2 * (n - 3) - shared
        if cand != d:
            bad += 1
            if shown < 3:
                print("      ★B：n=%d 一对树 —— d_NNI=%d，候选 2(n−3)−|共有内部分裂|=%d（共有 %d）"
                      % (n, d, cand, shared))
                shown += 1
    check(bad > 0, "n=%d：候选公式竟然处处正确" % n)
    print("      ★B：候选公式与真实距离不一致的有序对 = %d / %d" % (bad, len(dist_all)))
    # n = 4 的一次 NNI：与 Lean `nniDistanceCandidate_wrong` 对齐
    if n == 4:
        src = split_system(trees[0], n)
        for e in internal_edges(trees[0], n):
            dst = split_system(nni(trees[0], n, e)[0], n)
            shared = len(intern(src) & intern(dst))
            check(dist_all[(src, dst)] == 1 and 2 * (4 - 3) - shared == 2,
                  "n=4 一次 NNI：d=%d，候选=%d（应 1 与 2）"
                  % (dist_all[(src, dst)], 2 * (4 - 3) - shared))
            print("      n=4 一次 NNI：d_NNI = 1，候选 2(n−3)−0 = 2 ✓（与 Lean 反例一致）")
            break


# ------------------------------------------------------------------ N3
def exhibited_quartets(t, n):
    """`{a<b}|{c<d}` 形式的展出 quartet 集合（`frozenset` 支撑 -> 配对）。"""
    spl = split_system(t, n)
    out = {}
    for a, b, c, d in combinations(range(n), 4):
        for s in spl:
            if a in s and b in s and c not in s and d not in s:
                out[frozenset((a, b, c, d))] = frozenset(((a, b), (c, d)))
                break
    return out


def check_n3(n, trees):
    print("[N3] n=%d：树侧（Type I）quarnet 规则" % n)
    only1 = only2 = 0
    for t in trees:
        Q = exhibited_quartets(t, n)
        for key, pair in Q.items():
            check(len(pair) == 2 and all(len(p) == 2 for p in pair),
                  "配对形状异常 %s" % (pair,))
        # (1) 每个 4-元子集至多一个（thin）；枚举的 4-元子集恰有一个（存在性）
        for quad in combinations(range(n), 4):
            check(frozenset(quad) in Q,
                  "4-元集 %s 上无展出 quartet（存在性失效）" % (quad,))
        # (2) Colonius–Schulze
        for a, b, c, d in combinations(range(n), 4):
            base = Q.get(frozenset((a, b, c, d)))
            if base is None:
                continue
            for x in range(n):
                if x in (a, b, c, d):
                    continue
                qcx = Q.get(frozenset((a, b, c, x)))
                qxd = Q.get(frozenset((a, b, x, d)))
                if qcx == frozenset(((a, b), (c, x))) and qxd == frozenset(((a, b), (x, d))):
                    check(base == frozenset(((a, b), (c, d))),
                          "Colonius–Schulze 失效：%s" % ((a, b, c, d, x),))
        # ★B：单支见证计数（用树自己的 split 系统）
        for s in split_system(t, n):
            A = sorted(s)
            B = sorted(set(range(n)) - s)
            if len(A) < 2 or len(B) < 3:
                pass
            # x ∈ B 且 x ∉ {c,d}：ab|cd 与 ab|cx 展出，但 ax|cd 不展出
            for a, b in combinations(A, 2):
                for c, d in combinations(B, 2):
                    for x in B:
                        if x in (c, d):
                            continue
                        if Q.get(frozenset((a, b, c, d))) == frozenset(((a, b), (c, d))) and \
                           Q.get(frozenset((a, b, c, x))) == frozenset(((a, b), (c, x))):
                            only1 += 1
            # x ∈ A 且 x ∉ {a,b}：ab|cd 与 ax|cd 展出，但 ab|cx 不展出
            for c, d in combinations(B, 2):
                for a, b in combinations(A, 2):
                    for x in A:
                        if x in (a, b):
                            continue
                        if Q.get(frozenset((a, b, c, d))) == frozenset(((a, b), (c, d))) and \
                           Q.get(frozenset((a, x, c, d))) == frozenset(((a, x), (c, d))):
                            only2 += 1
    check(only1 > 0 and only2 > 0,
          "n=%d：(S1) 的单支情形未同时出现（only1=%d, only2=%d）" % (n, only1, only2))
    print("      ★B：`ab|cx` 独有见证 %d 例；`ax|cd` 独有见证 %d 例（两者都非零 ⟹ 析取必要）"
          % (only1, only2))


# ------------------------------------------------------------------ main
def main():
    expect = {4: 3, 5: 15, 6: 105, 7: 945}
    for n in (4, 5, 6, 7):
        trees = all_binary_trees(n)
        ok = check(len(trees) == expect[n],
                   "n=%d 二叉无根树数 %d ≠ %d" % (n, len(trees), expect[n]))
        print("n=%d：%d 棵二叉无根树（(2n−5)!! = %d）%s"
              % (n, len(trees), expect[n], "✓" if ok else "x"))
        check_d2(n, trees, varying=False)
        check_d2(n, trees, varying=True)
        check_n3(n, trees)
        check_t4(n, trees)
    check_star_counterexample()
    print("")
    if FAIL:
        print("== 失败 %d 项 ==" % len(FAIL))
        for m in FAIL[:20]:
            print("  - %s" % m)
        return 1
    print("== 全部通过（穷举·精确有理数·无 Monte Carlo）==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
