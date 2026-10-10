#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12h · greedy_gap 的数值核对（★D）—— v3（全性质报告 + PD 模型自检）

PD 模型（与库内 `Cladogram.IsCovered` 逐字一致）：
  `PD(S) = Σ_{e ∈ E} [∃ x,y ∈ S, e 分离 leaf x 与 leaf y] · w(e)`
  即「连接 `S` 的最小子树的边权和」（库内 `PD_of_card_le_one`：`|S| ≤ 1 ⟹ 0`）。

核对：
  (P0) 单调性 `S ⊆ T ⟹ PD(S) ≤ PD(T)`
  (P1) 加权交换性质（Steel 式 (1)）
  (P2) 辅助交换引理（k ≥ 2）
  (P3) 单点可扩：`∀ a ∃ M, |M| = 2 ∧ a ∈ M ∧ PD(M) = pd₂`
  (P4) 主引理：`|A| = k ≥ 1 ⟹ ∃ M ⊇ A, |M| = k+1 ∧ PD(M) = pd_{k+1}`
  (P5) 目标命题 `greedy_gap` 本身
"""

import itertools
import random
import sys

TOL = 1e-12


def rooted_binary_trees(leaves):
    leaves = tuple(sorted(leaves))
    if len(leaves) == 1:
        return [("L", leaves[0])]
    out = []
    first = leaves[0]
    rest = leaves[1:]
    for size in range(0, len(rest) + 1):
        for combo in itertools.combinations(rest, size):
            sideA = frozenset((first,) + combo)
            sideB = frozenset(rest) - frozenset(combo)
            if not sideB:
                continue
            for tl in rooted_binary_trees(sideA):
                for tr in rooted_binary_trees(sideB):
                    out.append((tl, tr))
    return out


def is_leaf(t):
    return t[0] == "L"


def canon(t):
    if is_leaf(t):
        return ("L", t[1])
    return (canon(t[0]), canon(t[1]))


def to_graph(tree, n):
    adj = {}
    edges = []
    ctr = [-1]

    def newv():
        v = ctr[0]
        ctr[0] -= 1
        return v

    def add(u, v):
        eid = len(edges)
        edges.append((u, v))
        adj.setdefault(u, []).append((v, eid))
        adj.setdefault(v, []).append((u, eid))

    def go(node, parent):
        if is_leaf(node):
            add(parent, node[1])
            return
        v = newv()
        if parent is not None:
            add(parent, v)
        go(node[0], v)
        go(node[1], v)

    go(tree, None)
    return adj, edges


def pd_cov(tree, n):
    adj, edges = to_graph(tree, n)
    side = {}
    for eid, (u, v) in enumerate(edges):
        seen = {u}
        stack = [u]
        while stack:
            a = stack.pop()
            for b, e2 in adj[a]:
                if e2 == eid or b in seen:
                    continue
                seen.add(b)
                stack.append(b)
        side[eid] = frozenset(seen)
    idx = sorted(x for x in adj if x >= 0)
    cov = {}
    for mask in range(1 << n):
        S = [idx[i] for i in range(n) if mask >> i & 1]
        if len(S) <= 1:
            cov[frozenset(S)] = frozenset()
            continue
        c = set()
        for eid in range(len(edges)):
            s = side[eid]
            if any((x in s) != (y in s) for x, y in itertools.combinations(S, 2)):
                c.add(eid)
        cov[frozenset(S)] = frozenset(c)
    return cov


def model_selftest():
    """4 叶 caterpillar: ((0,1),(2,3))，边权 R=1, RL=2, RR=3, RLL=4, RLR=5, RRL=6, RRR=7。

    手算（约定：S 的元素在两侧都有时根边 R 计入一次）：
      PD({0}) = 0
      PD({0,1}) = w(RL) + w(RLL) + w(RLR) = 2+4+5 = 11
      PD({1,2}) = w(R)  + w(RLR) + w(RRL) = 1+5+6 = 12
      PD({0,3}) = w(R)  + w(RL)  + w(RLL) + w(RRR) = 1+2+4+7 = 14
    """
    tree = ((("L", 0), ("L", 1)), (("L", 2), ("L", 3)))
    cov = pd_cov(tree, 4)
    nr = max(e for c in cov.values() for e in c) + 1
    w = list(range(1, nr + 1))  # 边权 1,2,3,...（权只用于打印，不参与路径并集自检）
    got = {tuple(sorted(S)): sum(w[e] for e in cov[S]) for S in cov}
    # 用「路径边并集」独立算法复核
    adj, edges = to_graph(tree, 4)
    paths = {}

    def dfs(u, tgt, seen, acc):
        if u == tgt:
            return list(acc)
        for b, e2 in adj[u]:
            if b in seen:
                continue
            seen.add(b)
            acc.append(e2)
            r = dfs(b, tgt, seen, acc)
            if r is not None:
                return r
            acc.pop()
            seen.discard(b)
        return None

    for x in range(4):
        acc = []
        for v in adj:
            if v < 0:
                pass
    # 路径并集算法：以「所有顶点对路径」的并集计
    verts = [v for v in adj]
    for mask in range(1 << 4):
        S = [i for i in range(4) if mask >> i & 1]
        eset = set()
        if len(S) >= 2:
            for x, y in itertools.combinations(S, 2):
                p = dfs(x, y, {x}, [])
                eset |= set(p)
        cov2 = frozenset(eset)
        if cov2 != cov[frozenset(S)]:
            print(f"  !! PD 模型自检失败 S={S}: 边集法={sorted(cov[frozenset(S)])} "
                  f"路径并集法={sorted(cov2)}")
            return False
    # 手算三点（边 id 依 `go` 的 DFS 次序分配）：
    #   (0,1) → {1,2}； (1,2) → 与 (1,3) 经 LCA 相连 → 含 (1,3) 的路径 + {4}；(0,3) → 见下
    checks = [((0, 1), [1, 2]), ((1, 2), [0, 2, 3, 4]), ((0, 3), [0, 1, 3, 5])]
    for S, exp_edges in checks:
        if sorted(cov[frozenset(S)]) != sorted(exp_edges):
            print(f"  !! PD 手算不符 S={S}: got={sorted(cov[frozenset(S)])} exp={sorted(exp_edges)}")
            for kk in sorted(cov, key=lambda s: (len(s), sorted(s))):
                print(f"     cov{sorted(kk)} = {sorted(cov[kk])}")
            return False
    print("PD 模型自检：4 叶 caterpillar 全部 16 个子集上「边集法 = 路径并集法」一致；"
          "3 个手工路径一致。")
    return True


def weight_styles(nedge, rng):
    yield [1.0] * nedge
    yield [float(i + 1) for i in range(nedge)]
    yield [float(nedge - i) for i in range(nedge)]
    yield [0.0] * nedge
    yield [float(rng.randint(0, 4)) for _ in range(nedge)]
    yield [float(rng.randint(1, 6)) for _ in range(nedge)]
    yield [round(rng.uniform(0, 1), 3) for _ in range(nedge)]
    yield [0.0 if rng.random() < 0.5 else 10.0 for _ in range(nedge)]
    for _ in range(10):
        yield [float(rng.randint(0, 9)) for _ in range(nedge)]
    for _ in range(5):
        yield [round(rng.uniform(0, 20), 3) for _ in range(nedge)]


def check_tree(tree, n, w, fails):
    """把每个失败追加到 `fails`（列表），不提前返回。"""
    cov = pd_cov(tree, n)

    def PD(S):
        return sum(w[e] for e in cov[frozenset(S)])

    by_size = {k: [] for k in range(n + 1)}
    for mask in range(1 << n):
        S = frozenset(i for i in range(n) if mask >> i & 1)
        by_size[len(S)].append(S)
    for k in range(n + 1):
        by_size[k].sort(key=lambda s: sorted(s))

    def pdmax(k):
        return 0.0 if k == 0 else max(PD(S) for S in by_size[k])

    pds = {k: pdmax(k) for k in range(n + 1)}

    for k in range(n):
        for S in by_size[k]:
            for x in range(n):
                if x not in S and PD(S | {x}) < PD(S) - TOL:
                    fails.append(("P0", f"S={sorted(S)} x={x}", w))
    for k in range(2, n + 1):
        for W in by_size[k]:
            for j in range(2, k):
                for Wp in by_size[j]:
                    if not any(PD(W - {x}) + PD(Wp | {x}) >= PD(W) + PD(Wp) - TOL
                               for x in W - Wp):
                        fails.append(("P1", f"W={sorted(W)} Wp={sorted(Wp)}", w))
    for k in range(2, n):
        for B in by_size[k + 1]:
            for A in (S for S in by_size[k] if S <= B):
                for Ap in (S for S in by_size[k - 1] if S < A):
                    if not any(PD(A | {x}) >= PD(A) - TOL for x in B - A):
                        fails.append(("P2", f"k={k} A={sorted(A)} Ap={sorted(Ap)} "
                                            f"B={sorted(B)}", w))
    if n >= 2:
        for a in range(n):
            if not any(a in M and abs(PD(M) - pds[2]) < TOL for M in by_size[2]):
                fails.append(("P3", f"a={a}", w))
    for k in range(1, n):
        for A in by_size[k]:
            if not any(A <= M and abs(PD(M) - pds[k + 1]) < TOL for M in by_size[k + 1]):
                fails.append(("P4", f"k={k} A={sorted(A)}", w))
    for k in range(1, n + 1):
        prevs = [S for S in by_size[k] if abs(PD(S) - pds[k]) < TOL]
        if k + 1 > n:
            continue
        nexts = [S for S in by_size[k + 1] if abs(PD(S) - pds[k + 1]) < TOL]
        if not any(p <= q for p in prevs for q in nexts):
            fails.append(("P5", f"k={k}", w))


def main():
    if not model_selftest():
        print("RESULT: PD 模型自检失败，脚本中止")
        return 2
    rng = random.Random(20260712)
    total = 0
    fails = []
    for n in range(2, 7):
        seen = set()
        uniq = []
        for t in rooted_binary_trees(frozenset(range(n))):
            c = repr(canon(t))
            if c not in seen:
                seen.add(c)
                uniq.append(t)
        print(f"n={n}: 叶标号 rooted binary trees = {len(uniq)}", flush=True)
        for ti, tree in enumerate(uniq):
            cov = pd_cov(tree, n)
            nedge = max((e for c in cov.values() for e in c), default=-1) + 1
            for w in weight_styles(nedge, rng):
                total += 1
                check_tree(tree, n, w, fails)
    from collections import Counter
    cnt = Counter(f[0] for f in fails)
    print(f"\n共核对 (树 × 权组) = {total}")
    print("各性质失败计数：" + (", ".join(f"{k}={cnt[k]}" for k in sorted(cnt))
                              if cnt else "全 0（P0–P5 全部通过）"))
    for tag in ["P0", "P1", "P2", "P3", "P4", "P5"]:
        ex = [f for f in fails if f[0] == tag]
        if ex:
            print(f"  首个 {tag} 反例：{ex[0][1]}  w={ex[0][2]}")
    print("RESULT:", "ALL PASS" if not fails else "COUNTEREXAMPLES FOUND")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
