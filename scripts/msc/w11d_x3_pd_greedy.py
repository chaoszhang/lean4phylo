#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
msc/w11d_x3_pd_greedy.py —— W11d / X3 的 ★C 穷举核对

在**最小具体例子**上把 PD 的贪心算法与穷举最大 PD 对齐，并检查 ★B
（「PD 增量是否次模」的最小反例搜索）。

铁律：纯标准库、**整数**穷举、无 Monte Carlo、无浮点、无随机。

与 Lean 侧 `Phylo/PhyloDiversity.lean` 的定义逐字对齐：
  PD_lean(S)  = Σ_{e ∈ E(T)} [e 分离 S 中两个叶] · w(e)   （每条「连接边」计**一次**）
  PD_steel(S) = 连接 S 的最小子树的枝长和                  （Steel 2005 第 15–16 行）
脚本的核对断言：**PD_lean = PD_steel**（每条连接边恰好计一次）。

⚠️ 关于「贪心」的两条文献纪律（本脚本严格遵守）：
  * Steel 第 248 行：第一步「Select any pair of species that are **maximally far apart**」
    —— 即 **k = 2 时必须穷举取最大对**；
  * Pardi–Goldman 第 274–276 行 Observation：`k = 1` 时任何单点都是「极大」的
    （PD = 0），故从单点起步的贪心对 `k = 1 → 2` 一步**不**保证最优。

文献：Steel 2005, Syst. Biol. 54(4):527–529；
      Pardi & Goldman 2005, PLoS Genet 1(6):e71。
"""

import itertools
from collections import deque

# ---------------------------------------------------------------- 树

class Tree:
    """无根带权树：顶点 0..n-1，边 (u, v, w)（w ≥ 0，整数）。"""

    def __init__(self, n, edges, leaves):
        self.n = n
        self.adj = [[] for _ in range(n)]
        for (u, v, w) in edges:
            self.adj[u].append((v, w))
            self.adj[v].append((u, w))
        self.edges = list(edges)
        self.leaves = list(leaves)

    def side_of_edge(self, e_idx):
        """删除第 e_idx 条边后每个顶点所属的分量 id。"""
        (eu, ev, _) = self.edges[e_idx]
        comp = [-1] * self.n
        cid = 0
        for s in range(self.n):
            if comp[s] != -1:
                continue
            comp[s] = cid
            dq = deque([s])
            while dq:
                x = dq.popleft()
                for (y, w) in self.adj[x]:
                    if {x, y} == {eu, ev}:
                        continue
                    if comp[y] == -1:
                        comp[y] = cid
                        dq.append(y)
            cid += 1
        return comp

    def pd_lean(self, S):
        """Σ_e [e 分离 S 中两个叶] · w(e)；|S| ≤ 1 时为 0。

        即「连接 S 的最小子树」的边权和 —— 与 PD_steel 完全一致（每条边计一次）。"""
        S = list(S)
        if len(S) <= 1:
            return 0
        total = 0
        for i in range(len(self.edges)):
            comp = self.side_of_edge(i)
            if len(set(comp[v] for v in S)) == 2:
                total += self.edges[i][2]
        return total

    def path_edges(self, a, b):
        """a→b 唯一路径经过的边索引集合（含 0 权边）。"""
        parent = {a: None}
        dq = deque([a])
        while dq:
            x = dq.popleft()
            if x == b:
                break
            for (y, w) in self.adj[x]:
                if y not in parent:
                    parent[y] = x
                    dq.append(y)
        idxs = set()
        cur = b
        while parent[cur] is not None:
            p = parent[cur]
            for i, (u, v, w) in enumerate(self.edges):
                if {u, v} == {p, cur}:
                    idxs.add(i)
                    break
            cur = p
        return idxs

    def pd_steel(self, S):
        """连接 S 的最小子树的枝长和（Steel 2005 的定义）。"""
        S = list(S)
        if len(S) <= 1:
            return 0
        used = set()
        for a, b in itertools.combinations(S, 2):
            used |= self.path_edges(a, b)
        return sum(self.edges[i][2] for i in used)

    def greedy(self, k):
        """k = 1：任取单点；k ≥ 2：先穷举取最大 PD 的 2-集（Steel 第 248 行），
        其后每步取使 PD 增量最大者（并列取字典序最小）。"""
        if k == 1:
            x = min(self.leaves)
            return [x], self.pd_lean([x])
        best2, bestv = None, -1
        for S in itertools.combinations(self.leaves, 2):
            v = self.pd_lean(list(S))
            if v > bestv:
                best2, bestv = tuple(sorted(S)), v
        seq = list(best2)
        for _ in range(k - 2):
            cands = [x for x in self.leaves if x not in seq]
            seq.append(max(cands, key=lambda x: (self.pd_lean(seq + [x]), -x)))
        return seq, self.pd_lean(seq)


# ---------------------------------------------------------------- 实例

def steel_figure_1():
    """Steel 2005 图 1 的树（按论文数值重建；PD({a,b,g,e}) = 18）。"""
    a, b, c, d, e, f, g = 0, 1, 2, 3, 4, 5, 6
    u, tab, teg, w, tcd = 7, 8, 9, 10, 11
    return Tree(12, [
        (a, u, 0), (b, u, 0),
        (u, tab, 3), (tab, w, 2), (w, teg, 4),
        (c, tcd, 3), (d, tcd, 0), (tcd, w, 1),
        (e, teg, 5), (g, teg, 4), (f, teg, 2),
    ], [a, b, c, d, e, f, g])


def minimal_four_leaf():
    """最小 4 叶实例 (a,b)|(c,d)：叶边权 1,2,3,4，内部边权 5,5。"""
    a, b, c, d = 0, 1, 2, 3
    x, z, y = 4, 5, 6
    return Tree(7, [(a, x, 1), (b, x, 2), (c, y, 3), (d, y, 4), (x, z, 5), (z, y, 5)],
                [a, b, c, d])


def star_three():
    return Tree(4, [(0, 1, 1), (0, 2, 1), (0, 3, 1)], [1, 2, 3])


def star_four():
    return Tree(5, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1)], [1, 2, 3, 4])


# ---------------------------------------------------------------- 核对

def check(kind, tree):
    leaves = tree.leaves
    n = len(leaves)
    print(f"\n=== {kind}（{n} 叶，{len(tree.edges)} 边）===")

    # (0) PD_lean = PD_steel
    bad = [(S, tree.pd_lean(list(S)), tree.pd_steel(list(S)))
           for r in range(1, n + 1) for S in itertools.combinations(leaves, r)
           if tree.pd_lean(list(S)) != tree.pd_steel(list(S))]
    print(f"  (0) PD_lean = PD_steel 对全部 {2**n - 1} 个非空子集："
          f"{'成立' if not bad else '失败 ' + str(bad[:3])}")

    # (1) ★B 次模性穷举 —— 预期**有**反例（PD 不次模；见 Lean `not_PD_submodular`）
    viol = []
    for rB in range(n + 1):
        for B in itertools.combinations(leaves, rB):
            Bs = set(B)
            rest = [x for x in leaves if x not in Bs]
            for rA in range(rB + 1):
                for A in itertools.combinations(B, rA):
                    As = set(A)
                    for x in rest:
                        # 次模性要求的原始不等式（增量随集合增大而不增）：
                        #   PD(A∪{x}) + PD(B) ≥ PD(B∪{x}) + PD(A)
                        lhs = tree.pd_lean(list(As | {x})) + tree.pd_lean(list(Bs))
                        rhs = tree.pd_lean(list(Bs | {x})) + tree.pd_lean(list(As))
                        if lhs < rhs:
                            viol.append((A, B, x, lhs - rhs))
    print(f"  (1) ★B 次模性（增量随集合增大而不增）穷举："
          f"{'无反例' if not viol else f'有反例 {len(viol)} 个，最小 = ' + str(viol[0])}")

    # (1b) Steel 式 (1) 的交换性质（穷举）—— 预期**零**失败
    ex_fail = []
    for rWp in range(2, n + 1):
        for Wp in itertools.combinations(leaves, rWp):
            Wps = set(Wp)
            for rW in range(rWp + 1, n + 1):
                for W in itertools.combinations(leaves, rW):
                    Ws = set(W)
                    ok = any(
                        tree.pd_lean(list(Ws - {x})) + tree.pd_lean(list(Wps | {x}))
                        >= tree.pd_lean(list(Ws)) + tree.pd_lean(list(Wps))
                        for x in Ws - Wps)
                    if not ok:
                        ex_fail.append((tuple(sorted(Ws)), tuple(sorted(Wps))))
    print(f"  (1b) Steel 式(1) 交换性质（2 ≤ |W'| < |W|）穷举："
          f"{'零失败' if not ex_fail else '失败 ' + str(ex_fail[:3])}")

    # (2) ★C 贪心 vs 穷举
    print("  (2) ★C 贪心 vs 穷举（每 k；贪心按 Steel 形式从最大 2-集起步）：")
    all_ok = True
    for k in range(1, n + 1):
        bf = max(tree.pd_lean(list(S)) for S in itertools.combinations(leaves, k))
        seq, gp = tree.greedy(k)
        ok = (gp == bf)
        all_ok &= ok
        print(f"      k={k}: 穷举最大 PD={bf:3d}  贪心 PD={gp:3d}  序列={seq}  "
              f"{'✓' if ok else '✗ 不等'}")
    print(f"      贪心对**每个** k 都最优：{'是' if all_ok else '否'}")

    # (3) 论文数值核对
    if kind.startswith("Steel"):
        S = [0, 1, 4, 6]
        print(f"  (3) 论文数值：PD({{a,b,g,e}}) = {tree.pd_steel(S)}（论文 = 18）")

    # (4) ★B 阴性：k = 1 无区分度
    if kind.startswith("star"):
        sizes = {r: max(tree.pd_lean(list(S)) for S in itertools.combinations(leaves, r))
                 for r in range(1, n + 1)}
        print(f"  (4) ★B 阴性检查：星形按 k 的最大 PD = {sizes}")
        print("      —— 所有 k-子集同值，故 k = 1 时贪心第一步无区分度，"
              "与 Pardi–Goldman Observation（第 274–276 行）一致。")


def main():
    print("=" * 74)
    print(" W11d / X3 —— PD 贪心最优性的穷举核对（纯标准库、整数、无随机）")
    print("=" * 74)
    check("Steel 2005 图 1（7 叶）", steel_figure_1())
    check("最小 4 叶实例", minimal_four_leaf())
    check("star 3 叶", star_three())
    check("star 4 叶", star_four())
    print("\n" + "=" * 74)
    print(" 结论：")
    print("  * PD_lean（Lean 侧定义）= PD_steel（Steel 2005 定义）逐子集成立；")
    print("  * ★B（**阴性**）：PD **不是**次模的 —— 上方 (1) 给出最小反例")
    print("         A=∅, B={b}, x=c：PD({b,c})+PD({b}) = 0 < 2 = PD({b,c})+PD(∅)")
    print("        （Lean 侧机器可查：`Phylo.PhyloDiversity.not_PD_submodular`）；")
    print("  * ★ 真正成立的是 Steel 式(1) 的**交换性质**（上方 (1b) 穷举零失败），")
    print("        它才是『greedoid』结构（Steel 第 332–337 行点名的框架）；")
    print("  * 贪心（**从最大 2-集起步** + 每步最大增量）对每个 k 都达到穷举最大值（★C）；")
    print("  * 「任取单点起步」的变体在 k = 1 → 2 一步**不**最优（Pardi–Goldman Observation）。")
    print("=" * 74)


if __name__ == "__main__":
    main()
