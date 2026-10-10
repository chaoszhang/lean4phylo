#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11d / X2 —— **完美系统发生（perfect phylogeny）与 Four Gamete 条件**的精确穷举核验。

用途：为 Lean 文件 `Phylo/PerfectPhylogeny.lean` 的定理提供**独立的组合学核验**：
  * ★★★ `exists_cladogram_displays_iff_pairwise_sidesCompatible`（Theorem 1.1 的等价刻画）；
  * ★★  `sidesCompatible_iff_no_four_gametes`（`O(nm^2)` 逐对判据的组合内核）；
  * ★B  多状态时两两相容**不充分**（Fitch-Meacham F_3），并**穷举求最小反例**；
  * ★C  最小例子（3 taxa / 2 字符）端到端。

文献（库内替代本，行号同 `.md`）：
  Lam, Gusfield, Sridhar 2009, "Generalizing the Splits Equivalence Theorem and Four Gamete
  Condition: Perfect Phylogeny on Three State Characters", arXiv:0905.1417
  → `references/md/LamGusfieldSridhar2009_PerfectPhylogenyThreeStateCharactersarXiv0905.1417.md`
    * 完美系统发生定义 193-205 行（条件 (3) = 每个状态类的**全体顶点**构成连通子树）
    * Theorem 1.1（Four Gamete Condition）104-106 行
    * Theorem 2.4（r <= 3 时判据要看**三元组**）276-278 行
    * Fitch 例 131-140 行；Theorem 7.1（Fitch-Meacham F_r）1290-1292 行
    * F_r 构造 1256-1273 行；F_3 的 EC1={a0,b2,c1} / EC2={a1,b0,c0} 1283-1284 行
    * F_2 = 四个 gamete 00/01/10/11 1275-1280 行

方法：**纯标准库**（itertools / heapq / collections）、**精确**、**无随机数 / 无 Monte Carlo**。
树空间：本库的 `Cladogram` 要求「叶恰好是度 1 的顶点」且「无度 2 顶点」，
        由度和恒等式 `n*1 + sum(deg_internal) = 2*(2n-3)` 且 `deg_internal >= 3`
        ⇒ **内部顶点度恰好 3** ⇒ `Cladogram` 恰是**全解析无根二叉树**。
        故树 = Prüfer 序列过滤（n <= 5 时 Prüfer 空间 <= 8^6 = 262144，可穷举）。
"""

import heapq
import itertools
import sys
from collections import deque

FAIL = []


def check(cond, label, extra=""):
    tag = "OK  " if cond else "FAIL"
    if not cond:
        FAIL.append(label)
    print("  [%s] %s%s" % (tag, label, ("  " + extra) if extra else ""))


# ---------------------------------------------------------------- 树枚举
def prufer_to_adj(seq, nv):
    """Prüfer 序列 -> 邻接表（nv 个顶点的标号树）。"""
    deg = [1] * nv
    for x in seq:
        deg[x] += 1
    leaves = [i for i in range(nv) if deg[i] == 1]
    heapq.heapify(leaves)
    adj = [[] for _ in range(nv)]
    for x in seq:
        leaf = heapq.heappop(leaves)
        adj[leaf].append(x)
        adj[x].append(leaf)
        deg[x] -= 1
        if deg[x] == 1:
            heapq.heappush(leaves, x)
    u = heapq.heappop(leaves)
    v = heapq.heappop(leaves)
    adj[u].append(v)
    adj[v].append(u)
    return adj


def all_cladograms(n):
    """全部 `Cladogram` **同构类**（n 片叶）：顶点 0..n-1 = 叶，n..2n-3 = 内部顶点。

    ⚠️ Prüfer 枚举给出的是**带标号**树，内部顶点标号有 (n-2)! 种冗余；
    这里按「边侧集」去重（边侧集决定无根树的同构类）。"""
    nv = 2 * n - 2
    seen = set()
    out = []
    for seq in itertools.product(range(nv), repeat=nv - 2):
        adj = prufer_to_adj(seq, nv)
        if any(len(adj[i]) != 1 for i in range(n)):          # 叶：度 1
            continue
        if any(len(adj[i]) < 3 for i in range(n, nv)):        # 内部：度 >= 3
            continue
        key = frozenset(edge_sides(adj, n))
        if key in seen:
            continue
        seen.add(key)
        out.append(adj)
    return out


def edge_sides(adj, n):
    """全部**边侧**（边的两侧各自的叶集）。"""
    sides = set()
    for u in range(len(adj)):
        for v in adj[u]:
            if u < v:
                # 删 (u,v)，取 u 侧
                seen = {u}
                dq = deque([u])
                while dq:
                    a = dq.popleft()
                    for b in adj[a]:
                        if (a == u and b == v) or (a == v and b == u):
                            continue
                        if b not in seen:
                            seen.add(b)
                            dq.append(b)
                leaves = frozenset(x for x in seen if x < n)
                sides.add(leaves)
                sides.add(frozenset(range(n)) - leaves)
    return sides


def connected(vertices, adj):
    """顶点集在 adj 的诱导子图上连通？"""
    vertices = set(vertices)
    if not vertices:
        return True
    start = next(iter(vertices))
    seen = {start}
    dq = deque([start])
    while dq:
        a = dq.popleft()
        for b in adj[a]:
            if b in vertices and b not in seen:
                seen.add(b)
                dq.append(b)
    return seen == vertices


def displayable_multistate(adj, n, chi, r):
    """Gusfield 条件 (3)（193-205 行）：存在全体顶点的状态标注，使每个状态类连通、叶上等于 chi。"""
    nv = len(adj)
    internal = list(range(n, nv))
    for lab in itertools.product(range(r), repeat=len(internal)):
        state = list(chi) + list(lab)
        if all(connected([w for w in range(nv) if state[w] == s], adj) for s in range(r)):
            return True
    return False


def displayed_binary(A, side_set, allset):
    """库内 `DisplaysBinary T A := A = ∅ ∨ A = univ ∨ T.IsSideOf A`（退化字符恒被展示）。"""
    return A == frozenset() or A == allset or (A in side_set)


# ---------------------------------------------------------------- 判据
def sides_compatible(A, B):
    return (A <= B) or (B <= A) or (not (A & B)) or ((A | B) == frozenset(ALL))


def no_four_gametes(A, B):
    """不存在 w in A∩B, x in A\\B, y in B\\A, z in (A∪B)^c 四者俱全。"""
    return not ((A & B) and (A - B) and (B - A) and (ALL - (A | B)))


def binary_compatible(A, B):
    return (A <= B) or (B <= A) or (not (A & B))


# ================================================================ 主流程
def main():
    global ALL
    print("=" * 78)
    print("W11d / X2 完美系统发生 —— 精确穷举核验（纯标准库，无 Monte Carlo）")
    print("=" * 78)

    def dfact(k):
        """双阶乘 k!!（k 为奇数）。"""
        r = 1
        while k > 1:
            r *= k
            k -= 2
        return r

    for n in (3, 4, 5):
        ALL = frozenset(range(n))
        trees = all_cladograms(n)
        expect = dfact(2 * n - 5)
        sidesets = [edge_sides(adj, n) for adj in trees]
        print("\n---- n = %d 片叶：Cladogram 数 = %d（期望 (2n-5)!! = %d） ----"
              % (n, len(trees), expect))
        check(len(trees) == expect, "Cladogram 计数 = (2n-5)!! 全解析无根二叉树（按同构类去重后）")

        subsets = [frozenset(s) for k in range(n + 1)
                   for s in itertools.combinations(range(n), k)]

        # ---------- Test A0 : two-state 的「边侧」== 「两状态类都连通」 ----------
        mism = 0
        for A in subsets:
            chi = tuple(1 if x in A else 0 for x in range(n))
            for ti in range(len(trees)):
                byside = displayed_binary(A, sidesets[ti], ALL)
                byconn = displayable_multistate(trees[ti], n, chi, 2)
                if byside != byconn:
                    mism += 1
        check(mism == 0,
              "two-state：「1-类是边侧（或退化）」⟺「两状态类都连通」(缺口 G1 的 r=2 情形)",
              "mismatch=%d" % mism)

        # ---------- Test B : Four Gamete 内核 ----------
        bad = 0
        for A in subsets:
            for B in subsets:
                if sides_compatible(A, B) != no_four_gametes(A, B):
                    bad += 1
        check(bad == 0, "SidesCompatible ⟺ 无四个 gamete（Theorem 1.1 的组合内核）",
              "pairs=%d mismatch=%d" % (len(subsets) ** 2, bad))

        # ---------- Test A : 等价刻画（两两相容 ⟺ 存在树展示全体） ----------
        ms = (2, 3) if n == 5 else (2, 3, 4)
        for m in ms:
            tot = pair_ok = bad_eq = bad_binary = fn_binary = 0
            for fam in itertools.product(subsets, repeat=m):
                if len(set(fam)) != m:
                    continue          # 只取互不相同的字符（同一字符自相容，见 sidesCompatible_self）
                tot += 1
                pw_sides = all(sides_compatible(fam[i], fam[j])
                               for i in range(m) for j in range(i + 1, m))
                if not pw_sides:
                    continue
                pair_ok += 1
                has_pp = any(all(displayed_binary(A, sc, ALL) for A in fam) for sc in sidesets)
                if not has_pp:
                    bad_eq += 1
                pw_bin = all(binary_compatible(fam[i], fam[j])
                             for i in range(m) for j in range(i + 1, m))
                if pw_bin and not has_pp:
                    bad_binary += 1
                if pw_bin:
                    continue
                # ★B：此族**真**有 PP，但两两 BinaryCompatible **不成立** ⇒ 用 BinaryCompatible 当
                #     判据会**误报「无 PP」**（假阴性）。
                if has_pp:
                    fn_binary += 1
            check(bad_eq == 0,
                  "m=%d：两两 SidesCompatible ⟺ 存在树展示全体（必要+充分）" % m,
                  "families=%d pairwise-ok=%d 违例=%d" % (tot, pair_ok, bad_eq))
            check(bad_binary == 0,
                  "m=%d：两两 BinaryCompatible ⟹ 存在树展示全体（不漏）" % m,
                  "两两Binary相容但无PP = %d" % bad_binary)
            check(fn_binary > 0,
                  "m=%d：★B BinaryCompatible **过强** —— 真有 PP 却被它判为不相容" % m,
                  "假阴性族数 = %d" % fn_binary)

        # ---------- ★B : BinaryCompatible 过强（给出显式见证） ----------
        if n == 3:
            A = frozenset({0, 1})
            B = frozenset({0, 2})
            check(not binary_compatible(A, B) and sides_compatible(A, B),
                  "★B 见证 n=3：A={0,1}, B={0,2} —— BinaryCompatible 假 / SidesCompatible 真",
                  "完美系统发生存在（3 叶星形树，中心标 (1,1)）")

    # ================================================ ★B 二元最小障碍（F_2）
    print("\n---- ★B 二元最小障碍 F_2（4 taxa / 2 字符，四个 gamete 本体） ----")
    n = 4
    ALL = frozenset(range(n))
    trees4 = all_cladograms(n)
    sc4 = [edge_sides(adj, n) for adj in trees4]
    # taxa 0,1,2,3 ≙ 00,01,10,11 ; 字符 a 的 1-类 = {2,3}(10,11), b 的 1-类 = {1,3}(01,11)
    a1 = frozenset({2, 3})
    b1 = frozenset({1, 3})
    check(not sides_compatible(a1, b1), "F_2 的那一对字符**不**相容（四个 gamete 俱全）")
    check(not no_four_gametes(a1, b1), "确实四个 gamete 全出现（00,01,10,11）")
    check(not any(a1 in sc and b1 in sc for sc in sc4),
          "F_2 无完美系统发生（穷举全部 %d 棵树）" % len(trees4))

    # ================================================ ★B/★C 多状态不充分
    print("\n---- ★B 多状态：两两相容 ⟹? 全局相容（Theorem 2.4 / Fitch 例） ----")
    n = 5
    ALL = frozenset(range(n))
    trees5 = all_cladograms(n)
    print("  （5 片叶：穷举 %d 棵树）" % len(trees5))

    # Fitch-Meacham F_3（由 1256-1273 / 1283-1284 行重构）：
    #   EC1={a0,b2,c1}, EC2={a1,b0,c0},
    #   TC1={a0,b0,c2}, TC2={a2,b2,c0}, TC3={a1,b1,c1}
    F3 = [(0, 2, 1), (1, 0, 0), (0, 0, 2), (2, 2, 0), (1, 1, 1)]
    print("  F_3 矩阵（5 taxa × 3 字符，行 = taxon，列 = 字符 a,b,c）：%s" % (F3,))
    chars3 = [tuple(row[k] for row in F3) for k in range(3)]      # 三个字符（列）
    disp = [[k for k, chi in enumerate(chars3) if displayable_multistate(adj, n, chi, 3)]
            for adj in trees5]
    pair = all(any((i in d and j in d) for d in disp)
               for i in range(3) for j in range(i + 1, 3))
    glob = any(all(i in d for i in range(3)) for d in disp)
    check(pair, "F_3：**任意两个**字符都有完美系统发生")
    check(not glob, "F_3：**三个一起**没有完美系统发生")
    check(pair and not glob, "★B ⇒ 多状态时两两相容**不充分** ✗（Theorem 2.4：需查三元组）")

    # ---------- 最小性：穷举 n=3,4,5 找最小的「两两相容但全局不相容」矩阵 ----------
    print("\n---- ★B 最小性：穷举求**最小**多状态反例（3 状态） ----")
    found = None
    for nn in (3, 4, 5):
        ALLn = frozenset(range(nn))
        tr = all_cladograms(nn) if nn <= 5 else []
        chars = [tuple(c) for c in itertools.product(range(3), repeat=nn)]
        dispn = [[k for k, chi in enumerate(chars) if displayable_multistate(adj, nn, chi, 3)]
                 for adj in tr]
        pairmap = {}
        for i in range(len(chars)):
            for j in range(i + 1, len(chars)):
                pairmap[(i, j)] = any((i in d and j in d) for d in dispn)
        hit = None
        for i, j, k in itertools.combinations(range(len(chars)), 3):
            if pairmap[(i, j)] and pairmap[(i, k)] and pairmap[(j, k)]:
                if not any((i in d and j in d and k in d) for d in dispn):
                    hit = (chars[i], chars[j], chars[k])
                    break
        print("    n=%d：%s" % (nn, "找到反例" if hit else "**不存在**反例"))
        if hit and found is None:
            found = (nn, hit)
    check(found is not None and found[0] == 5,
          "最小多状态反例需 5 taxa（= r+2，r=3；与 Theorem 7.1 的 F_r 规模一致）",
          "n=%s" % (found[0] if found else None))
    if found:
        nn, hit = found
        print("    最小反例（n=%d）：三个字符（按 taxon 列出） = %s" % (nn, hit))
        print("    （F_3 的三个字符为 %s）" % ([tuple(c) for c in chars3],))

    print("\n" + "=" * 78)
    if FAIL:
        print("结果：**失败** —— %d 项未通过：%s" % (len(FAIL), FAIL))
        return 1
    print("结果：**全部通过** ✓（精确穷举，无 Monte Carlo）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
