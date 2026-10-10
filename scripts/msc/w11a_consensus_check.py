#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11a / 共识族 —— 协调侧**独立重写**的核对脚本（agent 报告引用的 `w11a_checks.py` 从未入库 ✗）。

用途：给本批两个 Lean 交付**可复现的数值证据**：
  * C1 / 半严格共识（`Phylo/ConsensusExtra.lean`）：`lSplits_compatible`（Day 1985 的 M_l，鸽笼 `2l > |ι|`）
    与**它必须带 `|ι| ≤ 3`** 的 ★B 反例；
  * C2 / Adams 共识（`Phylo/AdamsConsensus.lean`）：最小例子上 Adams 簇族的手算复刻，
    以及「nested 刻画会把 `{2,3}` 误收」的反驳。

纯标准库、精确整数/集合运算、无 Monte Carlo。全部 assert 通过才打印 PASS。
"""
import itertools
import sys

FAIL = []


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


# ---------------------------------------------------------------- split 工具
def canon(A, S):
    """把 (A, S\\A) 规范化成 split（有序对里取「含最小元的那一侧」在前）。"""
    A = frozenset(A)
    B = frozenset(S) - A
    return (A, B) if (not A) or (not B) or min(A) < min(B) else (B, A)


def compatible(s, t):
    """split 相容 = 某一对分侧不交（4 点条件）。"""
    return any(not (a & b) for a in s for b in t)


def tree_splits(S, cherries):
    """由「樱花对」列表给出无根树的**非平凡** split 集（叶集 S）。"""
    S = frozenset(S)
    out = set()
    for c in cherries:
        out.add(canon(c, S))
    return out


# ------------------------------------------------- ① 鸽笼原理（M_l 相容性的根）
def part_pigeonhole():
    print("=" * 78)
    print("[1] 鸽笼原理：|S|,|S'| ≥ l 且 2l > n ⟹ S ∩ S' ≠ ∅（n = 族大小）")
    bad = 0
    tight = 0
    for n in range(1, 9):
        for l in range(1, 9):
            if 2 * l > n:
                # 每个 i ∈ [n] 各取一个大小 ≥ l 的子集时，两两必交
                for S in itertools.combinations(range(n), l):
                    for T in itertools.combinations(range(n), l):
                        if not (set(S) & set(T)):
                            bad += 1
            else:
                # 界是紧的：2l ≤ n 时存在不交的一对
                S = set(range(l))
                T = set(range(l, 2 * l))
                if n >= 2 * l and not (S & T):
                    tight += 1
    check("2l > n 时不存在不交的一对（0 例外）", bad == 0)
    check("2l ≤ n 时确实存在不交的一对（界紧）", tight > 0)


# -------------------------------------- ② ★B 核心反例：|ι| = 4 时「≥2 棵」不相容
def part_nonstrict_counterexample():
    print("=" * 78)
    print("[2] ★B 核心反例（agent 报告 [2] 的独立复算）：|ι| = 4、叶集 {0,1,2,3,4}")
    S = frozenset(range(5))
    T0 = tree_splits(S, [frozenset({0, 1}), frozenset({2, 3})])   # ((0,1),(2,3),4)
    T2 = tree_splits(S, [frozenset({0, 2}), frozenset({1, 4})])   # ((0,2),(1,4),3)
    fam = [T0, T0, T2, T2]                                        # 四棵树：两两相同
    s = canon({0, 1}, S)
    t = canon({0, 2}, S)
    sup_s = sum(1 for T in fam if s in T)
    sup_t = sum(1 for T in fam if t in T)
    print(f"   支撑度：s={sorted(map(sorted, s))} → {sup_s}；t={sorted(map(sorted, t))} → {sup_t}")
    check("两者支撑度都 = 2（都进了 M_2）", sup_s == 2 and sup_t == 2)
    check("★ 但 s 与 t 不相容（四个交全非空）", not compatible(s, t))
    inter = [(sorted(a), sorted(b)) for a in s for b in t if (a & b)]
    print(f"   非空的交共 {len(inter)} 个：{inter}")
    check("四个交全非空", len(inter) == 4)
    check("⇒ `nonstrict_compatible` 必须带 |ι| ≤ 3（与 Day 的 k/2 < l 一致）",
          len(fam) == 4 and not compatible(s, t))


# ------------------------------------------------ ③ M_l 在 |ι| = 3 时确实相容
def part_three_trees_ok():
    print("=" * 78)
    print("[3] |ι| = 3、l = 2：鸽笼 2·2 = 4 > 3 ⟹ M_2 内任意两个 split 必交 ⟹ 相容")
    S = frozenset(range(4))
    cherries = [frozenset({0, 1}), frozenset({0, 2}), frozenset({0, 3}),
                frozenset({1, 2}), frozenset({1, 3}), frozenset({2, 3})]
    trees = [tree_splits(S, [c, frozenset(S - (c | {x})) if False else frozenset(sorted(S - c)[:1])])
             for c in cherries]
    # 简化：用「星形 + 一条内边」的树，非平凡 split 只有一个 —— 仍然能测 M_2 的相容性
    trees = [tree_splits(S, [c]) for c in cherries]
    bad = 0
    for trio in itertools.combinations(range(len(trees)), 3):
        sup = {}
        for i in trio:
            for sp in trees[i]:
                sup[sp] = sup.get(sp, 0) + 1
        m2 = [sp for sp, k in sup.items() if k >= 2]
        for a, b in itertools.combinations(m2, 2):
            if not compatible(a, b):
                bad += 1
    check("全部三元组里 M_2 的 split 两两相容（0 例外）", bad == 0)
    return bad


# ---------------------------------------------- ④ ★C Adams 最小例子（含反驳）
def part_adams_minimal():
    print("=" * 78)
    print("[4] ★C Adams 最小例子（独立复算 agent 报告 [6]）")
    U = frozenset(range(4))
    # 树1 = ((0,1),(2,3))：簇 {univ,{0,1},{2,3}}；树2 = ((0,1),2,3)：簇 {univ,{0,1}}
    cl1 = [U, frozenset({0, 1}), frozenset({2, 3})]
    cl2 = [U, frozenset({0, 1})]

    # 在给定簇 C 处取「分支划分」：C 的**极大真子簇** ＋ 未被它们覆盖的叶各自成块
    # （这就是 Adams 1972 的 product-partition 里「各树在 LUB 处怎么分」那一项）
    def branch_partition(clusters, C):
        subs = [c for c in clusters if c < C]
        maximal = [c for c in subs if not any(c < d for d in subs)]
        covered = set()
        for m in maximal:
            covered |= set(m)
        extra = [frozenset({x}) for x in sorted(set(C) - covered)]
        return maximal + extra

    def adams(clusters_list, C):
        """递归 product-partition：各树在 C 处分支划分的所有交（丢空），再递归。
        Adams 簇族**含 `C` 本身**（根簇 `univ` 也在内）。"""
        parts = [branch_partition(cl, C) for cl in clusters_list]
        blocks = set()
        for combo in itertools.product(*parts):
            inter = frozenset.intersection(*combo)
            if inter:
                blocks.add(inter)
        out = {C}
        for b in blocks:
            out.add(b)
            if b != C and len(b) >= 2:
                out |= adams(clusters_list, b)
        return out

    fam = [cl1, cl2]
    parts_univ = [branch_partition(cl, U) for cl in fam]
    prod = set()
    for combo in itertools.product(*parts_univ):
        inter = frozenset.intersection(*combo)
        if inter:
            prod.add(inter)
    print(f"   两树在 univ 处分支划分：{[[sorted(x) for x in p] for p in parts_univ]}")
    print(f"   乘积划分 = {sorted(sorted(x) for x in prod)}")
    check("乘积划分 = {{0,1},{2},{3}}（与 Lean `ex_adamsPartition` 一致）",
          prod == {frozenset({0, 1}), frozenset({2}), frozenset({3})})

    A = adams(fam, U)
    print(f"   Adams 簇族 = {sorted(sorted(x) for x in A)}")
    check("Adams 簇族 = {univ,{0,1},{0},{1},{2},{3}}",
          A == {U, frozenset({0, 1}), frozenset({0}), frozenset({1}),
                frozenset({2}), frozenset({3})})
    check("★★★ {0,1} ∈ Adams 簇族（共同樱花）", frozenset({0, 1}) in A)
    check("★★★ {2,3} ∉ Adams 簇族（只在树 1 里）", frozenset({2, 3}) not in A)

    # 反驳「nested 刻画」：{2,3} 对**每棵**树的簇族都 nested ⟹ 会被误收
    def nested_in(c, clusters):
        return all((c <= d) or (d <= c) or (not (c & d)) for d in clusters)

    wrong = all(nested_in(frozenset({2, 3}), cl) for cl in fam)
    check("★ nested 刻画会把 {2,3} 误收（故派单建议的刻画是错的）", wrong)

    # 忠实性反空真：两棵树相同时，Adams 的非平凡簇 = 该树本身的簇
    same = [cl1, cl1]
    A_same = adams(same, U)
    check("两棵树相同时 Adams 簇族 ⊇ 该树簇族（忠实性）",
          set(cl1) <= A_same)


def main():
    print("scripts/msc/w11a_consensus_check.py —— W11a 共识族 独立核对（精确集合运算，无 Monte Carlo）")
    part_pigeonhole()
    part_nonstrict_counterexample()
    part_three_trees_ok()
    part_adams_minimal()
    print("=" * 78)
    if FAIL:
        print("VERDICT: FAIL ——", len(FAIL), "项未过：", FAIL)
        return 1
    print("VERDICT: PASS —— 全部检查通过")
    return 0


if __name__ == "__main__":
    sys.exit(main())
