#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W21 / C3 侦察：`SBD.two_parent_trees_core` 的有限内容。

★ 诚实状态：本脚本**只做穷举侦察**，为 Lean 形式化（手写/生成情形分析）提供**规模与结构**；
它本身**不是** Lean 证明，**不**作为缺口的证明。

模型（与 Lean 侧一一对应）：
  * taxon = 0..5（`Fin 6`）；
  * 一个 split「有向形态」由 `sideA` 决定（`sideB = sideAᶜ`）；
  * `SideDisplays(q, A) := (∃ p ∈ q, p ⊆ A) ∧ (∃ p' ∈ q, p' ⊆ Aᶜ)`（**朝向无关**，
    正对应 Lean 的 `DisplaysQP` 用某个 split `s` 的 `sideA = A` 展示 `q`）；
  * `Compatible(A, B) := A∩B=∅ ∨ A∩Bᶜ=∅ ∨ Aᶜ∩B=∅ ∨ Aᶜ∩Bᶜ=∅`
    （= Lean `Split.Compatible`，且**对两侧的补都不变**）。
"""
import itertools

N = 6
U = frozenset(range(N))


def compl(A):
    return U - A


def compat(A, B):
    return (not (A & B)) or (not (A & compl(B))) or (not (compl(A) & B)) or (not (compl(A) & compl(B)))


def nontrivial(A):
    return len(A) >= 2 and len(compl(A)) >= 2


# q1 = (12)(45) -> {0,1} vs {3,4}
# q2 = (34)(16) -> {2,3} vs {0,5}
# q3 = (56)(23) -> {4,5} vs {1,2}
Q1 = [frozenset({0, 1}), frozenset({3, 4})]
Q2 = [frozenset({2, 3}), frozenset({0, 5})]
Q3 = [frozenset({4, 5}), frozenset({1, 2})]


def side_displays(q, A):
    Ac = compl(A)
    return any(p <= A for p in q) and any(p <= Ac for p in q)


# ---- P1 / P2 的 sideA 集合（照 SupertreeLimits.lean 的 sP1a..sP2c）----
# sP1a = {2,3,4,5}, sP1b = {4,5}, sP1c = {2,3}
P1_BASE = [frozenset({2, 3, 4, 5}), frozenset({4, 5}), frozenset({2, 3})]
# sP2a = {3,4}, sP2b = {1,2}, sP2c = {1,2,3,4}
P2_BASE = [frozenset({3, 4}), frozenset({1, 2}), frozenset({1, 2, 3, 4})]


def closure(base):
    out = set()
    for A in base:
        out.add(A)
        out.add(compl(A))
    return out


FAM_P1 = closure(P1_BASE)
FAM_P2 = closure(P2_BASE)
FAM = FAM_P1 | FAM_P2
print("famP1 sideA 集合 =", sorted(tuple(sorted(a)) for a in FAM_P1))
print("famP2 sideA 集合 =", sorted(tuple(sorted(a)) for a in FAM_P2))


def main():
    allA = [frozenset(c) for r in range(N + 1) for c in itertools.combinations(range(N), r)]
    assert len(allA) == 64

    cand = {}
    for name, q in (("q1", Q1), ("q2", Q2), ("q3", Q3)):
        cs = [A for A in allA if side_displays(q, A) and nontrivial(A)]
        cand[name] = cs
        print(f"{name}: 候选 sideA 数 = {len(cs)} -> {sorted(tuple(sorted(a)) for a in cs)}")

    # 去重到「无向」代表（A 与 Aᶜ 视为同一 split）
    def unordered(cs):
        out, seen = [], set()
        for A in cs:
            key = min(tuple(sorted(A)), tuple(sorted(compl(A))))
            if key not in seen:
                seen.add(key)
                out.append(A)
        return out

    u1, u2, u3 = unordered(cand["q1"]), unordered(cand["q2"]), unordered(cand["q3"])
    print(f"无向代表数: q1 {len(u1)}, q2 {len(u2)}, q3 {len(u3)}")

    total = 0
    compatible_triples = []
    for A1 in u1:
        for A2 in u2:
            for A3 in u3:
                total += 1
                if compat(A1, A2) and compat(A1, A3) and compat(A2, A3):
                    compatible_triples.append((A1, A2, A3))
    print(f"无向有序三元组总数 = {total}，其中两两相容 = {len(compatible_triples)}")

    def fmt(A):
        return "{" + ",".join(str(x) for x in sorted(A)) + "}"

    bad = 0
    for (A1, A2, A3) in compatible_triples:
        print("  相容三元组:", fmt(A1), fmt(A2), fmt(A3),
              "| 三者在 famP1∪famP2 内:", all(a in FAM for a in (A1, A2, A3)))

    # 对每个相容三元组，求「与三者都相容的非平凡 split」全集
    print("\n--- 每个相容三元组下，「与三者都相容且非平凡」的 sideA 集合 ---")
    for (A1, A2, A3) in compatible_triples:
        S = [A for A in allA if nontrivial(A) and compat(A, A1) and compat(A, A2) and compat(A, A3)]
        outside = [A for A in S if A not in FAM]
        if outside:
            bad += 1
        print(f"  {fmt(A1)} {fmt(A2)} {fmt(A3)}: |S|={len(S)} 超出 famP1∪famP2={len(outside)}"
              + (f"  !! {[fmt(a) for a in outside]}" if outside else ""))
    print(f"\n>>> 反例三元组数 = {bad}（0 表示有限核心在『与三者都相容』口径下成立）")


if __name__ == "__main__":
    main()
