#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W21 / C3 侦察（第三轮）：**加强形态** —— 能否做到「恰是 P1 或 P2」。

★ 诚实状态：只做穷举侦察，**不是** Lean 证明，**不**作为缺口的证明。

要验证的三条（都将是 Lean 里的 `decide` 引理）：
  L1 候选归约（每 quartet 一条）：`SideDisplays q A ∧ 2 ≤ |A| ∧ 2 ≤ |Aᶜ| → ∃ i : Fin 4, A = c i ∨ A = (c i)ᶜ`
  L2 三元组分类（`Fin 4 × Fin 4 × Fin 4`）：两两相容的三元组**必**是
       `{c1 i 类, c2 j 类, c3 k 类} = P1 的三条` 或 `= P2 的三条`（无序口径）
  L3 强化的有限核心（每情形一条，1 量词）：
       `SBC B {0,1} → SBC B {2,3} → SBC B {4,5} → 2 ≤ |B| → 2 ≤ |Bᶜ| → B ∈ FAM_P1_sideA`
       （P2 情形同理）—— 若成立，则「非平凡 split 系统恰是 T₁ 的或 T₂ 的」**双向**都到手。
"""
import itertools

N = 6
U = frozenset(range(N))


def compl(A):
    return U - A


def sbc(A, B):
    return (A <= B) or (B <= A) or (not (A & B)) or (A | B == U)


def nt(A):
    return len(A) >= 2 and len(compl(A)) >= 2


def same_unordered(A, B):
    return A == B or A == compl(B)


def side_displays(q, A):
    Ac = compl(A)
    return any(p <= A for p in q) and any(p <= Ac for p in q)


Q1 = [frozenset({0, 1}), frozenset({3, 4})]
Q2 = [frozenset({2, 3}), frozenset({0, 5})]
Q3 = [frozenset({4, 5}), frozenset({1, 2})]

C1 = [frozenset({0, 1}), frozenset({0, 1, 2}), frozenset({0, 1, 5}), frozenset({0, 1, 2, 5})]
C2 = [frozenset({2, 3}), frozenset({1, 2, 3}), frozenset({2, 3, 4}), frozenset({1, 2, 3, 4})]
C3 = [frozenset({4, 5}), frozenset({0, 4, 5}), frozenset({3, 4, 5}), frozenset({0, 3, 4, 5})]

# famP1 / famP2 的 sideA 值（照 SupertreeLimits.lean 的 sP1a..sP2c）
FAM_P1 = set()
for A in [frozenset({2, 3, 4, 5}), frozenset({4, 5}), frozenset({2, 3})]:
    FAM_P1 |= {A, compl(A)}
FAM_P2 = set()
for A in [frozenset({3, 4}), frozenset({1, 2}), frozenset({1, 2, 3, 4})]:
    FAM_P2 |= {A, compl(A)}

# P1 / P2 的无序代表（用来做 L2 的结论）
REP_P1 = (frozenset({0, 1}), frozenset({2, 3}), frozenset({4, 5}))
REP_P2 = (frozenset({3, 4}), frozenset({0, 5}), frozenset({1, 2}))


def fmt(A):
    return "{" + ",".join(str(x) for x in sorted(A)) + "}"


def main():
    allA = [frozenset(c) for r in range(N + 1) for c in itertools.combinations(range(N), r)]

    print("=== L1 候选归约 ===")
    for name, q, C in (("q1", Q1, C1), ("q2", Q2, C2), ("q3", Q3, C3)):
        bad = [A for A in allA
               if side_displays(q, A) and nt(A)
               and not any(A == c or A == compl(c) for c in C)]
        print(f"  {name}: 遗漏 = {len(bad)}")

    print("\n=== L2 三元组分类（无向无序代表） ===")
    bad2 = 0
    compat = []
    for i in range(4):
        for j in range(4):
            for k in range(4):
                A1, A2, A3 = C1[i], C2[j], C3[k]
                if sbc(A1, A2) and sbc(A1, A3) and sbc(A2, A3):
                    compat.append((C1[i], C2[j], C3[k]))
                    ok1 = same_unordered(A1, REP_P1[0]) and same_unordered(A2, REP_P1[1]) and same_unordered(A3, REP_P1[2])
                    ok2 = same_unordered(A1, REP_P2[0]) and same_unordered(A2, REP_P2[1]) and same_unordered(A3, REP_P2[2])
                    if not (ok1 or ok2):
                        bad2 += 1
                        print(f"  !! {fmt(A1)} {fmt(A2)} {fmt(A3)}")
    print(f"  相容三元组数 = {len(compat)}，不落入 P1/P2 类 = {bad2}")

    print("\n=== L3 强化有限核心（恰是 P1 / 恰是 P2） ===")
    for name, reps, target, tname in (
            ("P1", (frozenset({0, 1}), frozenset({2, 3}), frozenset({4, 5})), FAM_P1, "FAM_P1"),
            ("P2", (frozenset({3, 4}), frozenset({0, 5}), frozenset({1, 2})), FAM_P2, "FAM_P2")):
        S = [B for B in allA
             if nt(B) and all(sbc(B, r) for r in reps)]
        outside = [B for B in S if B not in target]
        missing = [B for B in target if B not in S]
        print(f"  {name} 情形: |S| = {len(S)} | |{tname}| = {len(target)}"
              f" | S ⊄ {tname} = {len(outside)} | {tname} ⊄ S = {len(missing)}"
              + (f"  超出={[fmt(a) for a in outside]}" if outside else "")
              + (f"  缺={[fmt(a) for a in missing]}" if missing else ""))
        if not outside and not missing:
            print(f"    ⇒ ★ S 恰为 {tname} ✓（双向成立）")


if __name__ == "__main__":
    main()
