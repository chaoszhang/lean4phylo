#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W21 / C3 侦察（第二轮）：验证**将写进 Lean 的精确形态**是否成立。

★ 诚实状态：本脚本**只做穷举侦察**，为 Lean 形式化提供规模判断与真值；
它**不是** Lean 证明，**不**作为缺口的证明。

将要写进 Lean 的形态：
  * `c1 : Fin 4 → Finset (Fin 6)`（`{0,1}` 朝向）
  * `c2 : Fin 4 → Finset (Fin 6)`（`{2,3}` 朝向）
  * `c3 : Fin 4 → Finset (Fin 6)`（`{4,5}` 朝向）
  * 归约引理（每 quartet 一条，1 量词 ⇒ Lean 里可 `decide`）：
      `SideDisplays q A → 2 ≤ |A| → 2 ≤ |Aᶜ| → ∃ i : Fin 4, A = c i ∨ A = (c i)ᶜ`
  * 主引理（3+1 量词：4·4·4·64 = 4096 ⇒ Lean 里 `decide` 应可行）：
      `∀ i j k B, SBC (c1 i) (c2 j) → SBC (c1 i) (c3 k) → SBC (c2 j) (c3 k) →
                  SBC B (c1 i) → SBC B (c2 j) → SBC B (c3 k) → B ∈ FAM_sideA`
    其中 `SBC` = 库内 `SidesCompatible`（= `A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ`），
    `FAM_sideA` = `famP1 ∪ famP2` 的全体 `sideA` 值（12 个）。
"""
import itertools

N = 6
U = frozenset(range(N))


def compl(A):
    return U - A


def sbc(A, B):
    """库内 `SidesCompatible` 的四种情形（等价于 Split.Compatible 的四交点口径）。"""
    return (A <= B) or (B <= A) or (not (A & B)) or (A | B == U)


def card(A):
    return len(A)


def side_displays(q, A):
    Ac = compl(A)
    return any(p <= A for p in q) and any(p <= Ac for p in q)


Q1 = [frozenset({0, 1}), frozenset({3, 4})]
Q2 = [frozenset({2, 3}), frozenset({0, 5})]
Q3 = [frozenset({4, 5}), frozenset({1, 2})]

C1 = [frozenset({0, 1}), frozenset({0, 1, 2}), frozenset({0, 1, 5}), frozenset({0, 1, 2, 5})]
C2 = [frozenset({2, 3}), frozenset({1, 2, 3}), frozenset({2, 3, 4}), frozenset({1, 2, 3, 4})]
C3 = [frozenset({4, 5}), frozenset({0, 4, 5}), frozenset({3, 4, 5}), frozenset({0, 3, 4, 5})]

P1_BASE = [frozenset({2, 3, 4, 5}), frozenset({4, 5}), frozenset({2, 3})]
P2_BASE = [frozenset({3, 4}), frozenset({1, 2}), frozenset({1, 2, 3, 4})]


def closure(base):
    out = set()
    for A in base:
        out.add(A)
        out.add(compl(A))
    return out


FAM = closure(P1_BASE) | closure(P2_BASE)


def fmt(A):
    return "{" + ",".join(str(x) for x in sorted(A)) + "}"


def main():
    allA = [frozenset(c) for r in range(N + 1) for c in itertools.combinations(range(N), r)]

    # ---- 检验 1：候选归约引理 ----
    print("=== 检验 1：候选归约（∃ i : Fin 4, A = c i ∨ A = (c i)ᶜ） ===")
    for name, q, C in (("q1", Q1, C1), ("q2", Q2, C2), ("q3", Q3, C3)):
        bad = []
        for A in allA:
            if side_displays(q, A) and card(A) >= 2 and card(compl(A)) >= 2:
                if not any(A == c or A == compl(c) for c in C):
                    bad.append(A)
        print(f"  {name}: 遗漏 = {len(bad)} {[fmt(a) for a in bad]}")

    # ---- 检验 2：主引理 ----
    print("\n=== 检验 2：主引理（4·4·4·64 全枚举） ===")
    bad = 0
    total = 0
    for i in range(4):
        for j in range(4):
            for k in range(4):
                for B in allA:
                    total += 1
                    A1, A2, A3 = C1[i], C2[j], C3[k]
                    if not (sbc(A1, A2) and sbc(A1, A3) and sbc(A2, A3)):
                        continue
                    if not (card(B) >= 2 and card(compl(B)) >= 2):
                        continue
                    if not (sbc(B, A1) and sbc(B, A2) and sbc(B, A3)):
                        continue
                    if B not in FAM:
                        bad += 1
                        print(f"  !! 反例 i={i} j={j} k={k} B={fmt(B)}")
    print(f"  枚举总数 = {total}，反例 = {bad}")

    # ---- 检验 3：主引理去掉「三者两两相容」前提后是否仍真（决定 Lean 假设面） ----
    print("\n=== 检验 3：去掉三者两两相容前提后 ===")
    bad2 = 0
    for i in range(4):
        for j in range(4):
            for k in range(4):
                for B in allA:
                    A1, A2, A3 = C1[i], C2[j], C3[k]
                    if not (card(B) >= 2 and card(compl(B)) >= 2):
                        continue
                    if not (sbc(B, A1) and sbc(B, A2) and sbc(B, A3)):
                        continue
                    if B not in FAM:
                        bad2 += 1
    print(f"  反例 = {bad2}  ⇒ "
          + ("必须保留『三者两两相容』前提" if bad2 else "前提可去掉"))


if __name__ == "__main__":
    main()
