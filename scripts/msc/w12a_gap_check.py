#!/usr/bin/env python3
# W12a 反例检查 / 穷举复核：W11 登记的 6 个显式缺口，逐个核「命题是否为真」。
# 纯标准库、精确计数、无 Monte Carlo。运行：python3 w12a_gap_check.py
from itertools import combinations
from math import factorial
from collections import Counter

print("=" * 72)
print("W12a: 6 个登记缺口的命题真值复核（穷举，精确整数）")
print("=" * 72)


# ---------------------------------------------------------------- gap 1
def splits_of(n):
    """Split (Fin n) 的有向口径 = 非空真子集 A (= sideA)，B = A^c。"""
    universe = frozenset(range(n))
    out = []
    for k in range(1, n):
        for A in combinations(range(n), k):
            out.append((frozenset(A), universe - frozenset(A)))
    return out


def separates(r, Y0, Y1):
    A, B = r
    return (Y0 <= A and Y1 <= B) or (Y1 <= A and Y0 <= B)


print("\n[gap: card_trivial_splits_gap]  Split(Fin n) 有向平凡 split 计数 = 2n (n>=3)?")
for n in range(0, 8):
    sp = splits_of(n)
    triv = [r for r in sp if len(r[0]) == 1 or len(r[1]) == 1]
    pred = 2 * n
    flag = "OK " if (n >= 3 and len(triv) == pred) or (n < 3) else "!! "
    print(f"  {flag}n={n}: #{triv}={len(triv)}  2n={pred}  "
          f"{'(公式成立)' if len(triv) == pred else '(公式不成立! n<3 时退化)'}")

print("\n[gap: card_separates_four_gap]  Split(Fin 4) 分离三个 02|13,03|12,01|23 的各族 = 2?")
sp4 = splits_of(4)
for Y0, Y1 in [({0, 2}, {1, 3}), ({0, 3}, {1, 2}), ({0, 1}, {2, 3})]:
    fam = [r for r in sp4 if separates(r, Y0, Y1)]
    print(f"  分离 {sorted(Y0)}|{sorted(Y1)}: #{fam} = {len(fam)}  "
          f"{'OK' if len(fam) == 2 else '!! 不是 2'}  见证={[ (sorted(a), sorted(b)) for a,b in fam ]}")
print(f"  （Split(Fin 4) 总 {len(sp4)} 个 = 2*C(4,2)；三族两两不交且并 = 6）")

# ---------------------------------------------------------------- gap 2
print("\n[gap: multinomial_weight_count_gap]  #{s: weightOf s = w} * prod(w_i!) = n! ?")


def weight_of(s, n):
    return tuple(sum(1 for j in range(n) if s[j] == i) for i in range(n))


for n in range(1, 7):
    import itertools
    cnt = Counter()
    bad = 0
    for s in itertools.product(range(n), repeat=n):
        w = weight_of(s, n)
        if sum(w) != n:
            bad += 1
        cnt[w] += 1
    ok = True
    for w, c in cnt.items():
        lhs = c
        for wi in w:
            lhs *= factorial(wi)
        if lhs != factorial(n):
            ok = False
            print(f"  !! n={n} w={w} cnt={c} lhs={lhs} n!={factorial(n)}")
    print(f"  n={n}: {len(cnt)} 个不同权重向量，全部满足 cnt*prod(w_i!) = n!  -> {'OK' if ok else 'FAIL'}")
    print(f"        权重和恒 = n : {'OK' if bad == 0 else 'FAIL'}")

# ---------------------------------------------------------------- gap 3
print("\n[gap: rooted_tree_decidableEq_gap]  命题 = 「(forall T T', Decidable (T=T')) -> "
      "forall T T', T=T' or T != T'」")
print("  这是纯逻辑重言：假设本身即结论所需的判定程序（cases 消去 Decidable）。真。")

# ---------------------------------------------------------------- gap 4/5
print("\n[gap: iso_preserves_splits_gap]  Iso T T' -> (T.IsSplitOf s <-> T'.IsSplitOf s)")
print("  命题为真。（W12a 已建出零件 deleteEdgesIso；见报告）")

print("\n[gap: two_parent_trees_gap]  反例检查：把 T1=T2 代入")
print("  (i) 显示 prof：同一组条件，可满足；")
print("  (ii) split 系统：T2.IsSplitOf s <-> T1.IsSplitOf s，需 == T1.IsSplitOf (relabel sig s)；")
print("  (iii) 覆盖条件退化为 [T1 覆盖 T] or [T1 覆盖 T] = 「T1 的 split 系统 <= T 的」，")
print("        即「每个 parent tree 都含 T1 的全部 split」—— 这是原文 Figure 1 的分类定理本身，")
print("        **不是**本 Prop 里的日常重言。故本缺口**不可由构造 T1=T2 平凡解决**。")

# ---------------------------------------------------------------- Part III
print("\n" + "=" * 72)
print("Part III: 两个新接收缺口的 ★E 退化见证检查（它们都是 ∃ 抽象对象式登记）")
print("=" * 72)


def n_splits(n):
    """Split (Fin n) 的有向口径个数 = 非空真子集数 = 2^n - 2。"""
    return 2 ** n - 2


print("\n[gap: msc_split_probability_object_gap]  Displays := True 时可否平凡满足？")
print("  需要：sum_{r} P s r = 2(2n-3)，且平凡 split 上 P = 1（共 2n 个）。")
print("  剩余质量 = 2(2n-3) - 2n = 2n-6，必须 >= 0。")
for n in range(3, 11):
    triv = 2 * n
    total = n_splits(n)
    nontriv = total - triv
    target = 2 * (2 * n - 3)
    slack = target - triv
    ok = slack >= 0 and (slack == 0 or nontriv > 0)
    print(f"  n={n:2d}: #trivial={triv:3d}  #total={total:5d}  #nontrivial={nontriv:5d}  "
          f"target=2(2n-3)={target:4d}  剩余质量={slack:3d}  "
          f"{'OK(可平凡满足)' if ok else 'FAIL'}")
print("  => 结论：Displays:=True + (平凡上 1，其余平摊) 是【退化见证】。")
print("     终局判定 ⬜ 保留缺口：该 Prop 真但空转，不得据此宣布已证。")

print("\n[gap: bootstrap_confidence_gap]  Omega := PUnit, p := 点质量 可否平凡满足？")
print("  需要三条：0<=p<=1；1/2 < p w (TrueSplit w)；1/2 < p w s -> Compatible s (TrueSplit w)。")
print("  取 p w s = if s = TrueSplit w then 1 else 0（TrueSplit 常数）：")
print("   (a) 0<=p<=1            : OK（取值只 0/1）")
print("   (b) 1/2 < p w (TrueSplit w) = 1 : OK（1/2 < 1）")
print("   (c) 前提只对 s = TrueSplit w 成立，此时需 Compatible s s：")
print("       Compatible s s = (sideA 交 sideA 空) or (sideA 交 sideB 空) or ...")
print("       第二支 [Disjoint s.sideA s.sideB] **恒真**（split 的两侧按定义不交）=> OK")
sp4 = splits_of(4)
ok_self = all(not (len(a) == 0 or len(b) == 0) for a, b in sp4)
print(f"  实测：Split(Fin 4) 的 {len(sp4)} 个有向 split 全部两侧非空 = {ok_self}"
      f" => sideA 与 sideB 不交这一支恒可用")
print("  => 结论：【退化见证】存在，机器已验证（Lean `example` 在 Bootstrap.lean §6 内）。")
print("     终局判定 ⬜ 保留缺口：不得据此宣布已证；组件 ②③ 仍缺。")
print("\n  ⚠️ 组件① 现状更正（★D：docstring 判词不可信，已现查 Mathlib）：")
print("     ~/lean4phylo-t85/.lake/packages/mathlib/Mathlib/Probability/ProductMeasure.lean")
print("       `Measure.infinitePi` / `Measure.infinitePiNat` / `infinitePi_pi` / `infinitePi_cylinder`")
print("     ~/lean4phylo-t85/.lake/packages/mathlib/Mathlib/Probability/Independence/InfinitePi.lean")
print("       `iIndepFun_infinitePi`  (:124)")
print("     => 「本版 Mathlib 无无限乘积测度」**已过时**（EmpiricalConvergence.lean §4 缺口 K 需复核）。")

