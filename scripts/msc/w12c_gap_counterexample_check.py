#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W12c —— 三个 W11 遗留缺口的 ★B 反例检查 / ★C 最小例子。
纯标准库、精确有理数/整数、无 Monte Carlo、无 numpy。

对应缺口（原文见 Phylo/Stat/ 下同名 `def ..._gap : Prop`）：

  I6  edgeInvariants_suffice_gap                 (Phylo/Stat/EdgeInvariants.lean:289)
  I3  evansSpeed_general_gap                     (Phylo/Stat/HadamardTransform.lean:323)
  I7  toricIdeal_generated_in_degree_le_four_gap (Phylo/Stat/ToricIdeals.lean:472)

[A] I3：`evansSpeed_general_gap` 是**纯重指标恒等式**（无树、无 GMM、π 不必是概率）。
    本脚本在若干有限交换群上**穷举所有满足两条公理的实值特征标**（`χ 0 = 1`、
    `χ(a+b) = χ a · χ b`），对 m = 1,2,3 精确有理数验证恒等式两侧相等。
    ⚠️ 注意：`Z/n`（n > 2）上**不存在**非平凡**实值**特征标
    （`χ(1)^n = 1` 且 `χ(1) ∈ ℝ` ⟹ `χ(1) = ±1`，再由 `χ(1)^n = 1` 得 `χ(1) = 1`）。
    非平凡实值特征标只出现在初等 2-群上（如 `(Z/2)^2`、`Z/2 × Z/4`）。
    （W12c 初版脚本的 bug：`allk` 是 tuple 却按 `allk[i % len(allk)]` 当列表取，
    于是 Z/2 的 m=1 只取到 k=(0,0)（平凡），且 Z/3/Z/4 上拿了不满足公理的 χ 去测恒等式。
    本版已改为：先建群、再穷举**所有**合法实值特征标、并显式检查公理。）

[B] I6：`edgeInvariants_suffice_gap` 按字面（对**任意** U、**任意** Model）量化 ⇒ **假**。
    见证 `δ_(0,1,0,1)`：展平秩 1（故所有 5×5 子式 = 0）且因子分解，但 `δ ≠ 0`。
    对应 Lean 已证定理 `Phylo.Stat.EdgeInvariants.edgeInvariants_suffice_gap_refuted`。

[C] I7：`ker φ` 的最小生成元次数。本脚本给出**结构刻画 + 小规模穷举**（见 §[C]），
    完整的 Graver 基计算（判定「生成元次数 ≤ 4」真伪）**未完成**，如实登记。
"""

import sys
from fractions import Fraction
from itertools import product

FAIL = []


def check(cond, msg):
    print(f"    [{'OK' if cond else 'FAIL'}] {msg}")
    if not cond:
        FAIL.append(msg)


# ==========================================================================
# [A] I3 : Evans-Speed identity
# ==========================================================================
def group_elems(mods):
    return list(product(*[range(m) for m in mods]))


def gadd(mods, a, b):
    return tuple((x + y) % m for x, y, m in zip(a, b, mods))


def real_characters(mods):
    """穷举所有满足 χ(0)=1、χ(a+b)=χ(a)χ(b) 的**实值**函数 χ : G → Q。"""
    G = group_elems(mods)
    zero = tuple(0 for _ in mods)
    out = []
    vals = list(product((Fraction(1), Fraction(-1)), repeat=len(G) - 1))
    for v in vals:
        chi = {zero: Fraction(1)}
        for g, x in zip([e for e in G if e != zero], v):
            chi[g] = x
        ok = all(chi[gadd(mods, a, b)] == chi[a] * chi[b] for a in G for b in G)
        ok = ok and all(chi[gadd(mods, a, zero)] == chi[a] for a in G)
        if ok:
            out.append(chi)
    return G, zero, out


def check_I3():
    print("=== [A] I3 evansSpeed_general_gap : exhaustive exact identity check ===")
    print("    (all REAL-valued characters satisfying chi(0)=1 and chi(a+b)=chi(a)chi(b))")
    for gname, mods in (("Z/2", (2,)), ("Z/3", (3,)), ("Z/4", (4,)),
                        ("(Z/2)^2", (2, 2)), ("Z/2 x Z/4", (2, 4))):
        G, zero, chars = real_characters(mods)
        nontriv = [c for c in chars if any(c[g] != 1 for g in G)]
        print(f"  -- {gname}: |G| = {len(G)}, #real characters = {len(chars)}, "
              f"#non-trivial = {len(nontriv)}")
        check(True, f"{gname}: character enumeration done "
                    f"({len(chars)} real characters, {len(nontriv)} non-trivial)")
        pi = {h: Fraction((h[0] + 1) * (3 if len(h) > 1 else 1) - 1) for h in G}
        for m in (1, 2, 3):
            # use non-trivial characters when available, else the trivial one
            pool = nontriv if nontriv else chars
            chis = [pool[i % len(pool)] for i in range(m)]
            hyp = all(chis[i][zero] == 1 for i in range(m)) and all(
                chis[i][gadd(mods, a, b)] == chis[i][a] * chis[i][b]
                for i in range(m) for a in G for b in G)
            check(hyp, f"{gname} m={m}: chi hypotheses hold"
                       f" ({'non-trivial' if nontriv else 'only trivial chars exist'})")
            f = [{a: Fraction((i + 1) * (a[0] + 2)) for a in G} for i in range(m)]
            lhs = Fraction(0)
            for g in product(G, repeat=m):
                inner = Fraction(0)
                for h in G:
                    pr = pi[h]
                    for i in range(m):
                        # -h == h for these 2-groups; for Z/3/Z/4 use the additive inverse
                        neg = tuple((-x) % mm for x, mm in zip(h, mods))
                        pr *= f[i][gadd(mods, g[i], neg)]
                    inner += pr
                ch = Fraction(1)
                for i in range(m):
                    ch *= chis[i][g[i]]
                lhs += inner * ch
            rhs = Fraction(0)
            for h in G:
                t = pi[h]
                for i in range(m):
                    t *= chis[i][h]
                rhs += t
            for i in range(m):
                rhs *= sum(f[i][a] * chis[i][a] for a in G)
            check(lhs == rhs, f"{gname} m={m}: LHS = {lhs} == RHS = {rhs} (exact)")
    print()


# ==========================================================================
# [B] I6 : counterexample to the literal statement
# ==========================================================================
def rank_exact(rows):
    M = [[Fraction(x) for x in row] for row in rows]
    n, mc = len(M), len(M[0])
    r = 0
    for c in range(mc):
        piv = next((i for i in range(r, n) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        for i in range(n):
            if i != r and M[i][c] != 0:
                fac = M[i][c] / pv
                for j in range(c, mc):
                    M[i][j] -= fac * M[r][j]
        r += 1
        if r == n:
            break
    return r


def check_I6():
    print("=== [B] I6 edgeInvariants_suffice_gap : FALSE as literally quantified ===")
    G4 = range(4)
    # delta_(0,1,0,1) : P i j k l = [i=0][j=1][k=0][l=1]
    P = lambda i, j, k, l: 1 if (i, j, k, l) == (0, 1, 0, 1) else 0
    F = [[P(i, j, k, l) for k in G4 for l in G4] for i in G4 for j in G4]
    rk = rank_exact(F)
    check(rk == 1, f"flattening rank of delta_(0,1,0,1) = {rk} (= 1 <= 4) "
                   f"=> all 5x5 minors vanish => every f in edgeIdeal vanishes at P")
    check(any(any(row) for row in F), "P is NOT the zero tensor")
    # explicit factorization P i j k l = sum_m A (i,j) m * B m (k,l)
    A = {(0, 1): 0}          # A((i,j),0) = [i=0][j=1]
    Bm = 0
    def Amat(p_):
        return Fraction(1) if p_ == (0, 1) else Fraction(0)
    def Bmat(kl):
        return Fraction(1) if kl == (0, 1) else Fraction(0)
    facts = {((i, j), (k, l)): Amat((i, j)) * Bmat((k, l))
             for i in G4 for j in G4 for k in G4 for l in G4}
    ok = all(facts[((i, j), (k, l))] == P(i, j, k, l)
             for i in G4 for j in G4 for k in G4 for l in G4)
    check(ok, "delta_(0,1,0,1) is Factorizable (A = E_(0,1), B = E_(0,1)), tensor rank 1")
    print("    => U := univ, Model := {zero tensor}, p := delta_(0,1,0,1):")
    print("       (p in Model) FALSE, (forall f in edgeIdeal, evalAt p f = 0) TRUE")
    print("       => the gap, quantified over ARBITRARY U and Model, is a FALSE Prop.")
    print("       Lean: `Phylo.Stat.EdgeInvariants.edgeInvariants_suffice_gap_refuted`")
    print("    repair: Casanellas Thm 4.4 (1528-1548) fixes the model family and takes")
    print("       p in U with U = the generic (regular) set; U = univ is NOT enough.")
    print("       Lean: `edgeInvariants_suffice_gap_correct_shape` (registered def).")
    print()


# ==========================================================================
# [C] I7 : structural facts about ker(phi)
# ==========================================================================
def xsum(g):
    s = 0
    for x in g:
        s ^= x
    return s


def check_I7(m=4, degmax=3):
    print("=== [C] I7 toricIdeal_generated_in_degree_le_four_gap : partial check ===")
    print("    setting: G4 = (Z/2)^2 = {0,1,2,3} (XOR); Coord m = {g : Fin m -> G4 | sum g = 0};")
    print("    phi(q_g) = prod_i Y(i, g_i)  =>  phi(T) = phi(T')  <=>  the per-column")
    print("    multisets of symbols agree (both sides are products of variables Y(i,chi)).")
    coords = [g for g in product(range(4), repeat=m) if xsum(g) == 0]
    print(f"    m = {m}: |Coord m| = {len(coords)} (degree-m monomials in the phi-image)")

    def phi_pow(T):
        """exponent vector of prod_k monomialOf(T k): key (i, symbol) -> count."""
        d = {}
        for g in T:
            for i in range(m):
                d[(i, g[i])] = d.get((i, g[i]), 0) + 1
        return tuple(sorted(d.items()))

    # exhaustive: equal phi-image <=> equal column multisets, for degrees 1..degmax
    bad = 0
    tot = 0
    for deg in range(1, degmax + 1):
        seen = {}
        for T in product(coords, repeat=deg):
            key = phi_pow(T)
            colkey = tuple(sorted((i, T[k][i]) for k in range(deg) for i in range(m)))
            if key in seen and seen[key] != colkey:
                bad += 1
            seen[key] = colkey
            tot += 1
    check(bad == 0, f"m={m}: for all tableaux of degree <= {degmax} (n={tot}), the phi-image "
                    f"is exactly determined by the per-column symbol multisets "
                    f"(mismatches: {bad})")
    print(f"    => ker phi is the *balanced-binomial* ideal (SS2005 Remark 16);")
    print(f"       degree <= 4 generation is NOT decided here.")
    print("    *** OPEN: the Graver/Markov basis of this semigroup has not been computed.")
    print("        A degree-d relation corresponds to a pair of multisets of `row types`")
    print("        (rows = elements of Coord m) with the same per-column counts; the ideal")
    print("        is generated in degree <= 4 iff every such pair is connected through")
    print("        degree-<=4 relations. Deciding this needs the semigroup's Graver basis")
    print("        (4ti2/Normaliz, or a hand-rolled enumeration) -- NOT available in the")
    print("        current library (no Groebner/Markov machinery). ***")
    print()


if __name__ == "__main__":
    check_I3()
    check_I6()
    check_I7()
    print("=" * 70)
    if FAIL:
        print(f"FAILURES: {len(FAIL)}")
        for f in FAIL:
            print("  -", f)
        sys.exit(1)
    print("ALL W12c CHECKS COMPLETED (I7's generation question remains OPEN)")
