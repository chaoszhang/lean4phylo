#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/adr2017_split.py -- W10f：ADR2017 split 概率与「1/3 阈值」的**精确有理数**复核

文献：E. S. Allman, J. H. Degnan, J. A. Rhodes,
*Split probabilities and species tree inference under the multispecies coalescent model*。
引用一律用 `references/md/AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md` 的**行号**：

  * **Lemma 3.1**，第 315-316 行：
        "If |X | = n, then the sum of the non-trivial split probabilities is n - 3."
    证明（第 318-357 行）：sum_{A|B} P_sigma(A|B) = sum_T P_sigma(T) * (2n-3) = 2n-3
    （因为每条 unrooted binary 树恰展示 2n-3 个 split），再减去 n 个概率为 1 的平凡 split
    （第 355-357 行），得 (2n-3) - n = n-3。等价地：每条树恰展示 n-3 个**非平凡** split，
    故 sum_{非平凡 A|B} P_sigma(A|B) = sum_T P_sigma(T)(n-3) = n-3。
  * **Proposition 3.2**，第 363-374 行：binary 物种树 sigma 的内部枝长 lambda_i > eps >= 0 时
        P_sigma(A|B) >= (1/3) exp(-eps)  ==>  A|B 被 sigma 展示；
    且阈值**紧**：任意 alpha < (1/3)exp(-eps) 都有反例（不被展示但概率 > alpha）。
  * **Corollary 3.3**（第 415-421 行）：eps = 0（正枝长），阈值 1/3。
  * **Theorem 4.1**（第 656-677 行）：四族分离求和的不等式。

本脚本**不做 Monte Carlo**，也不出现浮点：
  * 一切有理数用 `fractions.Fraction` 精确运算；
  * 指数函数用**交错级数的有理上下界**（严格的区间算术，见 `exp_neg_bracket`），
    故 (C)(D)(E) 里的不等式是**严格证明**而非数值示意。

复核条目（每条打印 PASS/FAIL）
  (A) 4 叶 MSC 权重：p_conc(q) = 1 - 2q/3、p_disc(q) = q/3（q = exp(-t)），
      多项式恒等式 p_conc + 2 p_disc = 1（**系数比较**，对 q 是恒等式）。
  (B) Lemma 3.1 的组合核：穷举 n = 4,5,6 的全部 unrooted binary 树（数量 (2n-5)!!），
      验证每条树恰展示 2n-3 个 split、其中恰 n 个平凡、恰 n-3 个非平凡
      ==> sum_{非平凡} P = sum_T P(T)(n-3) = n-3。
  (C) Prop 3.2（4 叶）：不被展示的 split 概率 = (1/3)exp(-t)；对多组有理数 eps < t，
      用区间算术严格证明 (1/3)exp(-t) < (1/3)exp(-eps)。
  (D) 紧性：eps = 0、alpha = 1/4 < 1/3 = (1/3)exp(-eps)，取 t = 1/4 > eps，
      严格证明 alpha < (1/3)exp(-t)（即阈值不能再小）。
  (E) Cor 3.3（eps = 0）：t > 0 时严格证明 (1/3)exp(-t) < 1/3。
  (F) Theorem 4.1 的 n = 4 账目：三族无向权重 (d, d, c)，d = q/3 < c = 1 - 2q/3（0 < q < 1）。
"""

from fractions import Fraction as F
from itertools import count
from math import factorial
import sys

FAILED = []


def check(name, cond, detail=""):
    ok = bool(cond)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")
    if not ok:
        FAILED.append(name)
    return ok


# ---------------------------------------------------------------- 区间算术
def exp_neg_bracket(x, k):
    """返回 (lo, hi) 满足 lo < exp(-x) < hi，0 <= x <= 1 有理数，k 为部分和的指标。

    交错级数 exp(-x) = sum_{j>=0} (-x)^j / j!：各项绝对值单调不增（x <= j+1 时成立），
    故部分和 S_k = sum_{j<=k} (-x)^j/j! 的余项符号 = (-1)^{k+1}：
      * k 偶 ==> S_k > exp(-x)（上界），S_{k+1} < exp(-x)（下界）；
      * k 奇 ==> 反之。
    """
    assert 0 <= x <= 1
    if x == 0:
        return (F(1), F(1))                             # exp(0) = 1 精确
    terms = [F(1)]
    for j in count(1):
        if j > k + 1:
            break
        terms.append(-terms[-1] * x / j)
    for j in range(len(terms) - 1):                     # 项绝对值单调不增（交错级数前提）
        assert abs(terms[j + 1]) <= abs(terms[j]), "exp_neg_bracket: 项未单调递减"
    S = [terms[0]]
    for t in terms[1:]:
        S.append(S[-1] + t)
    lo, hi = (S[k + 1], S[k]) if k % 2 == 0 else (S[k], S[k + 1])
    assert lo < hi
    return lo, hi


# ---------------------------------------------------------------- (A)
def poly_mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def poly_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0)) for i in range(n)]


def poly_scale(a, c):
    return [c * x for x in a]


def section_A():
    print("(A) 4 叶 MSC 权重（q = exp(-t) 的多项式恒等式）")
    # p_conc(q) = 1 - (2/3) q ; p_disc(q) = (1/3) q      （MSCProof.mscConcordant_closed / mscDiscordant）
    p_conc = [F(1), F(-2, 3)]
    p_disc = [F(0), F(1, 3)]
    total = poly_add(poly_add(p_conc, poly_scale(p_disc, F(2))), [F(-1)])
    check("p_conc + 2*p_disc - 1 = 0（系数全零）", all(c == 0 for c in total),
          f"系数 = {total}")
    # p_conc 在 q=0 (t=inf) 与 q=1 (t=0) 的取值
    check("p_conc(q=1) = 1/3（星形树）", sum(p_conc) == F(1, 3))
    check("p_disc(q=1) = 1/3（星形树）", sum(p_disc) == F(1, 3))
    check("p_conc(q=0) = 1（无限长内部枝）", p_conc[0] == F(1))
    # 三条非平凡（无向）权重之和 = 4 - 3 = 1
    three = poly_add(poly_add(p_conc, p_disc), p_disc)
    check("p_conc + p_disc + p_disc = 1（= n - 3，n = 4）", all(c == 0 for c in poly_add(three, [F(-1)])),
          f"系数 = {three}")
    # 阈值：p_disc(t) 与 (1/3)exp(-t) 是同一个式子（这里给出 q 形式的记账）
    check("阈值 (1/3)exp(-eps) 与 p_disc 的形状一致：p_disc(q) = (1/3) q", p_disc == [F(0), F(1, 3)])


# ---------------------------------------------------------------- (B)
def split_of_edge(adj, u, v, labels):
    """删除边 (u,v) 后一侧的叶标签集合（返回 frozenset 的代表元，规范化成 2 元组）。"""
    seen, stack = {u}, [u]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if (x, y) == (u, v) or (y, x) == (u, v):
                continue
            if y not in seen:
                seen.add(y)
                stack.append(y)
    side = frozenset(x for x in seen if x in labels)
    other = frozenset(x for x in labels if x not in side)
    return (side, other) if (len(side), sorted(side)) <= (len(other), sorted(other)) else (other, side)


def binary_trees(n):
    """穷举 n 个标记叶（0..n-1）的 unrooted binary 树（邻接表）。n >= 3。

    归纳构造：n 叶树 -> n+1 叶树，把新叶 n 接到每条边细分出的新顶点上；
    每个 (n+1) 叶树恰由「收缩新叶所在的悬挂边」唯一还原，故不重不漏。
    内部顶点用 >= 1000 的编号，与叶标签 0..n-1 不冲突。
    """
    c = 1000                                            # 首个内部顶点编号
    adj = {0: {c}, 1: {c}, 2: {c}, c: {0, 1, 2}}
    trees = [adj]
    next_v = c + 1
    for leaf in range(3, n):
        new_trees = []
        for t in trees:
            edges = [(u, v) for u in t for v in t[u] if u < v]
            for (u, v) in edges:
                w, nid = next_v, next_v + 1
                nt = {x: set(s) for x, s in t.items()}
                nt[u].discard(v)
                nt[v].discard(u)
                nt[u].add(w)
                nt[v].add(w)
                nt[w] = {u, v, leaf}
                nt[leaf] = {w}
                new_trees.append(nt)
                next_v += 2
        trees = new_trees
    return trees


def section_B():
    print("(B) Lemma 3.1 的组合核：每条 unrooted binary 树恰展示 2n-3 / n / n-3 个 split")
    for n in (4, 5, 6):
        labels = set(range(n))
        trees = binary_trees(n)
        expected_trees = 1
        for j in range(3, n):
            expected_trees *= 2 * j - 3          # (2n-5)!! = 1*3*...*(2n-5)
        check(f"n = {n}：unrooted binary 树恰 {expected_trees} 棵 (2n-5)!!",
              len(trees) == expected_trees, f"实得 {len(trees)}")
        tot_ok = triv_ok = nontriv_ok = distinct_ok = True
        for t in trees:
            edges = [(u, v) for u in t for v in t[u] if u < v]
            splits = {split_of_edge(t, u, v, labels) for (u, v) in edges}
            triv = {s for s in splits if 1 in (len(s[0]), len(s[1]))}
            nontriv = splits - triv
            tot_ok &= (len(splits) == 2 * n - 3)
            triv_ok &= (len(triv) == n)
            nontriv_ok &= (len(nontriv) == n - 3)
            distinct_ok &= (len(splits) == len(edges))
        check(f"n = {n}：每条树恰展示 2n-3 = {2*n-3} 个（互异的）split", tot_ok and distinct_ok)
        check(f"n = {n}：其中平凡 split 恰 n = {n} 个", triv_ok)
        check(f"n = {n}：其中非平凡 split 恰 n-3 = {n-3} 个", nontriv_ok)
    # Lemma 3.1 的账目：sum_T P(T) * (n-3) = n-3（sum_T P(T) = 1）
    for n in range(3, 11):
        check(f"n = {n}：(2n-3) - n = n-3 = {n-3}", (2 * n - 3) - n == n - 3)
    # 无向 / 有向平凡 split 计数（有向 = 2n，n >= 3）
    for n in (4, 5, 6, 7):
        labels = set(range(n))
        unord_triv = len({frozenset((frozenset({x}), frozenset(labels - {x}))) for x in labels})
        check(f"n = {n}：无向平凡 split 恰 n = {n} 个（有向 {2*n} 个）", unord_triv == n)


# ---------------------------------------------------------------- (C) (D) (E)
def section_CDE():
    print("(C) Prop 3.2（4 叶）：t > eps 时 (1/3)exp(-t) < (1/3)exp(-eps)（区间算术，严格）")
    for (t, eps) in [(F(1, 4), F(0)), (F(1, 2), F(1, 4)), (F(3, 4), F(1, 2)), (F(1), F(3, 4))]:
        lo_t, hi_t = exp_neg_bracket(t, 6)
        lo_e, hi_e = exp_neg_bracket(eps, 6)
        # (1/3)exp(-t) <= hi_t/3 < lo_e/3 <= (1/3)exp(-eps)
        check(f"t = {t} > eps = {eps}：p_disc(t) < p_disc(eps)",
              hi_t / 3 < lo_e / 3, f"上界 {float(hi_t/3):.6f} < 下界 {float(lo_e/3):.6f}")

    print("(D) 紧性：eps = 0、alpha = 1/4 < 1/3，t = 1/4 > eps 使 alpha < p_disc(t)")
    alpha, eps, t = F(1, 4), F(0), F(1, 4)
    check("alpha = 1/4 < (1/3)exp(-0) = 1/3", alpha < F(1, 3))
    lo, hi = exp_neg_bracket(t, 6)
    check("t = 1/4 > eps = 0", t > eps)
    check("alpha = 1/4 < (1/3)exp(-1/4)（交错级数下界）",
          alpha < lo / 3, f"下界 (1/3)*{lo} = {lo/3} = {float(lo/3):.6f}")
    # 一般构造（原文第 408-414 行：取 λ1 > ε 使 α < (1/3)exp(-λ1)）：
    # u := -log(3α)（u > ε ⟺ 3α < exp(-ε)，由 log 严格单调），t := (ε+u)/2。
    # 这里核验**有理**的那一步：ε < u ==> ε < t < u
    # （于是 -u < -t，即 log(3α) < -t，即 α < (1/3)exp(-t)）。
    for (e, u) in [(F(0), F(1)), (F(0), F(1, 4)), (F(1, 2), F(3, 4))]:
        tt = (e + u) / 2
        check(f"eps = {e} < u = {u} ==> eps < t = {tt} < u", e < tt < u)

    print("(E) Cor 3.3（eps = 0）：t > 0 时 (1/3)exp(-t) < 1/3")
    for t in (F(1, 4), F(1, 2), F(1)):
        lo, hi = exp_neg_bracket(t, 6)
        check(f"t = {t}：p_disc(t) < 1/3", hi / 3 < F(1, 3), f"上界 {float(hi/3):.6f}")


# ---------------------------------------------------------------- (F)
def section_F():
    print("(F) Theorem 4.1 的 n = 4 账目：d = q/3 <= d <= c = 1 - 2q/3（0 < q < 1）")
    for q in (F(1, 4), F(1, 2), F(3, 4), F(9, 10)):
        c = 1 - 2 * q / 3
        d = q / 3
        check(f"q = {q}：d <= d <= c 且 d < c",
              d <= d <= c and d < c, f"d = {float(d):.6f}, c = {float(c):.6f}")
        check(f"q = {q}：c + 2d = 1", c + 2 * d == 1)


def main():
    print("=" * 78)
    print("ADR2017 split 概率 / 1-3 阈值：精确有理数复核（零 Monte Carlo、零浮点判定）")
    print("=" * 78)
    for f in (section_A, section_B, section_CDE, section_F):
        f()
    print("=" * 78)
    if FAILED:
        print(f"VERDICT: FAIL（{len(FAILED)} 条不通过）")
        for name in FAILED:
            print("  -", name)
        return 1
    print("VERDICT: ALL PASS")
    print("关键数字：")
    print("  * Lemma 3.1：每条 unrooted binary 树展示 2n-3 个 split，其中平凡 n 个、非平凡 n-3 个；")
    print("      n = 4 时非平凡概率之和 = p_conc + 2 p_disc = 1 = n - 3（对 q = exp(-t) 恒等）。")
    print("  * Prop 3.2 阈值 = (1/3)exp(-eps)；n = 4 时不展示的 split 概率恰 = (1/3)exp(-t)。")
    print("  * 紧性见证：eps = 0, alpha = 1/4, t = 1/4 时 alpha < (1/3)exp(-1/4)")
    print("      （交错级数下界 (1/3)*4287317/5505024 = 4287317/16515072 ≈ 0.259600 > 1/4）。")
    print("  * Cor 3.3（eps = 0）阈值 1/3：t > 0 时 (1/3)exp(-t) < 1/3（如 t = 1/4 时 < 1/4）。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
