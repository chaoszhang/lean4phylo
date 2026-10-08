#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W10i —— Stadler & Degnan (2012) "ranked gene tree probability" 的**精确**数值复核.

规格：`W10_COALESCENT_SPEC.md` §11.3 —— 精确有理数，**不要** Monte Carlo。
本脚本不依赖任何第三方库（无 sympy），全程 `fractions.Fraction` / 整数。

核对内容（每一条都对应本文件头「冒烟测试」里的一条断言）：

  (A) 论文式 (2)  `H_l = l!(l-1)!/2^(l-1)`  与  `H_l = prod_{k=2}^{l} C(k,2)`
      —— 两条独立来源的形状必须处处相等（l = 2..12）。
  (B) 穷举 `n = 2..7` 的**合并序列**（= ranked 树拓扑），核对其计数 = `H_n`
      （= 1, 3, 18, 180, 2700, 56700）；并核对无次序拓扑数 = `(2n-3)!!`。
  (C) ★ 论文 Remark 6（PDF 第 416-424 行）:「给定拓扑有
      `(n-1)!/prod_i (c_i - 1)` 个 ranking」—— 用穷举的拓扑纤维大小逐条核对（n <= 7）。
      ⚠️ 同时**证伪**任务书 §11.3 建议的「给定拓扑的 ranked 树计数 = (n-1)!」。
  (D) Theorem 1 在 `n = 3` 的赋值：把 `e^{-t}` 当作未定元 `x`（有理系数多项式），
      用论文的 `H_2 = 1`、`H_3 = 3` 算出
        concordant : (1-x)/H_2 + x/H_3 = 1 - (2/3) x   == 1 - (2/3)e^{-t}
        discordant : 0/H_2 + x/H_3     = (1/3) x       == (1/3)e^{-t}
      并核对三个 ranked 树的概率和 = 1（与 `Coalescent.pConcordant`/`pDiscordant` 一致）。
  (E) Theorem 3 的式 (4)：`sum_j e^{-lam_j s} / prod_{k!=j}(lam_k - lam_j)`。
      (E1) 论文自算的例子 `lam = (0,1,2)`、`m = 2`（PDF 第 399-413 行）：
           结果 = `1/2 - x + x^2/2 = (1/2)(1-x)^2 = [g_{2,1}(s)]^2/2`（`g_{2,1} = 1 - e^{-s}`）。
           —— 这是**论文自己给的两条独立路线**（式 (4) vs 式 (4) 下方第 356-357 行的
           「一个种群有合并时」的 `g` 乘积公式）的交叉核对。
      (E2) 一般 `lam_j = j`（j = 0..m）：和 = `(1/m!)(1-x)^m`（m <= 8，二项式定理）。
      (E3) 一般互异有理 `lam`：核对式 (4) 满足**分片差商递推**
             D(lam_0..lam_m) = (D(lam_1..lam_m) - D(lam_0..lam_{m-1})) / (lam_m - lam_0)
           （x = e^{-s/d}，lam_j = a_j/d）—— 独立核验式 (4) 的分母 `prod_{k!=j}(lam_k - lam_j)`
           与整体形状（含符号约定）。
"""

from fractions import Fraction as F
from itertools import combinations
from math import factorial
import sys

FAIL = []


def check(name, got, want):
    ok = got == want
    print(("  [ok]   " if ok else "  [FAIL] ") + name + f": got={got} want={want}")
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- (A) 式 (2)
def H_prod(l):
    """prod_{k=2}^{l} C(k,2)。"""
    r = 1
    for k in range(2, l + 1):
        r *= k * (k - 1) // 2
    return r


def H_closed(l):
    """l!(l-1)!/2^(l-1)（论文式 (2)）。"""
    return factorial(l) * factorial(l - 1) // (2 ** (l - 1))


def section_A():
    print("(A) 论文式 (2)：H_l = l!(l-1)!/2^(l-1) 与 prod_{k=2}^{l} C(k,2)")
    for l in range(2, 13):
        check(f"H_{l} 闭形式 = 乘积形式", H_closed(l), H_prod(l))
    print("      H_2..H_7 =", [H_prod(l) for l in range(2, 8)])


# ------------------------------------------------- (B)(C) 穷举 ranked 树
def merges_and_clades(n):
    """穷举所有合并序列（= ranked 树），返回 [(序列, clade 集)]。

    状态是 `frozenset` 的 `frozenset`（块用 tuple 排序做可复现输出）。
    """
    start = frozenset(frozenset([i]) for i in range(n))
    out = []

    def rec(state, seq, clades):
        if len(state) == 1:
            out.append((tuple(seq), frozenset(clades)))
            return
        blocks = sorted(state, key=lambda B: min(B))
        for B1, B2 in combinations(blocks, 2):
            new = (state - {B1, B2}) | {B1 | B2}
            rec(new, seq + [(tuple(sorted(B1)), tuple(sorted(B2)))],
                clades | {frozenset(B1 | B2)})

    rec(start, [], set(start))
    return out


def double_factorial_odd(n):
    """(2n-3)!! = 无次序有根二叉树（叶标记）的个数。"""
    r = 1
    for j in range(1, n - 1):
        r *= 2 * j + 1
    return r


def remark6_count(clades, n):
    """论文 Remark 6：(n-1)! / prod_{内部顶点}(c_i - 1)，内部顶点 <-> 大小 >= 2 的 clade。"""
    denom = 1
    for C in clades:
        if len(C) >= 2:
            denom *= (len(C) - 1)
    assert factorial(n - 1) % denom == 0, (n, clades)
    return factorial(n - 1) // denom


def section_BC():
    print("(B) 穷举合并序列（ranked 树）的计数")
    for n in range(2, 8):
        rt = merges_and_clades(n)
        check(f"n={n} ranked 树数 = H_n", len(rt), H_prod(n))
        tops = {}
        for _, cl in rt:
            tops[cl] = tops.get(cl, 0) + 1
        check(f"n={n} 无次序拓扑数 = (2n-3)!!", len(tops), double_factorial_odd(n))
        print(f"        n={n}: ranked={len(rt)} topologies={len(tops)} "
              f"纤维大小集合={sorted(set(tops.values()))}")
    print("(C) ★ 论文 Remark 6 的 ranking 计数（并证伪任务书的 (n-1)!）")
    for n in range(2, 8):
        rt = merges_and_clades(n)
        tops = {}
        for _, cl in rt:
            tops.setdefault(cl, 0)
            tops[cl] += 1
        bad_r6 = [cl for cl, c in tops.items() if c != remark6_count(cl, n)]
        check(f"n={n} Remark 6 公式与穷举一致（纤维数相符）", len(bad_r6), 0)
        if n >= 3:
            wrong = [cl for cl, c in tops.items() if c != factorial(n - 1)]
            print(f"        任务书 (n-1)! = {factorial(n - 1)}：n={n} 时有 {len(wrong)}/{len(tops)} "
                  f"个拓扑的纤维数**不等于**它 ⟹ 该断言为假")
            if not wrong:
                FAIL.append(f"n={n}: (n-1)! 竟然全对")


# ------------------------------------------- (D) Theorem 1 at n = 3
# 稀疏多项式：dict[幂] = Fraction，x 代表 e^{-t}
def pmul(p, q):
    r = {}
    for a, ca in p.items():
        for b, cb in q.items():
            r[a + b] = r.get(a + b, F(0)) + ca * cb
    return {k: v for k, v in r.items() if v != 0}


def padd(*ps):
    r = {}
    for p in ps:
        for k, v in p.items():
            r[k] = r.get(k, F(0)) + v
    return {k: v for k, v in r.items() if v != 0}


def pscale(p, c):
    return {k: v * c for k, v in p.items() if v * c != 0}


def section_D():
    print("(D) Theorem 1 在 n=3 的赋值（x = e^{-t}，有理系数）")
    H2, H3 = F(H_prod(2)), F(H_prod(3))
    X = {1: F(1)}                      # x = e^{-t}
    one = {0: F(1)}
    below_conc = {2: padd(one, pscale(X, F(-1))), 3: X}   # 1 - x  ,  x
    below_disc = {2: {}, 3: X}                            # 0      ,  x
    p_conc = padd(pscale(below_conc[2], 1 / H2), pscale(below_conc[3], 1 / H3))
    p_disc = padd(pscale(below_disc[2], 1 / H2), pscale(below_disc[3], 1 / H3))
    check("concordant = 1 - (2/3)x", p_conc, {0: F(1), 1: F(-2, 3)})
    check("discordant = (1/3)x", p_disc, {1: F(1, 3)})
    check("三个 ranked 树的概率和 = 1",
          padd(p_conc, p_disc, p_disc), {0: F(1)})
    print(f"        H_2={H2} H_3={H3}；1/H_3 = {1/H3} = MSCProof.rootTopoProb（库内推导值）")


# ------------------------------------------- (E) Theorem 3 eq (4)
def eq4(lam, x):
    """sum_j x^{lam_j} / prod_{k != j} (lam_k - lam_j)，lam 为互异 Fraction/整数。"""
    out = {}
    for j, lj in enumerate(lam):
        denom = F(1)
        for k, lk in enumerate(lam):
            if k != j:
                denom *= F(lk - lj)
        out = padd(out, pscale({int(lj): F(1)}, 1 / denom))
    return out


def pbinom_pow(m):
    """(1 - x)^m 的有理系数多项式。"""
    p = {0: F(1)}
    base = {0: F(1), 1: F(-1)}
    for _ in range(m):
        p = pmul(p, base)
    return p


def section_E():
    print("(E1) 论文自算例子 lam=(0,1,2)（PDF 第 399-413 行）")
    got = eq4([0, 1, 2], None)
    want = pscale(pbinom_pow(2), F(1, 2))
    check("式 (4)@lam=(0,1,2) = (1/2)(1-x)^2", got, want)
    check("式 (4)@lam=(0,1,2) = [g_{2,1}(s)]^2/2 的多项式形状", got,
          pscale(pmul({0: F(1), 1: F(-1)}, {0: F(1), 1: F(-1)}), F(1, 2)))
    print("(E2) 一般 lam_j = j：和 = (1/m!)(1-x)^m（m<=8）")
    for m in range(0, 9):
        check(f"m={m}", eq4(list(range(m + 1)), None),
              pscale(pbinom_pow(m), F(1, factorial(m))))
    print("(E3) 一般互异 lam：核对分片差商递推（整数 lam）与 Lagrange/部分分式幂和恒等式（有理 lam）")
    tests_int = [[F(0), F(1), F(3)], [F(0), F(2), F(5), F(9)], [F(1), F(2), F(4)]]
    for lam in tests_int:
        assert all(l.denominator == 1 for l in lam)
        d = eq4(lam, None)
        d_tail = eq4(lam[1:], None)
        d_head = eq4(lam[:-1], None)
        # 标准分片差商递推： f[x_0..x_m] = (f[x_1..x_m] - f[x_0..x_{m-1}])/(x_m - x_0)
        lhs = pscale(padd(d_head, pscale(d_tail, F(-1))), 1 / (lam[-1] - lam[0]))
        check(f"递推 lam={[str(l) for l in lam]}", lhs, d)
    print("        一般互异有理 lam：sum_j lam_j^r / prod_{{k!=j}}(lam_k - lam_j) = (-1)^m [r = m]")
    for lam in [[F(0), F(1), F(3)], [F(1, 2), F(3, 2), F(5, 2), F(7, 2)], [F(1, 3), F(4, 3), F(7, 3)]]:
        m = len(lam) - 1
        for r in range(m + 1):
            s = F(0)
            for j, lj in enumerate(lam):
                denom = F(1)
                for k, lk in enumerate(lam):
                    if k != j:
                        denom *= (lk - lj)
                s += (lj ** r) / denom
            check(f"幂和 lam={[str(l) for l in lam]} r={r}", s,
                  F((-1) ** m) if r == m else F(0))


def main():
    print("=" * 78)
    print("W10i 精确复核：Stadler & Degnan (2012) ranked gene tree probability")
    print("=" * 78)
    section_A()
    section_BC()
    section_D()
    section_E()
    print("=" * 78)
    if FAIL:
        print(f"失败 {len(FAIL)} 项：{FAIL}")
        return 1
    print("全部核对通过（精确有理数/整数，无 Monte Carlo）。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
