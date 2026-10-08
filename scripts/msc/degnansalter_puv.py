#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/degnansalter_puv.py -- W10e 数值复核脚本
（**精确有理数 / 60 位 Decimal**，**无 Monte Carlo**）

目的：复核 `Phylo/Stat/DegnanSalter.lean` 里 `pUV` 的定义。

## 文献

J. H. Degnan & L. A. Salter (2005), "Gene tree distributions under the coalescent
process", *Evolution* **59**(1):24-36, **式 (1)**，期刊第 25 页
= `references/pdf/DegnanSalter2005_GeneTreeDistributions.pdf` 第 2 页。
`references/md/DegnanSalter2005_GeneTreeDistributions.md` 第 375-421 行的转换
把 `-` 映射成 `(cid:53)`/`5`、`∑` 映射成 `O`、`≥` 映射成 `(cid:36)`，
**不是可判读的公式**；本脚本用 `pdftotext -layout -enc UTF-8` 的重新提取。

## 本脚本复核的 pUV 定义（= Lean 里的定义）

记 `lam k = k(k-1)/2`（coalescent units）。Kingman 纯死亡链的生成元
`Q`（`Q[k,k] = -lam k`、`Q[k,k-1] = lam k`）在 `{1..u}` 上**部分分式**给出

    p_uv(T) = sum_{k=v}^{u} c(u,v,k) * e^{-lam k * T}

    c(u,v,k) = ( prod_{m=v+1}^{u} lam m ) / ( prod_{m=v, m != k}^{u} (lam m - lam k) )

这是 `(sI - Q)^{-1}[u][v]` 的部分分式系数 —— 也就是式 (1) 的**闭合形式**
（Degnan–Salter 归给 Rosenberg 2002；更早 Tavaré 1984 / Watterson 1984 /
Takahata & Nei 1985）。

`(C1)` 用**独立的 Sylvester 公式** `P_k = prod_{i != k}(Q + lam_i I)/(lam_i - lam_k)`
逐项对照，并检查 `sum_k P_k = I`。

## 检查项

  (C0)  部分分式系数 == 闭合形式
        `(2k-1)(-1)^{k-v} * prod_{y=0}^{k-1}[(u-y)(v-1+y)/(u+y)] / (v!(k-v)!)`
  (C0b) k = u 项 == Tavaré (1984) 经典转移权重
  (C1)  独立 Sylvester 谱分解 == c(u,v,k)；且 sum_k P_k = I
  (C2)  p_uu(T) = e^{-u(u-1)T/2}（系数 = {u: 1}）
  (C3)  sum_k c(u,v,k) = [v == u]（即 p_uv(0) = delta_uv）
  (C4)  p_uv(T) >= 0（u<=6，多组 T，300 位 Decimal）
  (C5)  sum_{v=1}^{u} p_uv(T) = 1（u<=6，多组 T，300 位 Decimal）
  (C6)  p_21(T) = 1 - e^{-T}，p_22(T) = e^{-T}（符号层面）
  (C7)  ODE / 特征关系  sum_w Q[u][w] c(w,v,k) = -lam_k c(u,v,k)
        （即 p_uv(T) = sum_k c_k e^{-lam_k T} 确实是 d/dT p = Q p 的解）

用法：python3 degnansalter_puv.py     （全部通过才 exit 0）
"""
import decimal
import sys
from fractions import Fraction as F

decimal.getcontext().prec = 300


def lam(k):
    return F(k * (k - 1), 2)


def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def prod(xs):
    r = F(1)
    for x in xs:
        r *= x
    return r


# --------------------------------------------------- Lean 里的 pUV 定义
def puv_coeffs(u, v):
    """{k: c(u,v,k)}，即 p_uv(T) 里 e^{-lam_k T} 的系数（精确有理数）。"""
    if v == 0 or v > u:
        return {}
    num = prod(lam(m) for m in range(v + 1, u + 1))
    d = {}
    for k in range(v, u + 1):
        den = prod(lam(m) - lam(k) for m in range(v, u + 1) if m != k)
        c = num / den
        if c:
            d[k] = d.get(k, F(0)) + c
    return d


def dec_exp(x):
    """exp(x)，300 位精度；用 1/exp(-x) 处理大负指数以避免灾难性抵消。"""
    if x < 0:
        return decimal.Decimal(1) / dec_exp_pos(-x)
    return dec_exp_pos(x)


def dec_exp_pos(x):
    s = decimal.Decimal(1)
    term = decimal.Decimal(1)
    n = 0
    while True:
        n += 1
        term = term * x / decimal.Decimal(n)
        s += term
        if abs(term) < decimal.Decimal(10) ** (-290) or n > 20000:
            break
    return s


def puv_num(u, v, T):
    """60 位 Decimal 数值。"""
    tot = decimal.Decimal(0)
    for k, c in puv_coeffs(u, v).items():
        x = -(decimal.Decimal(k * (k - 1)) / decimal.Decimal(2)) * T
        tot += decimal.Decimal(c.numerator) / decimal.Decimal(c.denominator) * dec_exp(x)
    return tot


# --------------------------------------------------- 闭合成品式
def closed_form(u, v, k):
    """(2k-1)(-1)^{k-v} u!(u-1)!(v+k-2)! / (v!(v-1)!(k-v)!(u-k)!(u+k-1)!)"""
    if not (1 <= v <= k <= u):
        return F(0)
    return F((2 * k - 1) * ((-1) ** (k - v)) * fact(u) * fact(u - 1) * fact(v + k - 2)) \
        / F(fact(v) * fact(v - 1) * fact(k - v) * fact(u - k) * fact(u + k - 1))


def closed_form_prod(u, v, k):
    """同一系数的产品写法：
    (2k-1)(-1)^{k-v} * prod_{y=0}^{k-2}(v+y) * prod_{y=0}^{k-1}(u-y)/(u+y) / (v!(k-v)!)"""
    if not (1 <= v <= k <= u):
        return F(0)
    p = F(1)
    for y in range(k - 1):
        p *= F(v + y)
    q = F(1)
    for y in range(k):
        q *= F(u - y, u + y)
    return F((2 * k - 1) * ((-1) ** (k - v))) * p * q / F(fact(v) * fact(k - v))


# --------------------------------------------------- 独立参照：Sylvester
def sylvester(u):
    """P_k = prod_{i != k} (Q + lam_i I)/(lam_i - lam_k)，精确有理数矩阵。

    返回 M，M[k][(i,j)] 为 P_k 的 (i,j) 元；并断言 sum_k P_k = I。"""
    idx = list(range(1, u + 1))
    L = {k: lam(k) for k in idx}

    def ident():
        return {i: {j: (F(1) if i == j else F(0)) for j in idx} for i in idx}

    def Qmat():
        Q = {}
        for k in idx:
            row = {j: F(0) for j in idx}
            row[k] = -L[k]
            if k - 1 >= 1:
                row[k - 1] = L[k]
            Q[k] = row
        return Q

    def mm(A, B):
        return {i: {j: sum(A[i][m] * B[m][j] for m in idx) for j in idx} for i in idx}

    Q = Qmat()
    M = {}
    for k in idx:
        Pk = ident()
        for i in idx:
            if i == k:
                continue
            Qp = {a: {b: (Q[a][b] + (L[i] if a == b else 0)) for b in idx} for a in idx}
            Pk = mm(Pk, Qp)
            s = L[i] - L[k]
            Pk = {a: {b: Pk[a][b] / s for b in idx} for a in idx}
        M[k] = {(i, j): Pk[i][j] for i in idx for j in idx}
    tot = {(i, j): sum(M[k][(i, j)] for k in idx) for i in idx for j in idx}
    assert all(tot[(i, j)] == (F(1) if i == j else F(0)) for i in idx for j in idx), \
        "sum_k P_k != I"
    return M


# ------------------------------------------------------------------ main
def main():
    ok = True

    print("=" * 78)
    print("(C0) partial-fraction coefficient == closed form of eq. (1)")
    bad = 0
    for u in range(1, 10):
        for v in range(1, u + 1):
            cs = puv_coeffs(u, v)
            for k in range(v, u + 1):
                if cs.get(k, F(0)) != closed_form(u, v, k):
                    bad += 1
                    if bad <= 6:
                        print("   MISMATCH u=%d v=%d k=%d: pf=%s closed=%s"
                              % (u, v, k, cs.get(k, F(0)), closed_form(u, v, k)))
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("(C0b) standard textbook Kingman cases: u=2 and u=3")
    ref = {
        (2, 1): {1: F(1), 2: F(-1)},
        (2, 2): {2: F(1)},
        (3, 1): {1: F(1), 2: F(-3, 2), 3: F(1, 2)},
        (3, 2): {2: F(3, 2), 3: F(-3, 2)},
        (3, 3): {3: F(1)},
        (4, 1): {1: F(1), 2: F(-9, 5), 3: F(1), 4: F(-1, 5)},
    }
    bad = 0
    for (u, v), want in sorted(ref.items()):
        got = puv_coeffs(u, v)
        note = "" if got == want else "   <-- MISMATCH"
        if got != want:
            bad += 1
        print("   p_%d%d = %s%s" % (u, v, {k: str(c) for k, c in got.items()}, note))
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("(C0c) closed form, product shape  ==  factorial shape")
    bad = 0
    for u in range(1, 10):
        for v in range(1, u + 1):
            for k in range(v, u + 1):
                if closed_form(u, v, k) != closed_form_prod(u, v, k):
                    bad += 1
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("(C1) independent Sylvester spectral decomposition (and sum_k P_k = I)")
    bad = 0
    for u in range(1, 9):
        M = sylvester(u)
        for v in range(1, u + 1):
            got = {k: M[k][(u, v)] for k in range(1, u + 1) if M[k][(u, v)] != 0}
            want = puv_coeffs(u, v)
            if got != want:
                bad += 1
                if bad <= 6:
                    print("   MISMATCH u=%d v=%d sylvester=%s pf=%s" % (u, v, got, want))
    print("   mismatches:", bad)
    print("   (sum_k P_k = I checked inside sylvester() by assertion)")
    ok &= (bad == 0)

    print("=" * 78)
    print("(C2) p_uu(T) = e^{-u(u-1)T/2}   i.e. coefficients == {u: 1}")
    bad = 0
    for u in range(1, 10):
        if puv_coeffs(u, u) != {u: F(1)}:
            bad += 1
            print("   MISMATCH u=%d: %s" % (u, puv_coeffs(u, u)))
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("(C3) p_uv(0) = delta_uv   i.e. sum_k c(u,v,k) == [v == u]")
    bad = 0
    for u in range(1, 10):
        for v in range(1, u + 1):
            s = sum(puv_coeffs(u, v).values())
            if s != (F(1) if v == u else F(0)):
                bad += 1
                print("   MISMATCH u=%d v=%d sum=%s" % (u, v, s))
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("(C4)/(C5) nonnegativity and normalisation (60-digit Decimal)")
    print("   u    T        sum_v p_uv(T)                        min_v p_uv(T)")
    worst_norm = decimal.Decimal(0)
    worst_neg = decimal.Decimal(0)
    for u in range(1, 7):
        for T in (decimal.Decimal('0'), decimal.Decimal('0.01'), decimal.Decimal('0.1'),
                  decimal.Decimal('0.5'), decimal.Decimal('1'), decimal.Decimal('2'),
                  decimal.Decimal('5'), decimal.Decimal('10')):
            vals = [puv_num(u, v, T) for v in range(1, u + 1)]
            s = sum(vals)
            mn = min(vals)
            worst_norm = max(worst_norm, abs(s - 1))
            worst_neg = min(worst_neg, mn)
            print("   %-4d %-8s %.36f   % .3e" % (u, T, s, mn))
    print("   max |sum-1| = %.3e ; min value = % .3e" % (worst_norm, worst_neg))
    ok &= (worst_norm < decimal.Decimal('1e-30'))
    ok &= (worst_neg > decimal.Decimal('-1e-30'))

    print("=" * 78)
    print("(C6) p_21(T) = 1 - e^{-T} ; p_22(T) = e^{-T}   (symbolically)")
    a, b = puv_coeffs(2, 1), puv_coeffs(2, 2)
    print("   p_21 =", {k: str(c) for k, c in a.items()}, " -> 1 - e^{-T}")
    print("   p_22 =", {k: str(c) for k, c in b.items()}, " -> e^{-T}")
    c6 = (a == {1: F(1), 2: F(-1)}) and (b == {2: F(1)})
    print("   symbolic match:", c6)
    ok &= c6

    print("=" * 78)
    print("(C7) ODE / eigen-relation: sum_w Q[u][w] c(w,v,k) == -lam_k * c(u,v,k)")
    def Qentry(u, w):
        if w == u:
            return -lam(u)
        if w == u - 1:
            return lam(u)
        return F(0)

    bad = 0
    for u in range(1, 9):
        for v in range(1, u + 1):
            for k in range(v, u + 1):
                lhs = sum(Qentry(u, w) * puv_coeffs(w, v).get(k, F(0))
                          for w in range(1, u + 1))
                rhs = -lam(k) * puv_coeffs(u, v).get(k, F(0))
                if lhs != rhs:
                    bad += 1
                    if bad <= 5:
                        print("   MISMATCH u=%d v=%d k=%d: %s vs %s" % (u, v, k, lhs, rhs))
    print("   mismatches:", bad)
    ok &= (bad == 0)

    print("=" * 78)
    print("VERDICT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
