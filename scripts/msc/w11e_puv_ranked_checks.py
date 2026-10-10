#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""scripts/msc/w11e_puv_ranked_checks.py —— W11e 的**精确**数值/符号复核.

**精确有理数（`fractions.Fraction`）／整数，无 Monte Carlo。**

本脚本复核 W11e 新证的两组定理（`Phylo/Stat/DegnanSalter.lean`、
`Phylo/Stat/RankedGeneTree.lean`）：

  (A) `Phylo.Stat.DegnanSalter.pUVCoeff_sum_Icc_eq`（= 文件头勘误后的**正确**系数恒等式）
          sum_{v=1}^{k} c(u,v,k) = 1  if k = 1 else 0      (1 <= k <= u <= 9)
      以及**旧 docstring 里那条错的口径** `k = u`：显式给出 u = k = 3 的反例。

  (B) `Phylo.Stat.DegnanSalter.pUV_sum_Icc_one`（一般归一化）
      以 x = e^{-t} 为未定元：p_{uv} 是 x^{lam_k} 的有理系数多项式
      （lam_k = k(k-1)/2 恒为整数），故 `sum_v p_{uv} = 1` 是**多项式恒等式**，
      可在 u <= 9 上**精确**判定（不是数值抽样）。

  (C) `Phylo.Stat.DegnanSalter.pUV_nonneg` 的 u <= 3 部分：把闭形式化成
      非负因式（(1/2)(1-x)^2(2+x) 与 (3/2)(x - x^3)）逐项核对。

  (D) `Phylo.Stat.RankedGeneTree.eq4_uniform_rates`（式 (4) 一般 m，lam_j = j）
          sum_{j=0}^{m} x^j / prod_{k != j} (k - j) = (1/m!) (1-x)^m    (m <= 10)
      以 x = e^{-s} 为未定元，两边都是有理系数多项式，**精确**判定。

  (E) `Phylo.Stat.RankedGeneTree.rankedFiberCount_four`（Remark 6 在 n = 4 的
      **一般 f** 形式）与 `ranked4_probability_gap_proved`：
      穷举 n = 4 的**全部**合并史，核对每个纤维的大小 = (n-1)!/prod(c_i-1)，
      并核对构造出来的 p（平衡形 2 个各 mscConcordant/2、其余 16 个各
      (1 - mscConcordant)/16）非负、求和 = 1、平衡形边缘 = mscConcordant(x)。
"""

from fractions import Fraction as F
from itertools import product
from math import factorial

PASS = True
def check(name, cond):
    global PASS
    print(("  PASS  " if cond else "  FAIL  ") + name)
    if not cond:
        PASS = False

# ---------------------------------------------------------------- 0. 组合/多项式工具
def lam(k):
    """Kingman 合并率 k(k-1)/2（精确有理数，恒为整数）。"""
    return F(k * (k - 1), 2)

def c(u, v, k):
    """pUVCoeff（部分分式形式，与 Lean 的定义逐字对应）。"""
    if v == 0:
        return F(0)
    num = F(1)
    for m in range(v + 1, u + 1):
        num *= lam(m)
    den = F(1)
    for m in range(v, u + 1):
        if m != k:
            den *= lam(m) - lam(k)
    return num / den

def poly_mul(a, b):
    r = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            r[e1 + e2] = r.get(e1 + e2, F(0)) + c1 * c2
    return {e: c for e, c in r.items() if c != 0}

def poly_add(a, b):
    r = dict(a)
    for e, c in b.items():
        r[e] = r.get(e, F(0)) + c
    return {e: c for e, c in r.items() if c != 0}

def poly_pow(a, n):
    r = {0: F(1)}
    for _ in range(n):
        r = poly_mul(r, a)
    return r

def poly_str(a):
    if not a:
        return "0"
    return " + ".join(f"{c}*x^{e}" for e, c in sorted(a.items()))

def puv_poly(u, v):
    """p_{uv}(t) 以 x = e^{-t} 为未定元的多项式（指数 = lam_k，恒整数）。"""
    d = {}
    for k in range(v, u + 1):
        e = lam(k)
        assert e.denominator == 1
        d[e.numerator] = d.get(e.numerator, F(0)) + c(u, v, k)
    return {e: co for e, co in d.items() if co != 0}

# ---------------------------------------------------------------- (A) 系数恒等式
print("== (A) 系数行和恒等式 sum_{v=1}^{k} c(u,v,k) = delta_{k,1}  (u <= 9)")
ok = True
for u in range(1, 10):
    for k in range(1, u + 1):
        s = sum((c(u, v, k) for v in range(1, k + 1)), F(0))
        want = F(1) if k == 1 else F(0)
        if s != want:
            ok = False
            print(f"     mismatch u={u} k={k}: {s} != {want}")
check("sum_{v<=k} c(u,v,k) = delta_{k,1} for 1 <= k <= u <= 9", ok)
check("旧 docstring 的 k = u 口径在 u = k = 3 处为假 "
      f"(sum = {sum((c(3, v, 3) for v in range(1, 4)), F(0))} vs 1)",
      sum((c(3, v, 3) for v in range(1, 4)), F(0)) == 0)
check("沿 k 求和的那条（pUV_zero_time 用）sum_{k=v}^{u} c(u,v,k) = delta_{v,u}",
      all(sum((c(u, v, k) for k in range(v, u + 1)), F(0)) == (F(1) if u == v else F(0))
          for u in range(1, 8) for v in range(1, u + 1)))

# ---------------------------------------------------------------- (B) 一般归一化
print("== (B) 一般归一化 sum_{v=1}^{u} p_{uv}(t) = 1（多项式恒等式，x = e^{-t}）")
ok = True
for u in range(1, 10):
    tot = {}
    for v in range(1, u + 1):
        tot = poly_add(tot, puv_poly(u, v))
    if tot != {0: F(1)}:
        ok = False
        print(f"     mismatch u={u}: {poly_str(tot)}")
check("sum_{v=1}^{u} p_{uv} = 1（u <= 9，精确多项式）", ok)
# 逐项与 (C5) 的形状对齐（u = 2, 3, 4 的显式闭形式）
check("p_{21} = 1 - x, p_{22} = x", puv_poly(2, 1) == {0: F(1), 1: F(-1)}
      and puv_poly(2, 2) == {1: F(1)})
check("p_{31} = 1 - (3/2)x + (1/2)x^3", puv_poly(3, 1) == {0: F(1), 1: F(-3, 2), 3: F(1, 2)})
check("p_{32} = (3/2)(x - x^3)", puv_poly(3, 2) == {1: F(3, 2), 3: F(-3, 2)})
check("p_{33} = x^3", puv_poly(3, 3) == {3: F(1)})

# ---------------------------------------------------------------- (C) 非负性（u <= 3）
print("== (C) u <= 3 的闭形式非负因式")
lhs31 = {0: F(1), 1: F(-3, 2), 3: F(1, 2)}
fac31 = poly_mul(poly_mul({0: F(1, 2)}, poly_pow(poly_add({0: F(1)}, {1: F(-1)}), 2)),
                 poly_add({0: F(2)}, {1: F(1)}))
check("1 - (3/2)x + (1/2)x^3 = (1/2)(1-x)^2(2+x)", lhs31 == fac31)
check("p_{32} = (3/2)(x - x^3) = (3/2)x(1-x)(1+x) 在 0 < x <= 1 非负（逐点）",
      all(sum((co * x ** e for e, co in puv_poly(3, 2).items()), F(0)) >= 0
          for x in (F(1, 100), F(1, 2), F(9, 10), F(1))))
check("p_{31} 在 0 < x <= 1 非负（逐点，含闭式因式）",
      all(sum((co * x ** e for e, co in puv_poly(3, 1).items()), F(0)) >= 0
          for x in (F(1, 100), F(1, 2), F(9, 10), F(1))))
check("p_{uv} 在 x = 1/2, 3/4, 1 处非负（u <= 4）",
      all(sum((co * x ** e for e, co in puv_poly(u, v).items()), F(0)) >= 0
          for u in range(2, 5) for v in range(1, u + 1) for x in (F(1, 2), F(3, 4), F(1))))

# ---------------------------------------------------------------- (D) eq4（lam_j = j）
print("== (D) sum_{j=0}^{m} x^j / prod_{k != j}(k-j) = (1/m!)(1-x)^m  (m <= 10)")
ok = True
for m in range(0, 11):
    acc = {}
    for j in range(0, m + 1):
        den = F(1)
        for k in range(0, m + 1):
            if k != j:
                den *= (k - j)
        acc = poly_add(acc, {j: F(1) / den})
    rhs = poly_mul({0: F(1) / F(factorial(m))}, poly_pow(poly_add({0: F(1)}, {1: F(-1)}), m))
    if acc != rhs:
        ok = False
        print(f"     mismatch m={m}: {poly_str(acc)} != {poly_str(rhs)}")
check("eq4 的一般 m 恒等式（m <= 10，精确多项式）", ok)

# ---------------------------------------------------------------- (E) n = 4 ranked
print("== (E) n = 4：纤维公式（一般 f）与构造性概率表")
N = 4
def step_map(r, x, y):
    return tuple((x if r[w] == y else r[w]) for w in range(N))

def chain_map(f, L):
    r = tuple(range(N))
    for k in range(min(L, len(f))):
        r = step_map(r, f[k][0], f[k][1])
    return r

def is_merge_history(f):
    for k in range(len(f)):
        r = chain_map(f, k)
        x, y = f[k]
        if not (r[x] == x and r[y] == y and x < y):
            return False
    r = chain_map(f, len(f))
    return len(set(r)) == 1

def clades_of(f):
    out = set()
    for L in range(N):
        r = chain_map(f, L)
        for w in range(N):
            out.add(frozenset(z for z in range(N) if r[z] == r[w]))
    return frozenset(out)

allf = list(product(product(range(N), repeat=2), repeat=N - 1))
hist = [f for f in allf if is_merge_history(f)]
check(f"n = 4 的合并史数 = 18（穷举 {len(allf)} 个编码）", len(hist) == 18)
groups = {}
for f in hist:
    groups.setdefault(clades_of(f), []).append(f)
check("n = 4 的无次序拓扑数 = 15", len(groups) == 15)
ok = True
for cl, fs in groups.items():
    want = factorial(N - 1) // 1
    for C in cl:
        if len(C) >= 2:
            want //= (len(C) - 1)
    if len(fs) != want:
        ok = False
        print(f"     mismatch clades={sorted(sorted(C) for C in cl)}: {len(fs)} != {want}")
check("每个纤维大小 = (n-1)!/prod_{|C|>=2}(|C|-1)（n = 4 全部 15 个拓扑）", ok)
sizes = sorted(len(fs) for fs in groups.values())
check(f"纤维大小分布 = {sizes}（平衡形 2 × 3 个 + caterpillar 1 × 12 个）",
      sizes == [1] * 12 + [2] * 3)

def is_balanced(cl):
    pair = [C for C in cl if len(C) == 2]
    return len(pair) == 2
bal = frozenset(frozenset(C) for C in (frozenset({0, 1}), frozenset({2, 3}), frozenset({0, 1, 2, 3}),
                                       frozenset({0}), frozenset({1}), frozenset({2}), frozenset({3})))
bal_hist = [f for f in hist if clades_of(f) == bal]
check("平衡形 ((0,1),(2,3)) 恰有 2 个 ranking", len(bal_hist) == 2)
# 构造 p：平衡形两个各 C(x)/2，其余各 (1-C(x))/16；C(x) = 1 - (2/3)x
Cx = {0: F(1), 1: F(-2, 3)}
tot = {}
for f in hist:
    p = {0: F(1, 2)} if False else None
    if clades_of(f) == bal:
        p = poly_mul(Cx, {0: F(1, 2)})
    else:
        p = poly_mul(poly_add({0: F(1)}, poly_mul({0: F(-1)}, Cx)), {0: F(1, 16)})
    tot = poly_add(tot, p)
check("构造的 p 求和 = 1（精确多项式）", tot == {0: F(1)})
marg = {}
for f in bal_hist:
    marg = poly_add(marg, poly_mul(Cx, {0: F(1, 2)}))
check("平衡形边缘 sum = mscConcordant(x) = 1 - (2/3)x（精确多项式）", marg == Cx)
check("p 非负（x = 1/2, 3/4, 1 逐点，全部 18 个排名）",
      all((lambda p: sum((co * x ** e for e, co in p.items()), F(0)) >= 0)(
              poly_mul(Cx, {0: F(1, 2)}) if clades_of(f) == bal
              else poly_mul(poly_add({0: F(1)}, poly_mul({0: F(-1)}, Cx)), {0: F(1, 16)}))
          for f in hist for x in (F(1, 2), F(3, 4), F(1))))

print()
print("VERDICT:", "PASS" if PASS else "FAIL")
raise SystemExit(0 if PASS else 1)
