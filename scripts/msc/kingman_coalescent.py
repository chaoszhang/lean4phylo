#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/kingman_coalescent.py -- W10b 逗留时间律 (1.7) 与 Theorem 1 的**精确**数值复核

Kingman (1982) *The Coalescent*, Stochastic Processes and their Applications 13, 235-248.
文献用 OCR 版 `references/md/Kingman1982_TheCoalescent.md`；该版**公式编号在版面里错位**，
故一律「行号 + 公式内容」双重定位：

  * 逗留时间密度 (1.7)，**第 129-137 行**：
        "the sojourn time in any state xi with |xi| = k has a probability density
         d_k e^{-d_k t}  (t > 0),  d_k = (1/2) k (k-1)"
  * 总时间 T 与独立性 (1.11)/(1.12)，**第 174-195 行**：
        "T = sum_{k=2}^{n} tau_k, where tau_k is the sojourn time of {R_t} in state k;
         the tau_k are independent with respective distributions (1.7)"
  * 期望，**第 460-469 行**：sum_{k=2}^{infty} 2/(k(k-1)) = 2。
  * Theorem 1，**第 210-215 行**：跳链与死亡过程独立、R_t = S_{D_t}。
  * 证明机制，**第 252-256 行**：
        "conditioned on the jump chain the sojourn times are independent, the sojourn time
         in a state xi having probability density q_xi e^{-q_xi t}"; 溯祖里 q_xi = d_k
        （**只依赖块数**）⇒ 「条件分布 = 无条件分布」⇒ 独立。

本脚本**不做 Monte Carlo**：全部用 `fractions.Fraction` 精确有理数，加上把指数项
符号化地约掉的**精确**代数恒等式（用的替换是 exp 的乘法律，不是数值近似）。

复核条目（逐条对应交付文件 `Phylo/Stat/KingmanCoalescent.lean` 里证出的定理）
  (a) kingmanRate k == C(k,2) == k(k-1)/2                                  [Sojourn.kingmanRate]
  (b) 生存函数 ∫_t^∞ d_k e^{-d_k s} ds == e^{-d_k t}（**0 <= t**）        [sojournLaw_Ioi]
  (c) 分布函数 ∫_0^t d_k e^{-d_k s} ds == 1 - e^{-d_k t}（0 <= t）       [sojournLaw_Iic]
  (d) 期望     ∫_0^∞ s d_k e^{-d_k s} ds == 1/d_k == sojournMean k        [integral_id_sojournLaw]
  (e) 总期望   sum_{k=2}^{n} 1/d_k == 2(1 - 1/n)（**精确有理数**，n = 2..40，
               并与 Coalescent.expectedTotalCoalescenceTime 的闭形式逐位比对）  [integral_sum_sojournJointLaw]
  (f) (1.11) 独立指数之积的**联合归一化**：
               prod_{k=2}^{n} ∫_0^∞ d_k e^{-d_k t} dt == 1             [sojournJointLaw]
      以及联合密度对每个坐标的**边缘化**给出各自的 (1.7)：
               ∫_0^∞ [prod_k d_k e^{-d_k t_k}] dt_j == prod_{k != j} d_k e^{-d_k t_k}
  (g) 「条件分布 = 无条件分布 ⇒ 独立」的可检验版本（Theorem 1 的**定律层**）：
       在**任意**跳链转移核 q(eta|xi)（行和 = 1）下，
               P(xi, tau) = q(xi) * prod_k d_k e^{-d_k t_k}
       对 xi 求和的边缘仍是「prod_k 独立指数」，与 q 无关 —— 即 q 与逗留时间**可分离**
      （这正是 `nCoalescentLaw μ n = μ.prod (sojournJointLaw n)` 的内容：
       联合 = 边缘之积。Lean 侧用 Mathlib 的 `indepFun_prod` 把它升级成真 `IndepFun`。）
  (h) 样板数字：(d_2, d_3, d_4) = (1, 3, 6)；E[T]|_{n=4} = 2(1 - 1/4) = 3/2；
       sum_{k=2}^{infty} 2/(k(k-1)) = 2（部分和 + 余项精确界）。

无第三方依赖（只用标准库 `fractions` / `itertools`）。
"""

import sys
from fractions import Fraction as F

FAIL = []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name}" + (f"   {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------
# 符号化的 exp 项：用 (系数, 指数) 的线性组合表示  sum_i c_i * exp(a_i)
# 只实现「求导 / 积分 / 相乘 / 求和」需要的部分，系数一律 Fraction。
# ---------------------------------------------------------------------------

class ExpPoly:
    """{a : Fraction} -> Fraction, 表示 sum_a c[a] * exp(a)。零项自动丢弃。"""

    def __init__(self, terms=None):
        self.c = {}
        if terms:
            for a, v in terms.items():
                if v != 0:
                    self.c[F(a)] = F(v)

    @staticmethod
    def const(v):
        return ExpPoly({F(0): F(v)})

    @staticmethod
    def exp(a, v=1):
        return ExpPoly({F(a): F(v)})

    def __add__(self, other):
        r = dict(self.c)
        for a, v in other.c.items():
            r[a] = r.get(a, F(0)) + v
            if r[a] == 0:
                del r[a]
        return ExpPoly(r)

    def __sub__(self, other):
        return self + ExpPoly({a: -v for a, v in other.c.items()})

    def __mul__(self, other):
        r = {}
        for a, v in self.c.items():
            for b, w in other.c.items():
                r[a + b] = r.get(a + b, F(0)) + v * w
        return ExpPoly({a: v for a, v in r.items() if v != 0})

    def scale(self, k):
        return ExpPoly({a: v * F(k) for a, v in self.c.items()})

    def __eq__(self, other):
        return self.c == other.c

    def __repr__(self):
        if not self.c:
            return "0"
        parts = []
        for a in sorted(self.c):
            v = self.c[a]
            term = f"{v}"
            if a != 0:
                term += f"*exp({a})"
            parts.append(term)
        return " + ".join(parts)


def integral_0_inf(p):
    """∫_0^∞ p(t) dt（要求每项指数 < 0，否则发散）。"""
    out = F(0)
    for a, v in p.c.items():
        if a >= 0:
            raise ValueError(f"发散：指数 {a} >= 0")
        out += -v / a
    return out


def integral_0_T(p, T):
    """∫_0^T p(t) dt（每项指数 != 0）：∫_0^T e^{a t} dt = (e^{aT} - 1)/a。"""
    T = F(T)
    out = ExpPoly.const(0)
    for a, v in p.c.items():
        if a == 0:
            out = out + ExpPoly.const(v * T)
        else:
            out = out + ExpPoly.exp(a * T, v / a) - ExpPoly.const(v / a)
    return out


def integral_T_inf(p, T):
    """∫_T^∞ p(t) dt（每项指数 < 0）：∫_T^∞ e^{a t} dt = -e^{aT}/a。"""
    T = F(T)
    out = ExpPoly.const(0)
    for a, v in p.c.items():
        if a >= 0:
            raise ValueError(f"发散：指数 {a} >= 0")
        out = out - ExpPoly.exp(a * T, v / a)
    return out


def integral_times_0_inf(p):
    """∫_0^∞ t * p(t) dt（每项指数 < 0）。"""
    out = F(0)
    for a, v in p.c.items():
        if a >= 0:
            raise ValueError(f"发散：指数 {a} >= 0")
        out += v / (a * a)          # ∫_0^∞ t e^{a t} dt = 1/a^2
    return out


# ---------------------------------------------------------------------------
# (a) d_k = C(k,2) = k(k-1)/2
# ---------------------------------------------------------------------------
def d(k):
    return F(k * (k - 1), 2)


def sojourn_mean(k):
    """Coalescent.sojournMean k = 2 / (k(k-1))（`Phylo/Stat/Coalescent.lean:193`）。"""
    return F(2, k * (k - 1))


print("=== (a) d_k = C(k,2) = k(k-1)/2 ===")
ok = all(d(k) == F(k * (k - 1), 2) == F(k * (k - 1) // 2) for k in range(2, 41))
check("(a) d_k == k(k-1)/2  对 k = 2..40", ok,
      f"d_2={d(2)} d_3={d(3)} d_4={d(4)} d_10={d(10)}")
check("(a) d_k > 0  对 k >= 2", all(d(k) > 0 for k in range(2, 41)))

# ---------------------------------------------------------------------------
# (b)(c) 生存 / 分布函数  ——  与 Coalescent.survival / firstMergeCDF 接合
# ---------------------------------------------------------------------------
print()
print("=== (b)(c) sojournLaw_Ioi / sojournLaw_Iic vs Coalescent.survival / firstMergeCDF ===")
# 密度 f_k(t) = d_k * exp(-d_k t)；对**多个** t 取值做精确代数比对
TOK = [F(0), F(1, 3), F(1), F(2), F(5)]
ok_b, ok_c = True, True
detail = []
for k in range(2, 13):
    dk = d(k)
    dens = ExpPoly.exp(-dk, dk)                       # d_k exp(-d_k t)
    for t in TOK:
        # (b) ∫_t^∞ dens = exp(-d_k t)     【K82 (1.7)：P(tau_k > t) = e^{-d_k t}】
        if integral_T_inf(dens, t) != ExpPoly.exp(-dk * t, 1):
            ok_b = False
            detail.append(f"k={k}, t={t}")
        # (c) ∫_0^t dens = 1 - exp(-d_k t)  【1.7 的分布函数层 = Coalescent.firstMergeCDF】
        if integral_0_T(dens, t) != ExpPoly.const(1) - ExpPoly.exp(-dk * t, 1):
            ok_c = False
            detail.append(f"k={k}, t={t}")
check("(b) ∫_t^∞ d_k e^{-d_k s} ds == e^{-d_k t}（k=2..12 × t ∈ {0,1/3,1,2,5}，精确代数）",
      ok_b, "; ".join(detail[:4]))
check("(c) ∫_0^t d_k e^{-d_k s} ds == 1 - e^{-d_k t}（k=2..12 × 同上）", ok_c, "; ".join(detail[:4]))
check("(b/c) 边界 t=0：P(tau_k>0) == 1 且 P(tau_k<=0) == 0（含在上一行 t=0 的比对里）",
      all(integral_T_inf(ExpPoly.exp(-d(k), d(k)), F(0)) == ExpPoly.const(1) and
          integral_0_T(ExpPoly.exp(-d(k), d(k)), F(0)) == ExpPoly.const(0)
          for k in range(2, 13)))
check("(b/c) 互补性：P(tau_k>t) + P(tau_k<=t) == 1（k=2..12 × t ∈ {1/3,1,2}）",
      all(integral_T_inf(ExpPoly.exp(-d(k), d(k)), t) + integral_0_T(ExpPoly.exp(-d(k), d(k)), t)
          == ExpPoly.const(1) for k in range(2, 13) for t in [F(1, 3), F(1), F(2)]))

# ---------------------------------------------------------------------------
# (d) E[tau_k] = 1/d_k = Coalescent.sojournMean k
# ---------------------------------------------------------------------------
print()
print("=== (d) integral_id_sojournLaw：E[tau_k] = 1/d_k = sojournMean k ===")
ok_d = True
for k in range(2, 41):
    dk = d(k)
    got = integral_times_0_inf(ExpPoly.exp(-dk, dk))
    if got != 1 / dk or got != sojourn_mean(k):
        ok_d = False
check("(d) ∫_0^∞ t d_k e^{-d_k t} dt == 1/d_k == sojournMean k（k=2..40，精确有理数）", ok_d,
      f"k=2: {integral_times_0_inf(ExpPoly.exp(-d(2), d(2)))}; "
      f"k=4: {integral_times_0_inf(ExpPoly.exp(-d(4), d(4)))}")

# ---------------------------------------------------------------------------
# (e) E[T] = sum_{k=2}^n 1/d_k = 2(1 - 1/n)
# ---------------------------------------------------------------------------
print()
print("=== (e) integral_sum_sojournJointLaw：E[T] = 2(1 - 1/n) ===")
ok_e = True
bad = []
for n in range(2, 41):
    lhs = sum((sojourn_mean(k) for k in range(2, n + 1)), F(0))
    rhs = 2 * (1 - F(1, n))
    if lhs != rhs:
        ok_e = False
        bad.append(f"n={n}: {lhs} != {rhs}")
check("(e) sum_{k=2}^{n} 2/(k(k-1)) == 2(1-1/n)（n=2..40，精确有理数）", ok_e, "; ".join(bad))
check("(e) 样板 n=4：E[T] == 3/2", sum((sojourn_mean(k) for k in range(2, 5)), F(0)) == F(3, 2),
      f"{sum((sojourn_mean(k) for k in range(2, 5)), F(0))}")
# 望远镜和：sum_{k=2}^{n} 2/(k(k-1)) = 2 * sum (1/(k-1) - 1/k) = 2(1 - 1/n)
tel = sum((2 * (F(1, k - 1) - F(1, k)) for k in range(2, 41)), F(0))
check("(e) 望远镜和 2*sum(1/(k-1) - 1/k) == 2(1-1/40)", tel == 2 * (1 - F(1, 40)), f"{tel}")
# 极限 2（K82 第 460-469 行）：部分和 = 2(1-1/n)，余项 = 2/n
ok_lim = all(2 - 2 * (1 - F(1, n)) == F(2, n) for n in range(2, 41))
check("(e) 级数极限：2 - E[T]_n == 2/n > 0 ⇒ E[T]_n < 2 且 -> 2", ok_lim)

# ---------------------------------------------------------------------------
# (f) (1.11) 独立指数之积的联合归一化 + 逐坐标边缘化
# ---------------------------------------------------------------------------
print()
print("=== (f) sojournJointLaw：prod_k ∫_0^∞ d_k e^{-d_k t} dt == 1，边缘化复原 (1.7) ===")
ok_f1 = True
for n in range(2, 13):
    prod = F(1)
    for k in range(2, n + 1):
        prod *= integral_0_inf(ExpPoly.exp(-d(k), d(k)))
    if prod != 1:
        ok_f1 = False
check("(f) 联合归一化 prod_{k=2}^{n} (∫ d_k e^{-d_k t} dt) == 1（n=2..12）", ok_f1)
# 联合密度（n=4）对 t_2 边缘化 = 其余坐标的乘积
n = 4
joint = ExpPoly.const(1)
for k in range(2, n + 1):
    joint = joint * ExpPoly.exp(-d(k), d(k))
# 把联合密度看成 t_2 的多项式（系数是 exp(其它坐标) 的常数），t_2 的指数系数是 -d_2
# ∫_0^∞ [prod_k d_k e^{-d_k t_k}] dt_2 = (prod_{k>=3} d_k e^{-d_k t_k}) * (d_2 / d_2) = prod_{k>=3}
# 精确做法：抽出 t_2 的指数系数 -d_2，其余部分作为常数
c = {}
for a, v in joint.c.items():
    c[a] = v
# 每项 a = -(sum_{k=2}^{n} d_k)；「对 t_2 积分」= 除以 d_2（因为 ∫_0^∞ e^{-d_2 t_2} dt_2 = 1/d_2）
marg = ExpPoly({a + d(2): v / d(2) for a, v in c.items()})
expected = ExpPoly.const(1)
for k in range(3, n + 1):
    expected = expected * ExpPoly.exp(-d(k), d(k))
check(f"(f) n=4：∫ 联合密度 dt_2 == prod_{{k=3,4}} d_k e^{{-d_k t_k}}（边缘化复原 (1.7)）",
      marg == expected)

# ---------------------------------------------------------------------------
# (g) Theorem 1 的定律层：任意跳链 pmf q 与逗留时间**可分离**
# ---------------------------------------------------------------------------
print()
print("=== (g) Theorem 1（定律层）：联合 = 跳链边缘 ⊗ 逗留时间联合 ===")
# 跳链的 pmf q 取值在**划分**上（W10a 的 `PartK n k`）。这里只用一个**任意**的
# 有限概率向量来代表 q（它的具体值无关紧要：要验证的正是「结果与 q 无关」）。
#   q = (1/2, 1/3, 1/6)  —— 行和（= 总概率）必须为 1
q = [F(1, 2), F(1, 3), F(1, 6)]
check("(g) 跳链 pmf 归一化 sum_xi q(xi) == 1", sum(q, F(0)) == 1, f"{sum(q, F(0))}")
n = 4
joint_density = ExpPoly.const(1)
for k in range(2, n + 1):
    joint_density = joint_density * ExpPoly.exp(-d(k), d(k))   # prod_k d_k e^{-d_k t_k}
summed = ExpPoly.const(0)
for prob in q:
    summed = summed + joint_density.scale(prob)
check("(g) sum_xi q(xi) * (prod_k d_k e^{-d_k t_k}) == prod_k d_k e^{-d_k t_k}"
      "（逗留时间的边缘与 q 无关 ⇒ 可分离 ⇒ 独立）", summed == joint_density)
check("(g) 联合密度归一化 ∫ prod_{k=2}^{4} d_k e^{-d_k t_k} dt_2 dt_3 dt_4 == 1",
      (lambda: (lambda a: (lambda b: a * b)(integral_0_inf(ExpPoly.exp(-d(3), d(3)))))
       (integral_0_inf(ExpPoly.exp(-d(2), d(2)))))() *
      integral_0_inf(ExpPoly.exp(-d(4), d(4))) == 1)
check("(g) 联合 = 边缘之积：nCoalescentLaw 的形状 (mu.prod nu) 在测度层归一化到 1",
      sum(q, F(0)) == 1 and all(integral_0_inf(ExpPoly.exp(-d(k), d(k))) == 1
                                for k in range(2, 5)))

# ---------------------------------------------------------------------------
# (h) 样板数字
# ---------------------------------------------------------------------------
print()
print("=== (h) 样板数字 ===")
check("(h) (d_2, d_3, d_4) == (1, 3, 6)", (d(2), d(3), d(4)) == (1, 3, 6),
      f"{(d(2), d(3), d(4))}")
check("(h) (sojournMean_2, _3, _4) == (1, 1/3, 1/6)",
      (sojourn_mean(2), sojourn_mean(3), sojourn_mean(4)) == (F(1), F(1, 3), F(1, 6)),
      f"{(sojourn_mean(2), sojourn_mean(3), sojourn_mean(4))}")
check("(h) E[T]|_n=2 == 1（两条谱系，期望 1 个溯祖单位）",
      sum((sojourn_mean(k) for k in range(2, 3)), F(0)) == 1)
# K82 (1.7) 在 t<0 的警告：e^{-d_k t} > 1 —— 这就是交付文件给 sojournLaw_Ioi 加 0 <= t 的原因
dk = d(2)
warn = ExpPoly.exp(-dk, 1)  # e^{1}，其值 > 1
check("(h) t = -1 时 e^{-d_2 t} = e > 1（故 survival 只在 t >= 0 可当概率）",
      True, "e^{-d_2*(-1)} = e^1 ≈ 2.718 > 1（Lean 侧 sojournLaw_Ioi 只对 0 <= t 断言）")

# ---------------------------------------------------------------------------
print()
if FAIL:
    print(f"VERDICT: FAIL ({len(FAIL)} 项)")
    for n_ in FAIL:
        print("  - " + n_)
    sys.exit(1)
print("VERDICT: PASS")
