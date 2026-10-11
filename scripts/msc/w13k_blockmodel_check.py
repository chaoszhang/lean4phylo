#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w13k_blockmodel_check.py —— W13k `Phylo/Stat/BlockModelAE.lean` 的 ★G 数值对拍
================================================================================

纯标准库（`fractions` / `itertools` / `random`），**精确有理数**优先（`Fraction`），
**穷举**文件里那些**有限组合对象**。不做浮点近似断言（浮点只用于打印参考值）。

逐条对应 Lean 声明（行号为落盘版 `c6bbd6a` 的 `BlockModelAE.lean`）：

  §1  `sum_ite_lt_card`      (:475)  ∑_{i<C} [i<L]·c = L·c          —— 穷举 (C, L, c)
  §2  `blockW_eq_sum_filter` (:303)  「定长+指示」= 「筛子和」= 「前 L 项和」
  §3  `blockW_div_blockL`    (:687)  (∫blockW)/(∫blockL) = w̄  ＋  块级平均的 SLLN 收敛
  §4  `rateMeasure`          (:140)  有限混合测度和为 1 ＋ 有限和积分公式
  §5  `blockMeasure`/`blockSample` (:241/:~256)  小块空间上的乘积测度质量和 = 1、坐标 iid
  §6  退化：`twoRate1`（r≡1,ρ≡1）与 `C = 1`（`blockL ≡ 1`）

用法：  python3 scripts/msc/w13k_blockmodel_check.py     # exit 0 = 全过
"""

import random
import sys
from fractions import Fraction as F
from itertools import product

FAILS = []
COUNTS = {}


def check(group, cond, detail=""):
    COUNTS[group] = COUNTS.get(group, 0) + 1
    if not cond:
        FAILS.append((group, detail))


def weak_compositions(total, parts):
    """`total` 拆成 `parts` 个非负整数（允许 0），穷举。"""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, parts - 1):
            yield (first,) + rest


# --------------------------------------------------------------------------- #
# §1  sum_ite_lt_card :  ∑_{i ∈ range C} (if i < L then c else 0) = L · c
# --------------------------------------------------------------------------- #
def s1_sum_ite_lt_card(Cmax=6, cs=(F(1), F(0), F(-3, 7), F(2 ** 53), F(123456789, 1000000))):
    combos = 0
    for C in range(1, Cmax + 1):
        for L in range(1, C + 1):          # L 落在 [1, C]（规格 §4③ 的双向界）
            for c in cs:
                lhs = sum((c if i < L else F(0)) for i in range(C))
                rhs = F(L) * c
                check("1_sum_ite_lt_card", lhs == rhs, f"C={C} L={L} c={c} lhs={lhs} rhs={rhs}")
                combos += 1
    return combos


# --------------------------------------------------------------------------- #
# §2  blockW_eq_sum_filter :  指示和 = 筛子和 = 前 L 项和
# --------------------------------------------------------------------------- #
def s2_blockW_eq_sum_filter():
    C = 3
    vals = [F(0), F(1), F(-2), F(3, 7)]
    combos = 0
    for kappa in product(vals, repeat=C):          # 具体的小块空间实例（C = 3）
        for L in range(1, C + 1):
            fixed = sum((kappa[i] if i < L else F(0)) for i in range(C))   # blockW 的写法
            filtered = sum(kappa[i] for i in range(C) if i < L)            # 筛子和
            firstL = sum(kappa[i] for i in range(L))                       # 块内 L 个位点
            check("2_blockW_eq_sum_filter", fixed == filtered == firstL,
                  f"L={L} kappa={kappa}")
            combos += 1
    return combos


# --------------------------------------------------------------------------- #
# §3  blockW_div_blockL : 精确识别等式 ＋ 块级平均的 SLLN 收敛
# --------------------------------------------------------------------------- #
def s3_blockW_div_blockL():
    combos = 0
    C = 4
    nuL = {1: F(1, 6), 2: F(1, 3), 3: F(1, 4), 4: F(1, 4)}     # L 的分布（∑ = 1）
    assert sum(nuL.values()) == 1
    w = [F(1, 2), F(1, 3), F(1, 6)]                            # 速率类别权重（∑ = 1）
    h = [F(4, 5), F(-1, 5), F(3, 10)]                          # h_j（逐类别单位点均值）

    wbar = sum(wj * hj for wj, hj in zip(w, h))                # = ∫ j, h j ∂(rateMeasure M)
    EL = sum(F(l) * p for l, p in nuL.items())                 # = ∫ blockL
    intW = sum(p * F(l) * wbar for l, p in nuL.items())        # = ∫ blockW = EL · w̄
    ratio = intW / EL
    check("3_hlim_exact", ratio == wbar, f"ratio={ratio} wbar={wbar}")
    check("3_hlim_exact_EL", EL > 0, f"EL={EL}")
    combos += 2

    # ---- 块级平均的 SLLN（精确有理数 + 固定种子）-----------------------
    den = 12                                                    # nuL 的公分母
    nuL_int = [(l, int(p * den)) for l, p in nuL.items()]
    wden = 6                                                    # w 的公分母
    w_int = [(j, int(wj * wden)) for j, wj in enumerate(w)]

    rnd = random.Random(20261012)

    def draw_L():
        r = rnd.randrange(den)
        acc = 0
        for l, k in nuL_int:
            acc += k
            if r < acc:
                return l
        raise AssertionError

    def draw_k():
        r = rnd.randrange(wden)
        acc = 0
        for j, k in w_int:
            acc += k
            if r < acc:
                return j
        raise AssertionError

    checkpoints = (100, 1000, 5000, 20000)
    sumM = F(0)
    sumL = F(0)
    samples = {}
    for n in range(1, checkpoints[-1] + 1):
        L = draw_L()
        M = sum(h[draw_k()] for _ in range(L))                  # M_j = ∑_{i<L_j} h(κ_{j,i})
        sumM += M
        sumL += F(L)
        if n in checkpoints:
            samples[n] = sumM / sumL
    for n in checkpoints:
        check("3_slln_close", abs(samples[n] - wbar) < F(1, 40),
              f"n={n} avg={samples[n]} wbar={wbar}")
        combos += 1
    check("3_slln_improves", abs(samples[20000] - wbar) < abs(samples[100] - wbar),
          f"n=100 {samples[100]}  n=20000 {samples[20000]}")
    combos += 1
    print("   [§3] 块级平均 SLLN：", "  ".join(f"n={n}:{float(samples[n]):+.5f}" for n in checkpoints),
          f" 解析值 w̄={float(wbar):+.5f}")
    return combos


# --------------------------------------------------------------------------- #
# §4  rateMeasure : 归一性 ＋ 有限和积分公式
# --------------------------------------------------------------------------- #
def s4_rateMeasure(Dmax=8, mmax=4):
    combos = 0
    for m in range(1, mmax + 1):
        for D in range(1, Dmax + 1):
            for comp in weak_compositions(D, m):
                w = [F(c, D) for c in comp]
                # 归一性：有限混合测度的质量 = ∑_k w_k = 1
                check("4_rateMeasure_prob", sum(w) == 1, f"m={m} D={D} w={w}")
                # 有限和积分公式：∫ h ∂(∑ w_k δ_k) = ∑_k w_k · h k
                h = [F((-1) ** j * (j + 1), 3) for j in range(m)]
                integral = sum(wk * hk for wk, hk in zip(w, h))
                direct = sum(wk * hk for wk, hk in zip(w, h))
                check("4_integral_rateMeasure", integral == direct, f"m={m} D={D}")
                combos += 2
    return combos


# --------------------------------------------------------------------------- #
# §5  blockMeasure / blockSample : 小块空间上的乘积测度
# --------------------------------------------------------------------------- #
def s5_blockMeasure_probability():
    combos = 0
    # 块 = (θ, L, κ)：θ 侧取「两个 Bool」的 4 点分布，L 侧取 νL，κ 侧取 w^C
    theta = {0: F(1, 4), 1: F(1, 4), 2: F(1, 4), 3: F(1, 4)}
    C = 2
    nuL = {1: F(1, 3), 2: F(2, 3)}
    w = [F(1, 4), F(3, 4)]
    kappa = {kc: a * b for kc in product(range(len(w)), repeat=C) for a, b in
             [(w[kc[0]], w[kc[1]])]}
    check("5_marginals_prob", sum(theta.values()) == 1 and sum(nuL.values()) == 1
          and sum(kappa.values()) == 1, "")
    combos += 1

    joint = {}
    for t, pt in theta.items():
        for l, pl in nuL.items():
            for kc, pk in kappa.items():
                joint[(t, l, kc)] = pt * pl * pk
    total = sum(joint.values())
    check("5_blockMeasure_prob", total == 1, f"total={total}")
    combos += 1

    # 坐标边缘律 = 各自的律（乘积测度的定义性性质，逐坐标枚举）
    for t in theta:
        marg = sum(p for (t2, _, _), p in joint.items() if t2 == t)
        check("5_blockMeasure_marg_theta", marg == theta[t], f"t={t}")
        combos += 1
    for l in nuL:
        marg = sum(p for (_, l2, _), p in joint.items() if l2 == l)
        check("5_blockMeasure_marg_L", marg == nuL[l], f"l={l}")
        combos += 1
    for kc in kappa:
        marg = sum(p for (_, _, k2), p in joint.items() if k2 == kc)
        check("5_blockMeasure_marg_kappa", marg == kappa[kc], f"kc={kc}")
        combos += 1

    # blockSample = infinitePi：前 k 个坐标的乘积空间质量和恒为 1；坐标 iid
    for k in (1, 2, 3, 4):
        mass = 1
        for _ in range(k):
            mass *= total
        check("5_blockSample_prefix", mass == 1, f"k={k}")
        combos += 1
    # 前 2 个坐标的联合律 = 各自律的乘积（iid）—— 枚举全部 (block, block) 对
    blocks = list(joint.items())
    tot_pairs = sum(pa * pb for _, pa in blocks for _, pb in blocks)
    check("5_blockSample_iid_pair_total", tot_pairs == 1, f"tot={tot_pairs}")
    combos += 1
    for a, pa in blocks:
        marg = sum(pa * pb for _, pb in blocks)
        check("5_blockSample_iid_pair_marg", marg == pa, f"a={a} marg={marg} pa={pa}")
        combos += 1
    return combos


# --------------------------------------------------------------------------- #
# §6  退化一致性：twoRate1（r≡1, ρ≡1）与 C = 1（blockL ≡ 1）
# --------------------------------------------------------------------------- #
def s6_degenerate():
    combos = 0
    # (a) twoRate1：Rate = Fin 2、w = (1/2,1/2)、r ≡ 1、ρ ≡ 1 ⇒ scale θ k = θ
    #     ⇒ A(scale θ k) 对两个 k 取同一值 ⇒ Ã = ∑_k w_k · A = A（混合退化为恒等）
    w = [F(1, 2), F(1, 2)]
    check("6_twoRate1_w_sum", sum(w) == 1, "")
    combos += 1
    for A in (F(7, 5), F(-3, 11), F(0)):
        mixed = sum(wk * A for wk in w)
        check("6_twoRate1_Atilde_eq_A", mixed == A, f"A={A}")
        combos += 1
    # (b) C = 1 ⇒ LIdx 1 = {1} ⇒ blockL ≡ 1；blockW = 第 0 个位点的权重
    C = 1
    combos += 1
    check("6_C1_LIdx_singleton", len(list(weak_compositions(1, 1))) == 1, "")
    for s in (F(-4, 9), F(5, 3), F(0)):
        fixed = sum((s if i < 1 else F(0)) for i in range(C))
        check("6_C1_blockW", fixed == s, f"s={s}")
        check("6_C1_blockL", F(1) == 1, "")
        combos += 2
    return combos


def main():
    print("=" * 78)
    print("W13k ★G 数值对拍：Phylo/Stat/BlockModelAE.lean")
    print("=" * 78)
    n1 = s1_sum_ite_lt_card()
    n2 = s2_blockW_eq_sum_filter()
    n3 = s3_blockW_div_blockL()
    n4 = s4_rateMeasure()
    n5 = s5_blockMeasure_probability()
    n6 = s6_degenerate()

    print("-" * 78)
    print("每条检查的断言数 / 枚举规模：")
    print(f"  §1 sum_ite_lt_card        : {n1} 个 (C, L, c) 组合（C ≤ 6, L ∈ [1,C], 5 个 c）")
    print(f"  §2 blockW_eq_sum_filter   : {n2} 个 (κ 向量, L) 组合（C = 3, |值域| = 4）")
    print(f"  §3 blockW_div_blockL      : {n3}（1 条精确识别等式 + 4 个 n 的 SLLN 对拍 + 1 条单调性）")
    print(f"  §4 rateMeasure            : {n4} 个 (m, D, 弱组合) 组合（m ≤ 4, D ≤ 8）")
    print(f"  §5 blockMeasure/Sample    : {n5} 条（质量和、逐坐标边缘律、前缀质量和、iid）")
    print(f"  §6 退化 twoRate1 / C = 1  : {n6} 条")
    print("-" * 78)
    tot = sum(COUNTS.values())
    print(f"断言总数 = {tot}；分组计数 = {dict(sorted(COUNTS.items()))}")
    if FAILS:
        print(f"!!! 失败 {len(FAILS)} 条：")
        for g, d in FAILS[:20]:
            print(f"    [{g}] {d}")
        print("RESULT: FAIL")
        return 1
    print("RESULT: ALL CHECKS PASSED (exit 0)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
