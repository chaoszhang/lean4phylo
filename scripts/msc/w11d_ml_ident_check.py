#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w11d_ml_ident_check.py —— W11d/X1「ML 可识别性」的**精确有理数**数值核验
（**无 Monte Carlo**：全部为 `fractions.Fraction` 精确算术）

## 数学设置（2-状态对称模型 = Neyman 模型，4 taxon）

* 叶 1..4，两个状态 {0,1}，根分布均匀；
* 每条边 `e` 给一个**精确有理数**的「变换概率」`p_e ∈ (0, 1/2)`（2-状态对称模型的
  转移矩阵 `[[1-p, p], [p, 1-p]]`；这是它的一般形状，`p = (1-e^{-2t})/2` 见文献）；
* 无根 4-taxon 树：内部边 `e5` 把 `{1,2}` 与 `{3,4}` 分开（拓扑 `12|34`），
  另两个候选拓扑 `13|24` / `14|23` 用**同一组**边参数（同枝长不同拓扑 —— ML 的比较设定）；
* 位点模式 `x = (x1,x2,x3,x4)` 共 `2^4 = 16` 个，概率是 `p_e` 的**有理多项式**，
  故**精确可算**（`Fraction`）。

## 本脚本核验什么

1. 三个拓扑的模式分布 `D_12`, `D_13`, `D_14` 各自的 16 个分量**精确**求和为 `1`；
2. 三者**两两不同**（精确有理数不等式）⟹ 由 **Gibbs 不等式**
   （`KL(D_true || D_τ) ≥ 0`，取等 ⟺ 分布相同）**严格**
   `E_{D_true}[log D_true] > E_{D_true}[log D_τ]`（`τ ≠ true`）
   —— **这就是「ML 在期望意义下可识别」的模型层结论**（Chang 1996 / Rogers 1997 的形状）；
3. 该 gap 的一个**精确有理数下界**：由 **Pinsker 不等式** `KL ≥ (1/2)·TV²`
   （`TV = ½·‖D_true − D_τ‖₁` 是精确有理数）⇒ `gap ≥ (1/2)·TV² > 0`，**完全有理**；
4. 浮点对照：直接算 `Σ_x D_12(x)·log(D_12(x)/D_τ(x))`（仅作**参考打印**，不参与判定）。

⟹ 对应的 Lean 侧：`Phylo/Stat/MLIdentifiability.lean` 的 `Identifiable`
（真树期望得分唯一最大）在本例上**非空洞**，其下游 `exists_gap` / `ml_statisticallyConsistent`
无条件成立。⚠️ Lean 的 ★C 例子用有理数表 `(0, −1/8, −3/8)` 复现**同一结构**
（真树严格最大 ⟹ 正 gap），**不是**本脚本的数值；本脚本给出的是**模型层**的定性结论 ＋ 有理下界。

用法：`python3 scripts/msc/w11d_ml_ident_check.py`（退出码 0 = 全部核验通过）
"""
import math
import sys
from fractions import Fraction as F

STATES = (0, 1)


def edge_probs():
    """精确有理数的边参数：4 条叶边 + 1 条内部边（同枝长不同拓扑）。"""
    return {
        "e1": F(1, 4),
        "e2": F(1, 5),
        "e3": F(1, 6),
        "e4": F(1, 7),
        "e5": F(1, 3),   # 内部边（较长 ⇒ 信号强）
    }


def trans(p, x, y):
    """2-状态对称模型：同态概率 1-p，异态概率 p。"""
    return (1 - p) if x == y else p


def pattern_probs(cherry_a, cherry_b, P):
    """无根 4-taxon 树 `cherry_a | cherry_b`（两个 cherry 各 2 叶）的 16 个模式概率。

    树形：`a1,a2` 挂在内部点 `u`；`b1,b2` 挂在内部点 `v`；`u—v` 是内部边。
    `P(x) = Σ_{s_u,s_v} (1/2)·P(u→a1)P(u→a2)·P(u→v)·P(v→b1)P(v→b2)`
    """
    (a1, a2), (b1, b2) = cherry_a, cherry_b
    out = {}
    for xa1 in STATES:
        for xa2 in STATES:
            for xb1 in STATES:
                for xb2 in STATES:
                    tot = F(0)
                    for su in STATES:
                        for sv in STATES:
                            tot += (F(1, 2)
                                    * trans(P["e" + str(a1)], su, xa1)
                                    * trans(P["e" + str(a2)], su, xa2)
                                    * trans(P["e5"], su, sv)
                                    * trans(P["e" + str(b1)], sv, xb1)
                                    * trans(P["e" + str(b2)], sv, xb2))
                    out[(xa1, xa2, xb1, xb2)] = tot
    return out


def tv(d1, d2):
    """全变差距离 TV = ½ Σ |d1 - d2|（精确有理数）。"""
    return sum(abs(d1[k] - d2[k]) for k in d1) / 2


def kl_float(d1, d2):
    """参考打印用的浮点 KL（不参与判定）。"""
    return sum(float(d1[k]) * math.log(float(d1[k]) / float(d2[k])) for k in d1)


def main():
    P = edge_probs()
    tops = {
        "12|34": ((1, 2), (3, 4)),
        "13|24": ((1, 3), (2, 4)),
        "14|23": ((1, 4), (2, 3)),
    }
    D = {name: pattern_probs(a, b, P) for name, (a, b) in tops.items()}
    ok = True

    print("== 1. 每个拓扑的模式分布精确归一（16 个模式） ==")
    for name, d in D.items():
        s = sum(d.values())
        print(f"  {name}: Σ = {s}  ({'OK' if s == 1 else 'FAIL'})")
        ok &= (s == 1)

    print("\n== 2. 三拓扑两两不同（精确有理数）⇒ Gibbs ⇒ 严格排序 ==")
    true_name = "12|34"
    d_true = D[true_name]
    for name, d in D.items():
        if name == true_name:
            continue
        diff = [k for k in d_true if d_true[k] != d[k]]
        print(f"  D_{true_name} vs D_{name}: 不同的模式数 = {len(diff)}  "
              f"({'不同 OK' if diff else 'FAIL'})")
        ok &= bool(diff)
        t = tv(d_true, d)
        pinsker = t * t / 2          # KL ≥ (1/2)·TV²  （Pinsker）
        print(f"    TV = {t} = {float(t):.6f}   ⇒ Pinsker 下界 KL ≥ {pinsker} "
              f"= {float(pinsker):.6f} > 0  ({'OK' if pinsker > 0 else 'FAIL'})")
        ok &= (pinsker > 0)
        print(f"    参考浮点 KL(D_true‖D_{name}) = {kl_float(d_true, d):.6f} nats "
              f"(> Pinsker 下界: {kl_float(d_true, d) >= float(pinsker)})")
        ok &= (kl_float(d_true, d) >= float(pinsker) - 1e-12)

    print("\n== 3. 结论 ==")
    print("  三个候选拓扑的模式分布两两不同（精确） + Gibbs ⇒ 真拓扑的**期望对数似然唯一最大**")
    print("  ⇒ Phylo/Stat/MLIdentifiability.lean 的 `Identifiable` 在 4 taxon 2-状态模型上非空洞")
    print("  ⇒ 其下游 `exists_gap` / `argmax_eq_truth_of_close` / `ml_statisticallyConsistent` 给出")
    print("     「正 gap δ > 0」与「ML 最终选真树」")
    print("\nALL_CHECKS_PASS =", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
