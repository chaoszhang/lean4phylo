#!/usr/bin/env python3
"""
scripts/msc/msc_quartet_prob.py —— W10c 交付的**独立精确复核**

复核对象：`Phylo/Stat/MSCProof.lean` 里 `Fin 4` 上由 Kingman 溯祖构造的 MSC quartet 概率表。

三件事：
  ① **穷举** `Fin 4` 的全部有向 split（= 2 元非空真子集对），按 `sideA.card` 分类，
     数出 `2|2` 有向 split = 6 个、`1|3` 有向 split = 8 个（对应 Lean 的 `card_two_two`
     与「其余为 0」）。
  ② **符号（精确有理数）**验证概率表之和恒等于 1：把 `x = e^{−t}` 当作自由符号，
     检查 `pConc + 2·pDisc ≡ 1`（多项式恒等式，误差 0）。
  ③ **严格不等式**（`MSCFreq.majorizes` 的全部解析内容）：
     `0 < t` 时 `pDisc/2 < pConc/2` 且 `0 < pConc/2`。

⚠️ 全部用 `fractions.Fraction`（有理数）与**符号多项式**，不用 Monte Carlo。
"""
from fractions import Fraction as F
from itertools import combinations
from math import exp

X = (0, 1, 2, 3)

def directed_splits():
    """全部**有向** split：(sideA, sideB)，sideA 非空真子集。"""
    out = []
    for r in range(1, 4):
        for A in combinations(X, r):
            Aset = frozenset(A)
            Bset = frozenset(set(X) - Aset)
            out.append((Aset, Bset))
    return out

def main():
    print("=" * 78)
    print("① 穷举 `Fin 4` 的有向 split 计数")
    ds = directed_splits()
    n22 = [s for s in ds if len(s[0]) == 2]
    n13 = [s for s in ds if len(s[0]) != 2]
    print(f"   有向 split 总数 = {len(ds)}（2·(2^4−2)/2 = 14）")
    print(f"   `2|2` 有向 split = {len(n22)}   （Lean `card_two_two` 断言 6）")
    print(f"   `1|3` 有向 split = {len(n13)}   （Lean 里取值 0）")
    assert len(n22) == 6 and len(n13) == 8

    # 一致性谓词：sideA 含 0,1 同在或同不在（= sideA ∈ {{0,1},{2,3}}）
    conc = [s for s in n22 if ((0 in s[0]) == (1 in s[0]))]
    disc = [s for s in n22 if s not in conc]
    print(f"   一致（concordant）有向 split = {len(conc)}（Lean `card_isConc` 断言 2）")
    print(f"   不一致 `2|2` 有向 split   = {len(disc)}（Lean `card_notConc_two` 断言 4）")
    assert len(conc) == 2 and len(disc) == 4

    # 3 个无向拓扑，每个恰 2 个有向 split
    topo = {}
    for s in n22:
        key = frozenset({s[0], s[1]})
        topo.setdefault(key, []).append(s)
    print(f"   无向 `2|2` 拓扑 = {len(topo)} 个，每个恰 {sorted({len(v) for v in topo.values()})} 个有向 split")

    print("=" * 78)
    print("② 符号（精确有理数）验证：把 x = e^{−t} 当自由符号")
    # 概率表：一致的有向 split 各 pConc/2，不一致的各 pDisc/2，其余 0
    # pConc = 1 − (2/3)x ; pDisc = (1/3)x        （两者的 x 系数用 Fraction 表示）
    pConc = (F(1), F(-2, 3))     # 常数项, x 的系数
    pDisc = (F(0), F(1, 3))
    def add(a, b): return (a[0] + b[0], a[1] + b[1])
    def smul(c, a): return (c * a[0], c * a[1])
    half = F(1, 2)
    total = (F(0), F(0))
    for _ in conc:
        total = add(total, smul(half, pConc))
    for _ in disc:
        total = add(total, smul(half, pDisc))
    print(f"   Σ over the 14 directed splits of p = {total[0]} + {total[1]}·x   （要求 1 + 0·x）")
    assert total == (F(1), F(0)), total
    print("   ⇒ **误差恰为 0**（有理数、符号恒等式）✓  —— 对应 Lean `mscP_sum`")

    print("=" * 78)
    print("③ 严格不等式（`majorizes` 的解析内容）")
    ok = True
    for t in [F(1, 100), F(1, 10), F(1, 2), F(1), F(2), F(5), F(20)]:
        tf = float(t)
        x = exp(-tf)                      # 数值仅用于**展示**；下面用符号验证
        pc = 1 - F(2, 3) * F(x).limit_denominator(10**12)
        pd = F(1, 3) * F(x).limit_denominator(10**12)
        print(f"   t={tf:>6.2f}  e^-t={x:.12f}  pConc≈{float(pc):.12f}  pDisc≈{float(pd):.12f}  "
              f"disc<conc? {pd < pc}  conc>0? {pc > 0}")
        ok = ok and (pd < pc) and (pc > 0)
    # 符号证明：pDisc/2 < pConc/2  ⟺  (1/3)x < 1 − (2/3)x  ⟺  x < 1；
    #           0 < pConc/2        ⟺  x < 3/2。  0 < t ⟹ 0 < x < 1。
    print("   符号：pDisc/2 < pConc/2 ⟺ x < 1；0 < pConc/2 ⟺ x < 3/2；0<t ⇒ 0<x<1 ⇒ 两者均成立 ✓")
    assert ok

    print("=" * 78)
    print("④ **测度层**（`Phylo/Stat/MSCMeasure.lean`）：内部枝上的概率划分")
    # 把 x = e^{−t} 当自由符号：P(τ₂ ≤ t) = 1 − x, P(τ₂ > t) = x
    P_le = (F(1), F(-1))     # 常数项, x 的系数
    P_gt = (F(0), F(1))
    tot = (P_le[0] + P_gt[0], P_le[1] + P_gt[1])
    print(f"   P(τ₂ ≤ t) + P(τ₂ > t) = {tot[0]} + {tot[1]}·x   （要求 1 + 0·x）")
    assert tot == (F(1), F(0)), tot
    # 一致概率的测度层混合：P(≤t)·1 + P(>t)·rootTopoProb，rootTopoProb = 1/3
    third = F(1, 3)
    mix = (P_le[0] * 1 + P_gt[0] * third, P_le[1] * 1 + P_gt[1] * third)
    print(f"   P(≤t)·1 + P(>t)·(1/3) = {mix[0]} + {mix[1]}·x   （要求 1 + (−2/3)·x = pConc）")
    assert mix == pConc, (mix, pConc)
    print("   ⇒ **误差恰为 0** ✓  —— 对应 Lean `branch_partition` / `mscConcordant_eq_measure`")

    print("=" * 78)
    print("VERDICT: PASS")

if __name__ == "__main__":
    main()
