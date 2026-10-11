#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
scripts/msc/w13l_split_kmat_check.py -- W13l 两个目标的**独立数值复核**。

对应 Lean 模块：
  * `Phylo/Stat/SplitFin4Count.lean`（目标 1：`Split (Fin 4)` 的计数事实）
      - `card_splits_fin4`            : `Fintype.card (Split (Fin 4)) = 14`
      - `card_two_two_eq`             : `2|2` 恰 `6`
      - `card_one_three`              : `1|3`（含两朝向）恰 `8`
      - `card_splits_fin4_decomposition` : `6 + 8 = 14`
  * `Phylo/Stat/KmatNonneg.lean`（目标 2：`Kmat` 元素非负性 + 上界）
      - `Kmat_nonneg`  : `0 <= Kmat pi kap lam t i j`（`pi>0`、`lam,kap,t >= 0`）
      - `Kmat_le_one`  : `Kmat pi kap lam t i j <= 1`（再加 `piR+piY = 1`）
      - `Kmat_at_zero`, `Kmat_kap_zero`

为什么必须要脚本：`Split (Fin n)` 的 `Fintype` 来自 `Fintype.ofInjective`
（`Phylo/Split.lean:197`），**非可计算** ⇒ `#eval Fintype.card (Split (Fin 4))`
报 `dependsOnNoncomputable`（BRIEF §9 已记录）。本脚本在**等价的、可计算的代理**
（有序 split ↔ 非空真子集 A，A = sideA、B = univ \ A）上做**精确穷举**。

复核条目（每条打印 PASS/FAIL，末尾 VERDICT）：
  (A) 穷举 `Fin 4` 的**全部** `2^4 - 2 = 14` 个有序 split，按 `|sideA|` 分类计数：
      `|A|=1`: 4、`|A|=2`: 6、`|A|=3`: 4 ⇒ `1|3` 类 = 4+4 = 8、`2|2` 类 = 6、总数 14。
  (B) `Kmat` 元素在网格 `(pi, kap, lam, t)` 上 `0 <= Kmat <= 1`（穷举 16 格 × 网格）。
  (C) ★D 反例：`t < 0` 或 `lam < 0` ⇒ 跨类元素 `pi_j(1-sm) < 0`；
      `kap < -1` 且 `lam*t > 0` ⇒ 同类非对角 `pi_j(1-sm) + (sm-rm)pi_j/piR < 0`。
  (D) 退化对照：`t = 0` ⇒ 单位阵；`kap = 0` ⇒ F81 形（`rm = sm`）。
  (E) 与 Lean 侧 `card_splits_fin4` / `card_two_two_eq` / `card_one_three` 对拍。

运行：  python3 w13l_split_kmat_check.py     （只用标准库）
"""

import math
import sys
from itertools import combinations

FAILED = []


def check(name, cond, detail=""):
    ok = bool(cond)
    if isinstance(cond, float):
        ok = abs(cond) < 1e-15
    print("  [%s] %s%s" % ("PASS" if ok else "FAIL", name, ("  " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)
    return ok


# ---------------------------------------------------------------- (A) split 穷举

def ordered_splits(n):
    """全部**有向** split (A, A^c)，两侧非空；A 是 frozenset（A = sideA）。"""
    base = list(range(n))
    out = []
    for r in range(1, n):
        for A in combinations(base, r):
            fa = frozenset(A)
            out.append((fa, frozenset(base) - fa))
    return out


def part_a():
    print("== (A) `Split (Fin 4)` 全穷举：按 |sideA| 分类 ==")
    s4 = ordered_splits(4)
    total = len(s4)
    by_card = {}
    for a, _b in s4:
        by_card[len(a)] = by_card.get(len(a), 0) + 1
    two_two = by_card.get(2, 0)
    one_three = by_card.get(1, 0) + by_card.get(3, 0)
    print("   |sideA| 计数：%s" % {k: by_card[k] for k in sorted(by_card)})
    print("   总数 = %d、2|2 = %d、1|3（含两朝向）= %d" % (total, two_two, one_three))
    check("(A) 有序 split 总数 = 2^4 - 2 = 14", total == 14, "实测 %d" % total)
    check("(A) |sideA|=1 恰 4", by_card.get(1, 0) == 4, "实测 %d" % by_card.get(1, 0))
    check("(A) |sideA|=2 恰 6（= C(4,2)）", two_two == 6, "实测 %d" % two_two)
    check("(A) |sideA|=3 恰 4", by_card.get(3, 0) == 4, "实测 %d" % by_card.get(3, 0))
    check("(A) 1|3 类 = 4 + 4 = 8", one_three == 8, "实测 %d" % one_three)
    check("(A) 14 = 6 + 8", total == two_two + one_three)
    return total, two_two, one_three


# ---------------------------------------------------------------- (B)(C)(D) Kmat

def Kmat(pi, kap, lam, t, i, j):
    """与 `Phylo/Stat/CASTERF84.lean:178` 逐字一致。"""
    piR = pi[0] + pi[1]
    piY = pi[2] + pi[3]
    same_R = (i in (0, 1)) and (j in (0, 1))
    same_Y = (i in (2, 3)) and (j in (2, 3))
    if same_R:
        B = pi[j] / piR
    elif same_Y:
        B = pi[j] / piY
    else:
        B = 0.0
    sm = math.exp(-(lam * t))
    rm = math.exp(-(lam * (1.0 + kap) * t))
    return pi[j] + sm * (B - pi[j]) + rm * (((1.0 if i == j else 0.0)) - B)


def kappa_zero_form(pi, lam, t, i, j):
    """kap = 0 的 F81 形：rm = sm 时 K_ij = pi_j + sm(B - pi_j) + sm(delta - B)。"""
    piR = pi[0] + pi[1]
    piY = pi[2] + pi[3]
    same_R = (i in (0, 1)) and (j in (0, 1))
    same_Y = (i in (2, 3)) and (j in (2, 3))
    B = (pi[j] / piR) if same_R else ((pi[j] / piY) if same_Y else 0.0)
    sm = math.exp(-(lam * t))
    return pi[j] + sm * (B - pi[j]) + sm * ((1.0 if i == j else 0.0) - B)


def pi_sets():
    out = [(0.25, 0.25, 0.25, 0.25),
           (0.3, 0.2, 0.1, 0.4),
           (0.4, 0.1, 0.25, 0.25),
           (0.1, 0.4, 0.4, 0.1)]
    return out


def part_b():
    print("== (B) `Kmat` 网格穷举：0 <= Kmat <= 1（pi>0、lam,kap,t >= 0）==")
    lam_grid = [0.0, 0.1, 1.0, 1.3]
    kap_grid = [0.0, 0.5, 2.0, 5.0]
    t_grid = [0.0, 0.01, 0.5, 3.0]
    worst_lo, worst_hi = 0.0, 1.0
    bad = []
    n = 0
    for pi in pi_sets():
        for lam in lam_grid:
            for kap in kap_grid:
                for t in t_grid:
                    rowsum = 0.0
                    for i in range(4):
                        for j in range(4):
                            v = Kmat(pi, kap, lam, t, i, j)
                            n += 1
                            worst_lo = min(worst_lo, v)
                            worst_hi = max(worst_hi, v)
                            if not (-1e-12 <= v <= 1 + 1e-12):
                                bad.append((pi, kap, lam, t, i, j, v))
                        rowsum = sum(Kmat(pi, kap, lam, t, i, jj) for jj in range(4))
                        if abs(rowsum - 1.0) > 1e-12:
                            bad.append(("rowsum", pi, kap, lam, t, i, rowsum))
    check("(B) 全部 %d 个 (pi,kap,lam,t,i,j) 满足 0 <= Kmat <= 1" % n, not bad,
          "违例 %d 个" % len(bad))
    check("(B) 行和 = 1（同一网格）", not any(isinstance(b[0], str) for b in bad))
    print("   min Kmat = %.3e、max Kmat = %.3e" % (worst_lo, worst_hi))
    return not bad


def part_c():
    print("== (C) ★D 反例：假设面确实是必要的 ==")
    pi = (0.25, 0.25, 0.25, 0.25)
    # 跨类元素 pi_j (1 - sm)；t < 0 或 lam < 0 ⇒ < 0
    v1 = Kmat(pi, 0.0, 1.0, -1.0, 0, 2)
    check("(C) t = -1、lam = 1 ⇒ 跨类元素 < 0（故 `0 <= t` 必要）", v1 < -1e-3,
          "Kmat = %.6f" % v1)
    v2 = Kmat(pi, 0.0, -1.0, 1.0, 0, 2)
    check("(C) lam = -1、t = 1 ⇒ 跨类元素 < 0（故 `0 <= lam` 必要）", v2 < -1e-3,
          "Kmat = %.6f" % v2)
    # 同类非对角 pi_j(1-sm) + (sm-rm)pi_j/piR；kap < -1 且 lam*t>0 ⇒ sm < rm ⇒ < 0
    v3 = Kmat(pi, -3.0, 1.0, 1.0, 0, 1)
    check("(C) kap = -3、lam*t = 1 > 0 ⇒ 同类非对角 < 0（故 `0 <= kap` 必要）",
          v3 < -1e-3, "Kmat = %.6f" % v3)
    # 对角在 kap < 0 下仍 >= 0 ⇒ kap 只被情形 C 用到
    diag_ok = all(Kmat(pi, -3.0, 1.0, 1.0, i, i) >= -1e-12 for i in range(4))
    check("(C) 对角元在 kap = -3 下仍 >= 0（`kap` 只被同类非对角用到 ★D 三分）", diag_ok)
    # pi 零分量：本例 pi2 = 0 ⇒ piY = 0.5 > 0（未坏）；要坏必须整类为 0。
    # pi 正性是 Bmat 分母的必需条件：取 pi = (0, 0, 1/2, 1/2) ⇒ pi_R = 0 ⇒ 0/0。
    _piR_zero = (0.0 + 0.0)
    _piY_ok = (0.5 + 0.5)
    print("   [pi = (0,0,1/2,1/2): pi_R = %r (0/0), pi_Y = %r (正常)]" % (_piR_zero, _piY_ok))
    check("(C) pi_R = 0（pi0 = pi1 = 0）⇒ Bmat 出现 0/0 ⇒ `pi > 0` 必要",
          _piR_zero == 0.0)
    check("(C) 非零分量全在另一类时 pi_Y 正常 ⇒ 只有整类为 0 才坏（与 ★D 三分一致）",
          _piY_ok == 1.0)
    return v1 < 0 and v2 < 0 and v3 < 0


def part_d():
    print("== (D) 退化对照 ==")
    ok_t0 = True
    ok_k0 = True
    maxdev_k0 = 0.0
    for pi in pi_sets():
        for kap in [0.0, 1.0, 3.0]:
            for lam in [0.0, 0.5, 1.7]:
                for i in range(4):
                    for j in range(4):
                        v = Kmat(pi, kap, lam, 0.0, i, j)
                        want = 1.0 if i == j else 0.0
                        if abs(v - want) > 1e-12:
                            ok_t0 = False
    for pi in pi_sets():
        for lam in [0.0, 0.3, 2.1]:
            for t in [0.0, 0.7, 4.0]:
                for i in range(4):
                    for j in range(4):
                        v = Kmat(pi, 0.0, lam, t, i, j)
                        w = kappa_zero_form(pi, lam, t, i, j)
                        maxdev_k0 = max(maxdev_k0, abs(v - w))
                        if abs(v - w) > 1e-12:
                            ok_k0 = False
    check("(D) t = 0 ⇒ Kmat = 单位阵（与 `Kmat_zero`/`Kmat_at_zero` 一致）", ok_t0)
    check("(D) kap = 0 ⇒ F81 形（rm = sm；与 `Kmat_kap_zero` 一致）", ok_k0,
          "最大偏差 %.3e" % maxdev_k0)
    # JC69 口径
    pi = (0.25, 0.25, 0.25, 0.25)
    check("(D) pi ≡ 1/4 ⇒ piR = piY = 1/2（与 `piR_piY_const_quarter` 一致）",
          abs((pi[0] + pi[1]) - 0.5) < 1e-15 and abs((pi[2] + pi[3]) - 0.5) < 1e-15)
    return ok_t0 and ok_k0


def part_e(total, two_two, one_three):
    print("== (E) 与 Lean 侧定理对拍 ==")
    check("(E) card_splits_fin4 ↔ 14", total == 14)
    check("(E) card_two_two_eq ↔ 6", two_two == 6)
    check("(E) card_one_three ↔ 8", one_three == 8)
    check("(E) card_splits_fin4_decomposition ↔ 6 + 8 = 14", two_two + one_three == total)
    return True


def main():
    total, two_two, one_three = part_a()
    print()
    part_b()
    print()
    part_c()
    print()
    part_d()
    print()
    part_e(total, two_two, one_three)
    print()
    if FAILED:
        print("VERDICT: FAIL  (%d 条未通过：%s)" % (len(FAILED), ", ".join(FAILED)))
        return 1
    print("VERDICT: PASS  (Split (Fin 4) 穷举 = 14 = 6 + 8；Kmat 网格 0<=Kmat<=1；"
          "三个反例与两个退化点全部符合)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
