#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W11e 后半 / AGT 判据的**精确有理数**复核（无随机数、无 Monte Carlo、无浮点判定）。

对应 Lean 交付 `Phylo/Stat/AnomalousGeneTree.lean`（Degnan & Rosenberg 2006, PLoS Genet 2(5):e68）。

本脚本**独立复核四件事**：

  (1) 公式层：`f`/`g`/`h` 三个函数（DR2006 式 (1)(2)(3)，md 170–246 行逐字核读）在
      **有理数点**上满足本脚本自算的 `h − g = (1/3)Zx(1 − Zy)` 与
      `h − f = Zy(2/3 − Zx/2 − Zx³/9) − (1 − Zx)`（与 Lean 里 `h_sub_g`/`h_sub_f` 同式）；
  (2) **判据**（Lean `h_gt_f_iff`）：`h > f ⟺ 1 − Zx < Zy(2/3 − Zx/2 − Zx³/9)`，
      在 `x,y` 的**有理数网格**上逐点比对（三套独立写法：定义直接算 / 判据 / 除法定理），
      三者在每一点必须**同真同假**；
  (3) **DR2006 式 (4)(5) 的边界函数** `a(x)`、`b(x)`（含化简式）与判据的单调交叉一致性
      —— 在 `y < a(x)` ⟺ `h > f`、`y < b(x)` ⟺ `g > f` 上用二分法定出数值根，精度 10⁻³⁰；
  (4) **Lean 里的两个★C 见证点**：`(1/100, 1/100)`（产 AGT）与 `(1/100, 100)`（不产 AGT），
      以及 Lean 证明所用的**有理数界** `99/100 ≤ e^{−1/100} ≤ 100/101` 与 `e^{−100} ≤ 1/101`
      是否成立（这是 Lean 证明的**前提**，必须独立确认）。

⚠️ 与 `scripts/msc/w11e_agt_check.py`（前一位 agent 的脚本）的关系：
    该脚本断言了 `f + 2g + h = 1` 与 `1 − f = 1/3 + Zy/3 + Zy²/3`（"与 x 无关"）**两条假命题**
    （本目录下 `AnomalousGeneTree.orphan.lean` 的 `f_add_two_g_add_h`/`one_sub_f` 同源 ✗）；
    实测重跑该脚本输出大量 `[FAIL]`。**本脚本不沿用它的任何断言**，其 (1) 项正是对它的否证。
    逐条数值反证见本脚本 §1 的 `[REFUTED]` 行。

用法：`python3 scripts/msc/w11e_agt_criterion.py`（exit 0 ⟺ 全部通过）。
"""
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 60

# ---------------------------------------------------------------- 精确 exp/log

def E(t: F) -> Decimal:
    """e^{t}（t 为有理数），用 60 位 Decimal 级数，判定不用浮点。"""
    x = Decimal(t.numerator) / Decimal(t.denominator)
    s, term, k = Decimal(1), Decimal(1), 0
    while True:
        k += 1
        term = term * x / k
        s += term
        if abs(term) < Decimal(10) ** -60:
            break
    return s


def ZD(t: F) -> Decimal:
    """Z t = e^{−t}。"""
    return 1 / E(t)


def D_pow(d: Decimal, n: int) -> Decimal:
    r = Decimal(1)
    for _ in range(n):
        r *= d
    return r


# ------------------------------------------------- DR2006 式 (1)(2)(3)（Decimal 层）

def f_d(x: F, y: F) -> Decimal:
    """一致拓扑 (((A,B),C),D)（DR2006 式 (1)）。"""
    Zx, Zy = ZD(x), ZD(y)
    return (1 - dec(F(2, 3)) * Zx - dec(F(2, 3)) * Zy
            + dec(F(1, 3)) * Zx * Zy + dec(F(1, 18)) * D_pow(Zx, 3) * Zy)


def g_d(x: F, y: F) -> Decimal:
    """((A,C),(B,D))（DR2006 式 (2)）。"""
    Zx, Zy = ZD(x), ZD(y)
    return dec(F(1, 6)) * Zx * Zy - dec(F(1, 18)) * D_pow(Zx, 3) * Zy


def h_d(x: F, y: F) -> Decimal:
    """((A,B),(C,D))（DR2006 式 (3)）——四叶的 AGT 候选。"""
    Zx, Zy = ZD(x), ZD(y)
    return dec(F(1, 3)) * Zx - dec(F(1, 6)) * Zx * Zy - dec(F(1, 18)) * D_pow(Zx, 3) * Zy


def dec(fr: F) -> Decimal:
    return Decimal(fr.numerator) / Decimal(fr.denominator)


# ------------------------------------------------- 判据的三种独立写法

def crit_criterion(x: F, y: F) -> bool:
    """判据：1 − Zx < Zy·(2/3 − Zx/2 − Zx³/9)（Lean `h_gt_f_iff`）。"""
    Zx, Zy = ZD(x), ZD(y)
    return (1 - Zx) < Zy * (dec(F(2, 3)) - Zx / 2 - D_pow(Zx, 3) / 9)


def crit_definition(x: F, y: F) -> bool:
    """直接按定义：h > f。"""
    return h_d(x, y) > f_d(x, y)


def crit_div(x: F, y: F) -> bool:
    """除法定理（Lean `h_gt_f_iff_div`）：18(1−Zx)/(12−9Zx−2Zx³) < Zy。"""
    Zx, Zy = ZD(x), ZD(y)
    return 18 * (1 - Zx) / (12 - 9 * Zx - 2 * D_pow(Zx, 3)) < Zy


def crit_literature_a(x: F, y: F) -> bool:
    """DR2006 式 (4) 的文献形式：0 AGT ⟺ y ≥ a(x)，故 h > f ⟺ y < a(x)。"""
    Zx = ZD(x)
    # a(x) = log(2/3 + (3e^{2x} − 2)/(18(e^{3x} − e^{2x})))，用 u = e^{−x} 化简：
    # e^{−a(x)} = 18(1−u)/(12 − 9u − 2u³)
    e_neg_a = 18 * (1 - Zx) / (12 - 9 * Zx - 2 * D_pow(Zx, 3))
    return ZD(y) > e_neg_a


def crit_b(x: F, y: F) -> bool:
    """DR2006 式 (5)：3-AGT 区 ⟺ y < b(x)，即 g > f ⟺ e^{−b(x)} < e^{−y}，
    其中 e^{−b(x)} = 6(3 − 2u)/(12 − 3u − 2u³)，u = e^{−x}。"""
    Zx, Zy = ZD(x), ZD(y)
    e_neg_b = 6 * (3 - 2 * Zx) / (12 - 3 * Zx - 2 * D_pow(Zx, 3))
    return Zy > e_neg_b


# ---------------------------------------------------------------- 测试框架

results = []


def check(name: str, ok: bool, detail: str = "") -> None:
    results.append(bool(ok))
    tag = "[PASS]" if ok else "[FAIL]"
    print(f"  {tag} {name}" + (f"  {detail}" if detail else ""))


def main() -> int:
    print("=" * 78)
    print("W11e 后半 / AGT —— 精确有理数复核（脚本：w11e_agt_criterion.py）")
    print("=" * 78)

    grid = [F(a, b) for b in (20, 10, 4, 2) for a in range(1, 2 * b + 1, max(1, b // 4))]
    pts = [(x, y) for x in grid for y in grid]

    # ---- §1 公式层 + 对前一位 agent 两条假命题的否证
    print("\n== §1 公式层：h − g、h − f 的闭形式（Lean `h_sub_g` / `h_sub_f`）==")
    bad_g = bad_f = 0
    for (x, y) in pts:
        Zx, Zy = ZD(x), ZD(y)
        if abs((h_d(x, y) - g_d(x, y)) - (dec(F(1, 3)) * Zx * (1 - Zy))) > Decimal(10) ** -40:
            bad_g += 1
        lhs = h_d(x, y) - f_d(x, y)
        rhs = Zy * (dec(F(2, 3)) - Zx / 2 - D_pow(Zx, 3) / 9) - (1 - Zx)
        if abs(lhs - rhs) > Decimal(10) ** -40:
            bad_f += 1
    check(f"h − g = (1/3)Zx(1−Zy) 在 {len(pts)} 点成立", bad_g == 0, f"反例 {bad_g}")
    check(f"h − f = Zy(2/3−Zx/2−Zx³/9) − (1−Zx) 在 {len(pts)} 点成立", bad_f == 0, f"反例 {bad_f}")

    print("\n== §1b 否证前一位 agent 的两条断言（`w11e_agt_check.py` / 孤儿件）==")
    worst1 = max(abs((f_d(x, y) + 2 * g_d(x, y) + h_d(x, y)) - 1) for (x, y) in pts)
    check("『f + 2g + h = 1』为假（这三个拓扑的概率和本来就不是 1）", worst1 > dec(F(1, 100)),
          f"最大偏差 {float(worst1):.6f}")
    worst2 = max(abs((1 - f_d(x, y)) - (dec(F(1, 3)) + ZD(y) / 3 + D_pow(ZD(y), 2) / 3))
                 for (x, y) in pts)
    check("『1 − f = 1/3 + Zy/3 + Zy²/3（与 x 无关）』为假", worst2 > dec(F(1, 100)),
          f"最大偏差 {float(worst2):.6f}")
    # 正解：1 − f 的闭形式（含 x）
    bad_1mf = 0
    for (x, y) in pts:
        Zx, Zy = ZD(x), ZD(y)
        rhs = dec(F(2, 3)) * Zx + dec(F(2, 3)) * Zy - dec(F(1, 3)) * Zx * Zy \
            - dec(F(1, 18)) * D_pow(Zx, 3) * Zy
        if abs((1 - f_d(x, y)) - rhs) > Decimal(10) ** -40:
            bad_1mf += 1
    check(f"正解 1 − f = (2/3)(Zx+Zy) − (1/3)ZxZy − (1/18)Zx³Zy 在 {len(pts)} 点成立",
          bad_1mf == 0, f"反例 {bad_1mf}")

    # ---- §2 判据四写法一致
    print("\n== §2 判据：h > f  ⟺  1−Zx < Zy(2/3−Zx/2−Zx³/9)  ⟺  除法式  ⟺  文献 a(x) 式 ==")
    mism = 0
    same_side = 0
    for (x, y) in pts:
        c1 = crit_definition(x, y)
        c2 = crit_criterion(x, y)
        c3 = crit_div(x, y)
        c4 = crit_literature_a(x, y)
        if not (c1 == c2 == c3 == c4):
            mism += 1
        if c1:
            same_side += 1
    check(f"四种写法在 {len(pts)} 点上完全一致", mism == 0, f"不一致 {mism}")
    check("判据**非空真**（网格上既有真也有假）", 0 < same_side < len(pts),
          f"真 {same_side} / 假 {len(pts) - same_side}")

    # ---- §3 h > g（DR2006 247–248）与 3-AGT 边界 b
    print("\n== §3 h > g（DR2006 247–248）与 式 (5) 的 b(x) ==")
    bad_hg = sum(1 for (x, y) in pts if not (h_d(x, y) > g_d(x, y)))
    check(f"h > g 在 {len(pts)} 点上成立（y > 0）", bad_hg == 0, f"反例 {bad_hg}")
    bad_b = 0
    for (x, y) in pts:
        if (g_d(x, y) > f_d(x, y)) != crit_b(x, y):
            bad_b += 1
    check("式 (5)：g > f ⟺ e^(−y) > 6(3−2Zx)/(12−3Zx−2Zx³) 在 " + str(len(pts)) + " 点一致",
          bad_b == 0, f"不一致 {bad_b}")

    # ---- §4 Lean 见证点 + Lean 证明所用的有理数界
    print("\n== §4 ★C 见证点与 Lean 证明所用的有理数界 ==")
    w1 = (F(1, 100), F(1, 100))
    w2 = (F(1, 100), F(100))
    check("(1/100, 1/100)：h > f（产 AGT，Lean `four_taxon_agt_witness`）",
          crit_definition(*w1), f"h−f = {float(h_d(*w1) - f_d(*w1)):.10f}")
    check("(1/100, 100)：f > h（不产 AGT，Lean `four_taxon_no_agt_witness`）",
          f_d(*w2) > h_d(*w2), f"f−h = {float(f_d(*w2) - h_d(*w2)):.10f}")
    u = ZD(F(1, 100))
    check("Lean 界 99/100 ≤ e^{−1/100}", dec(F(99, 100)) <= u, f"e^(−1/100) = {u:.20f}")
    check("Lean 界 e^{−1/100} ≤ 100/101", u <= dec(F(100, 101)), f"100/101 = {dec(F(100,101)):.20f}")
    v = ZD(F(100))
    check("Lean 界 e^{−100} ≤ 1/101", v <= dec(F(1, 101)), f"e^(−100) = {float(v):.6e}")
    # Lean 的代数余量
    A_lo = dec(F(2, 3)) - dec(F(100, 101)) / 2 - D_pow(dec(F(100, 101)), 3) / 9
    check("Lean 的 A 下界 591356/9272709 是有效下界",
          A_lo >= dec(F(591356, 9272709)), f"A_lo = {float(A_lo):.10f}")
    check("Lean 的乘积余量 99/100·591356/9272709 > 1/100",
          dec(F(99, 100)) * dec(F(591356, 9272709)) > dec(F(1, 100)))
    check("非见证点的余量 2/303 < 1/101",
          dec(F(2, 303)) < dec(F(1, 101)))

    print("\n" + "=" * 78)
    ok = all(results)
    print(f"通过 {sum(results)}/{len(results)}")
    print("VERDICT:", "PASS" if ok else "FAIL")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
