#!/usr/bin/env python3
"""
scripts/msc/adr2011_identifiability.py —— `Phylo/Stat/Identifiability.lean` 的独立复核

**高精度**（`decimal`，50 位有效数字；不用 Monte Carlo、不重跑 Lean）核对：

  ① ADR2011 第 300–306 行的公式 `t = −log((3/2)(1 − p))`，其中 `p = 1 − ⅔e^{−t}`；
  ② 无 `log` 形式 `(3/2)(1 − p) = e^{−t}`；
  ③ `p` 的**单射性**（在网格上：`p(t₁) = p(t₂) ⇒ t₁ = t₂`）；
  ④ `p(0) = 1/3`；`t > 0 ⇒ p(t) > 1/3`（星形树是唯一的「无优势」点）。
"""
from decimal import Decimal as D, getcontext

getcontext().prec = 50

def p(t: D) -> D:
    """mscConcordant t = 1 − ⅔·e^{−t}。"""
    return D(1) - (D(2) / D(3)) * (-t).exp()

def main():
    print("=" * 78)
    print("① ADR2011 第 300–306 行：t = −log((3/2)(1 − p))  ⇒ 复算回 t")
    worst = D(0)
    for k in [D(1) / 10, D(1) / 4, D(1) / 2, D(1), D(2), D(5), D(10)]:
        lhs = -((D(3) / D(2)) * (D(1) - p(k))).ln()
        err = abs(lhs - k)
        worst = max(worst, err)
        print(f"   t={k}  复算={lhs:.30f}  误差={err}")
    print(f"   最大误差 = {worst}  （判据 < 1e-40）")
    assert worst < D(10) ** (-40), worst
    print("   ✓ 50 位精度下**恒等**")

    print("=" * 78)
    print("② 无 log 形式：(3/2)(1 − p) = e^{−t}")
    worst = D(0)
    for k in [D(1) / 10, D(1), D(3), D(7)]:
        a = (D(3) / D(2)) * (D(1) - p(k))
        b = (-k).exp()
        worst = max(worst, abs(a - b))
    print(f"   最大误差 = {worst}")
    assert worst < D(10) ** (-48), worst
    print("   ✓")

    print("=" * 78)
    print("③ 单射性：网格上 p(t₁) = p(t₂) ⇒ t₁ = t₂")
    grid = [D(i) / D(10) for i in range(0, 51)]
    vals = {}
    ok = True
    for t in grid:
        v = +p(t)          # 取 50 位精度下的规范值
        if v in vals and vals[v] != t:
            ok = False
            print(f"   ✗ 碰撞：{vals[v]} 与 {t} 同为 {v}")
        vals[v] = t
    print(f"   网格 {len(grid)} 个点、{len(vals)} 个不同概率值  —— {'✓ 无碰撞' if ok else '✗'}")
    assert ok

    print("=" * 78)
    print("④ p(0) = 1/3；t > 0 ⇒ p(t) > 1/3")
    assert abs(p(D(0)) - D(1) / D(3)) < D(10) ** (-48)
    print(f"   p(0) = {p(D(0)):.30f}  = 1/3 ✓")
    for t in [D(1) / D(100), D(1), D(10)]:
        assert p(t) > D(1) / D(3)
        print(f"   p({t}) = {p(t):.30f} > 1/3 ✓")

    print("=" * 78)
    print("VERDICT: PASS")

if __name__ == "__main__":
    main()
