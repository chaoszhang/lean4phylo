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
    print("⑤ **单调性**（`Identifiability.mscConcordant_strictMono` / `mscDiscordant_antitone`）：")
    print("   ADR 公式的定量形式 —— 枝长越长 ⇒ 一致概率越高、不一致概率越低")
    prev_p, prev_d = None, None
    strictly_up = True
    strictly_dn = True
    for t in grid:
        v, dv = +p(t), +(D(1) / D(3) * (-t).exp())
        if prev_p is not None and not (prev_p < v):
            strictly_up = False
        if prev_d is not None and not (dv < prev_d):
            strictly_dn = False
        prev_p, prev_d = v, dv
    print(f"   网格 {len(grid)} 个点上 p 严格递增：{'✓' if strictly_up else '✗'}"
          f"；⅓e^{{−t}} 严格递减：{'✓' if strictly_dn else '✗'}")
    assert strictly_up and strictly_dn
    # 定量形式：a < b ⇒ p(a) < p(b)（此处即上面的严格递增），并抽查三对
    for (a, b) in [(D(0), D(1)), (D(1) / D(2), D(3) / D(2)), (D(1), D(10))]:
        assert p(a) < p(b), (a, b)
        print(f"   p({a}) = {p(a):.30f} < p({b}) = {p(b):.30f} ✓")
    # 复数域外的一致性：p(t) + 2·⅓e^{−t} = 1（三拓扑归一化）
    for t in [D(1) / D(10), D(1), D(5)]:
        tot = p(t) + 2 * (D(1) / D(3) * (-t).exp())
        assert abs(tot - D(1)) < D(10) ** (-45)
    print("   p(t) + 2·(⅓e^{−t}) ≡ 1（三拓扑归一化）✓")

    print("=" * 78)
    print("VERDICT: PASS")

if __name__ == "__main__":
    main()
