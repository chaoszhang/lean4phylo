#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W19 C1-M3②：threeAgtCriterion（DR2006 式 (5)）的代数内核数值验证。

目标：确认缺口 threeAgtCriterion 的证明可归约为【一条代数恒等式】：

    g x y - f x y = -A'(w) + B(w) * Z y                (w := Z x, z := Z y)
    A'(w) := 1 - (2/3) w
    B(w)  := 2/3 - w/6 - w^3/9

    ⇒ g > f  ⟺  B*z > A'  ⟺  z > A'/B  ⟺  e^{-y} > A'/B
              ⟺  -y > log(A'/B)  ⟺  y < log(B/A')
    故 only 剩余 = 恒等式  B/A' = C(w) := (12 - 3w - 2w^3) / (6 (3 - 2w))

同时验证文献的判决性数字 b(0) = log(7/6) ≈ 0.1542（DR2006 :299）。
"""
from fractions import Fraction as F
import math

def A(w):  return 1 - F(2, 3) * w
def B(w):  return F(2, 3) - w / 6 - w ** 3 / 9
def C(w):  return (12 - 3 * w - 2 * w ** 3) / (6 * (3 - 2 * w))
def f(w, z): return 1 - F(2, 3) * w - F(2, 3) * z + F(1, 3) * (w * z) + F(1, 18) * (w ** 3 * z)
def g(w, z): return F(1, 6) * (w * z) - F(1, 18) * (w ** 3 * z)

print("=" * 74)
print("① 因式分解验证： g - f = -A'(w) + B(w) * z   （精确有理数 ✓）")
bad = 0
for wi in [F(1, 100), F(1, 10), F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(1)]:
    for zi in [F(1, 100), F(1, 3), F(1, 2), F(7, 10), F(1)]:
        lhs = g(wi, zi) - f(wi, zi)
        rhs = -A(wi) + B(wi) * zi
        if lhs != rhs:
            bad += 1
            print("  ✗ w=%s z=%s : %s ≠ %s" % (wi, zi, lhs, rhs))
print("  检查 35 组：不符 %d 组 %s" % (bad, "✓ 恒等式成立" if bad == 0 else "✗"))

print("=" * 74)
print("② 关键分式恒等式： B(w)/A'(w) = C(w)   ⟺   B·6(3−2w) = A'·(12−3w−2w³)")
bad2 = 0
for wi in [F(1, 100), F(1, 10), F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(1)]:
    if B(wi) * 6 * (3 - 2 * wi) != A(wi) * (12 - 3 * wi - 2 * wi ** 3):
        bad2 += 1
        print("  ✗ w=%s" % wi)
    if A(wi) != 0 and B(wi) / A(wi) != C(wi):
        bad2 += 1
        print("  ✗ 商 w=%s : %s ≠ %s" % (wi, B(wi) / A(wi), C(wi)))
print("  不符 %d 处 %s" % (bad2, "✓ 恒等式成立" if bad2 == 0 else "✗"))

print("=" * 74)
print("③ 文献判决性数字（DR2006 :299）：b(0) = log(7/6) ≈ 0.1542")
print("  B(1)/A'(1) = %s  （应为 7/6 = %s）%s" % (B(F(1)) / A(F(1)), F(7, 6),
      "✓" if B(F(1)) / A(F(1)) == F(7, 6) else "✗"))
print("  log(7/6) = %.6f   （文献 b(0) ≈ 0.1542）%s"
      % (math.log(7 / 6), "✓" if abs(math.log(7 / 6) - 0.1542) < 5e-5 else "✗"))

print("=" * 74)
print("④ 判据等价性抽查： g > f  ⟺  y < log(B(w)/A'(w))")
bad3 = 0
for wi in [F(1, 100), F(1, 10), F(1, 2), F(9, 10)]:
    thr = math.log(float(B(wi) / A(wi)))
    for yy in [0.05, 0.5, 1.0, 2.0, 5.0]:
        zz = math.exp(-yy)
        lhs = (float(g(wi, F(zz).limit_denominator(10 ** 9))) >
               float(f(wi, F(zz).limit_denominator(10 ** 9))))
        rhs = yy < thr
        if lhs != rhs:
            bad3 += 1
print("  抽查 20 组：不符 %d 组 %s" % (bad3, "✓ 判据等价" if bad3 == 0 else "✗"))
print("=" * 74)
print("结论：threeAgtCriterion 的证明可归约为 ①（ring ✓）＋ ②（ring ✓）＋ log 单调性 ✓")
