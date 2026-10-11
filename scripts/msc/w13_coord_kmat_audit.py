#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w13_coord_kmat_audit.py —— 协调侧对 §零·J「Kmat ≥ 0 的三分情形判定」的**独立数值审计**.

复刻 Phylo/Stat/CASTERF84.lean 的 Bmat / sm / rm / Kmat（逐元素字面定义）,
然后:
  §1 正例: λ,κ,t ≥ 0, π>0, Σπ=1  ⇒ 0 ≤ Kmat ≤ 1  (网格 + 随机)
  §2 三分情形的公式对拍 (跨类 / 对角 / 同类非对角)
  §3 反例(必要性): (A) λ·t < 0 ⇒ 跨类为负; (C) κ < -1 ⇒ 同类非对角为负
  §4 退化: t=0 ⇒ I;  κ=0 ⇒ F81 形;  π≡1/4 ⇒ JC69 形
"""
import math, random, itertools, sys

R, Y = (0, 1), (2, 3)

def piR(pi): return pi[0] + pi[1]
def piY(pi): return pi[2] + pi[3]

def Bmat(pi, i, j):
    if i in R and j in R: return pi[j] / piR(pi)
    if i in Y and j in Y: return pi[j] / piY(pi)
    return 0.0

def sm(lam, t):            return math.exp(-(lam * t))
def rm(lam, kap, t):       return math.exp(-(lam * (1.0 + kap) * t))

def Kmat(pi, kap, lam, t, i, j):
    d = 1.0 if i == j else 0.0
    return pi[j] + sm(lam, t) * (Bmat(pi, i, j) - pi[j]) + rm(lam, kap, t) * (d - Bmat(pi, i, j))

def rand_pi(rng):
    v = [rng.uniform(1e-3, 1.0) for _ in range(4)]
    s = sum(v)
    return [x / s for x in v]

def cls_ok(name, cond, extra=""):
    print(f"  [{'OK ' if cond else 'FAIL'}] {name}   {extra}")
    return cond

def main():
    ok = True
    rng = random.Random(20261012)

    print("=" * 78); print("§1 正例: λ,κ,t ≥ 0, π>0, Σπ=1  ⇒  0 ≤ Kmat ≤ 1"); print("=" * 78)
    lo, hi = float('inf'), float('-inf')
    n = 0
    for _ in range(4000):
        pi = rand_pi(rng)
        kap = rng.choice([0.0, rng.uniform(0, 5), rng.uniform(0, 100)])
        lam = rng.uniform(0, 10)
        t   = rng.uniform(0, 10)
        for i, j in itertools.product(range(4), repeat=2):
            k = Kmat(pi, kap, lam, t, i, j); n += 1
            lo, hi = min(lo, k), max(hi, k)
    ok &= cls_ok(f"随机构造 {n} 个元素均在 [0,1]", lo >= -1e-12 and hi <= 1 + 1e-12,
                 f"min={lo:.6e}  max={hi:.6e}")
    # 边界网格: π 极不均匀 (考验 pi_j/piR 接近 1)
    pi = [0.499, 0.499, 0.001, 0.001]
    lo2, hi2 = float('inf'), float('-inf')
    for lam in [0.0, 1e-3, 1.0, 1e3]:
        for kap in [0.0, 1.0, 1e4]:
            for t in [0.0, 1e-6, 1.0, 1e3]:
                for i, j in itertools.product(range(4), repeat=2):
                    k = Kmat(pi, kap, lam, t, i, j); lo2, hi2 = min(lo2, k), max(hi2, k)
    ok &= cls_ok("极端 π=(.499,.499,.001,.001) 的网格", lo2 >= -1e-12 and hi2 <= 1 + 1e-12,
                 f"min={lo2:.6e}  max={hi2:.6e}")

    print(); print("=" * 78); print("§2 三分情形公式对拍 (§零·J)"); print("=" * 78)
    bad = []
    for _ in range(2000):
        pi = rand_pi(rng); kap = rng.uniform(0, 3); lam = rng.uniform(0, 5); t = rng.uniform(0, 5)
        # A 跨类 (i,j) 异类
        for i, j in [(0, 2), (0, 3), (1, 2), (3, 0)]:
            if abs(Kmat(pi, kap, lam, t, i, j) - pi[j] * (1 - sm(lam, t))) > 1e-12: bad.append("A")
        # B 对角
        for i in range(4):
            want = pi[i]*(1-sm(lam,t)) + sm(lam,t)*(pi[i]/(piR(pi) if i in R else piY(pi))) \
                 + rm(lam,kap,t)*(1 - pi[i]/(piR(pi) if i in R else piY(pi)))
            if abs(Kmat(pi, kap, lam, t, i, i) - want) > 1e-12: bad.append("B")
        # C 同类非对角
        for i, j in [(0, 1), (1, 0), (2, 3), (3, 2)]:
            pR = piR(pi) if i in R else piY(pi)
            want = pi[j]*(1-sm(lam,t)) + (sm(lam,t)-rm(lam,kap,t))*(pi[j]/pR)
            if abs(Kmat(pi, kap, lam, t, i, j) - want) > 1e-12: bad.append("C")
    ok &= cls_ok("情形 A/B/C 的化简式逐点吻合", not bad, f"失配={len(bad)}")

    print(); print("=" * 78); print("§3 反例: 假设的必要性 (§零·J)"); print("=" * 78)
    pi4 = [0.25]*4
    kA = Kmat(pi4, 0.0, 1.0, -1.0, 0, 2)          # 跨类, t<0
    ok &= cls_ok("(A) λ·t<0 ⇒ 跨类元素为负", kA < 0, f"K(0,2)={kA:.6f} = 1/4·(1-e)={0.25*(1-math.e):.6f}")
    kC = Kmat(pi4, -2.0, 1.0, 1.0, 0, 1)          # 同类非对角, κ<-1
    ok &= cls_ok("(C) κ<-1 ⇒ 同类非对角为负", kC < 0, f"K(0,1)={kC:.6f}")
    smv, rmv = sm(1.0, 1.0), rm(1.0, -2.0, 1.0)
    ok &= cls_ok("    且此时 sm < rm (情形 C 的病根)", smv < rmv, f"sm={smv:.6f} rm={rmv:.6f}")
    kC2 = Kmat(pi4, -0.5, 1.0, 1.0, 0, 1)         # -1<κ<0 仍应非负 (1+κ>0)
    ok &= cls_ok("    -1<κ<0 时仍非负 (1+κ>0)", kC2 > 0, f"K(0,1)={kC2:.6f}")

    print(); print("=" * 78); print("§4 退化一致性"); print("=" * 78)
    bad = []
    for pi in [pi4, [0.4, 0.3, 0.2, 0.1]]:
        for i, j in itertools.product(range(4), repeat=2):
            want = 1.0 if i == j else 0.0
            if abs(Kmat(pi, 0.7, 2.0, 0.0, i, j) - want) > 1e-15: bad.append("t=0")
    ok &= cls_ok("t=0  ⇒ K = I", not bad, f"失配={len(bad)}")
    # kap=0 ⇒ K_ij = pi_j(1-sm) + sm*δ_ij  (F81 形)
    bad = []
    for _ in range(500):
        pi = rand_pi(rng); lam = rng.uniform(0, 5); t = rng.uniform(0, 5)
        for i, j in itertools.product(range(4), repeat=2):
            want = pi[j]*(1-sm(lam,t)) + (sm(lam,t) if i == j else 0.0)
            if abs(Kmat(pi, 0.0, lam, t, i, j) - want) > 1e-12: bad.append("F81")
    ok &= cls_ok("κ=0 ⇒ F81 形  π_j(1-sm) + sm·δ_ij", not bad, f"失配={len(bad)}")
    # pi = 1/4, kap=0 ⇒ JC69: 对角 1/4+3/4·sm, 非对角 1/4(1-sm)
    bad = []
    for lam in [0.5, 1.0, 3.0]:
        for t in [0.1, 1.0, 4.0]:
            s = sm(lam, t)
            if abs(Kmat(pi4, 0.0, lam, t, 0, 0) - (0.25 + 0.75*s)) > 1e-12: bad.append("JC-diag")
            if abs(Kmat(pi4, 0.0, lam, t, 0, 1) - 0.25*(1-s)) > 1e-12: bad.append("JC-off")
    ok &= cls_ok("π≡1/4, κ=0 ⇒ JC69 (1/4+3/4·sm 对角, 1/4(1-sm) 非对角)", not bad, f"失配={len(bad)}")

    print(); print("=" * 78)
    print("AUDIT PASSED: all checks ok" if ok else "AUDIT FAILED")
    print("=" * 78)
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
