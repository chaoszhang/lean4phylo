#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11f / G1 -- "multi-marker average => true frequency": exhaustive exact-rational
replication of the algebra, plus the counterexample check.

Lean counterpart:
  Phylo/Stat/MultiLocusLaw.lean
    Phylo.Stat.MultiLocusLaw.multiLocusData_avg_p        (avg = finite mean)
    Phylo.Stat.MultiLocusLaw.multiLocusData_avg_eq_empFreq
    Phylo.Stat.MultiLocusLaw.avg_p_sub_le                (triangle inequality)
    Phylo.Stat.MultiLocusLaw.avg_FreqClose               (all loci eps-close => avg eps-close)
    Phylo.Stat.MultiLocusLaw.avg_eq_of_forall_eq         (equal loci => avg = that table)
    Phylo.Stat.MultiLocusLaw.const_avg                   (M.avg = m.freq IS a theorem)
    Phylo.Stat.MultiLocusLaw.multiLocus_maximizer_agrees_close
                                                         (eps-close REPLACES M.avg = m.freq)
    Phylo.Stat.MultiLocusLaw.empFreq_const_locus         (counterexample core)

Everything below is exact rational arithmetic (`fractions.Fraction`).
No Monte Carlo, no floating point in the checks.

Model (X = Fin 4, the smallest instance):
  * X has exactly ONE 4-element subset (the whole of Fin 4);
  * there are exactly 3 undirected quartet topologies: ab|cd (true), ac|bd, ad|bc;
  * the MSC truth table with internal branch length t is, with q := e^{-t},
        ab|cd = 1 - (2/3) q,   ac|bd = ad|bc = (1/3) q,        (M1)
    required to sum to 1: 1 - (2/3)q + (2/3)q = 1  (checked exactly).
  * `q` is carried as an exact rational (the identities used are polynomial in q,
    so no transcendental value is ever needed).
  * the ASTRAL score of a choice on Fin 4 is just that choice's probability, so
    the multi-marker argmax question is exactly "which column is largest".

Exits non-zero if any check fails.
"""

from fractions import Fraction as F
import sys

FAIL = []


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


TOPO = ("ab|cd", "ac|bd", "ad|bc")


def truth(q):
    """MSC truth table on Fin 4, q = e^{-t} as an exact rational."""
    return {"ab|cd": 1 - F(2, 3) * q, "ac|bd": F(1, 3) * q, "ad|bc": F(1, 3) * q}


def score(table, choice):
    """ASTRAL score = sum over the single 4-set of table[choice]."""
    return table[choice]


def avg(tables):
    """Pointwise finite mean, mirroring `MultiMarkerFreq.avg`."""
    L = len(tables)
    assert L > 0
    return {c: sum((t[c] for t in tables), F(0)) / L for c in TOPO}


def is_table(t):
    return all(v >= 0 for v in t.values()) and sum(t.values(), F(0)) == 1


# --------------------------------------------------------------------------
print("== 1. MSC truth table is a genuine probability table (exact) ==")
for q in [F(0), F(1, 4), F(1, 3), F(1, 2), F(2, 3), F(9, 10), F(1)]:
    t = truth(q)
    check("truth(q=%s) is a table (nonneg, sums to 1)" % q, is_table(t))
    if q < 1:
        check("truth(q=%s): true topology strictly maximal" % q,
              all(t["ab|cd"] > t[c] for c in TOPO if c != "ab|cd"))

# --------------------------------------------------------------------------
print("== 2. avg = finite mean; multiLocusScore = L * astralScore(avg) ==")
# three explicit rational locus tables, each a genuine table
D1 = {"ab|cd": F(3, 4), "ac|bd": F(1, 8), "ad|bc": F(1, 8)}
D2 = {"ab|cd": F(1, 2), "ac|bd": F(1, 4), "ad|bc": F(1, 4)}
D3 = {"ab|cd": F(7, 8), "ac|bd": F(1, 16), "ad|bc": F(1, 16)}
loci = [D1, D2, D3]
check("D1,D2,D3 are tables", all(is_table(D) for D in loci))
A = avg(loci)
check("avg(D1,D2,D3) on ab|cd = (7/8 + 1/2 + 3/4)/3 = 17/24 exactly",
      A["ab|cd"] == (F(7, 8) + F(1, 2) + F(3, 4)) / 3 and A["ab|cd"] == F(17, 24))
check("avg is a table", is_table(A))
for c in TOPO:
    lhs = sum((score(D, c) for D in loci), F(0))
    rhs = len(loci) * score(A, c)
    check("multiLocusScore(%s) = L * astralScore(avg, %s)" % (c, c), lhs == rhs)

# --------------------------------------------------------------------------
print("== 3. avg_p_sub_le (triangle inequality) and avg_FreqClose ==")
q = F(1, 2)
T = truth(q)
for eps in [F(1, 100), F(1, 10), F(1, 3)]:
    # build loci that are all within eps of the truth (keeping them tables)
    def jitter(base, delta):
        d = dict(base)
        d["ab|cd"] = base["ab|cd"] - delta
        d["ac|bd"] = base["ac|bd"] + delta / 2
        d["ad|bc"] = base["ad|bc"] + delta / 2
        return d
    L = [jitter(T, eps / 2), jitter(T, -eps / 3), T]
    raw = [abs(D[c] - T[c]) for D in L for c in TOPO]
    avgA = avg(L)
    lhs = [abs(avgA[c] - T[c]) for c in TOPO]
    bound = [sum((abs(D[c] - T[c]) for D in L), F(0)) / len(L) for c in TOPO]
    check("eps=%s: every locus within eps of truth" % eps, max(raw) < eps)
    check("eps=%s: |avg - truth| <= mean|D - truth| (per column)" % eps,
          all(l <= b for l, b in zip(lhs, bound)))
    check("eps=%s: avg within eps of truth (avg_FreqClose)" % eps, max(lhs) < eps)

# --------------------------------------------------------------------------
print("== 4. exact-equality case: equal loci => avg = that table (const_avg) ==")
for D in [truth(F(1, 5)), D1, D2]:
    A = avg([D, D, D, D])
    check("all loci = D => avg = D (exact)", A == D)
    check("FreqClose(avg, D, eps) for every eps > 0 holds (delta = 0 < eps)",
          all(abs(A[c] - D[c]) == 0 for c in TOPO))

# --------------------------------------------------------------------------
print("== 5. COUNTEREXAMPLE (discipline B): no `hmean` => limit is NOT the truth ==")
# locus is CONSTANT = D; then the average is D for every L, so its a.e. limit is D.
# Take q_truth = 1/2 and q_D = 1/4: then D != truth, hence hmean must FAIL.
Dtruth = truth(F(1, 2))
Dother = truth(F(1, 4))
check("truth(1/2) != truth(1/4)", Dtruth != Dother)
for L in [1, 2, 3, 5, 17, 1000]:
    A = avg([Dother] * L)
    check("L=%d: constant locus D => avg = D (exact equality, L>=1)" % L, A == Dother)
check("limit (= Dother) differs from truth at ab|cd",
      Dother["ab|cd"] != Dtruth["ab|cd"])
check("so `int locus.p = truth.p` (hmean) is FALSE for this model",
      Dother["ab|cd"] != Dtruth["ab|cd"] or Dother["ac|bd"] != Dtruth["ac|bd"])
# and hmean failing is exactly what the SLLN conclusion needs: without it the
# limit is Dother, and Dother's argmax is still ab|cd here -- so use a D whose
# argmax is the WRONG topology to make the failure visible:
Dwrong = {"ab|cd": F(1, 4), "ac|bd": F(1, 2), "ad|bc": F(1, 4)}
check("Dwrong is a table with wrong argmax", is_table(Dwrong) and
      max(TOPO, key=lambda c: Dwrong[c]) == "ac|bd")
for L in [1, 2, 3, 5, 1000]:
    A = avg([Dwrong] * L)
    check("L=%d: constant locus Dwrong => avg = Dwrong, argmax = ac|bd (WRONG)" % L,
          A == Dwrong and max(TOPO, key=lambda c: A[c]) == "ac|bd")

# --------------------------------------------------------------------------
print("== 6. gap delta and the stability threshold eps < delta/(2N+1), N = 1 ==")
N = 1  # Fin 4 has exactly one 4-element subset
for q in [F(1, 4), F(1, 2), F(2, 3), F(9, 10)]:
    T = truth(q)
    delta = min(T["ab|cd"] - T[c] for c in TOPO if c != "ab|cd")
    check("q=%s: gap delta = 1 - q > 0" % q, delta == 1 - q and delta > 0)
    eps = delta / (2 * N + 1)
    check("q=%s: eps = delta/3; a table within eps of truth has the true argmax" % q,
          all((T["ab|cd"] - eps) > (T[c] + eps) for c in TOPO if c != "ab|cd"))

# --------------------------------------------------------------------------
print("== 7. EXHAUSTIVE: over a finite rational grid, `all loci eps-close` => `avg eps-close` ==")
grid = [F(0), F(1, 8), F(1, 4), F(1, 3), F(1, 2), F(2, 3), F(3, 4), F(7, 8), F(1)]
count = 0
bad = 0
for q in [F(1, 3), F(1, 2), F(2, 3)]:
    T = truth(q)
    for q1 in grid:
        for q2 in grid:
            for eps in [F(1, 10), F(1, 4), F(1, 2)]:
                L = [truth(q1), truth(q2), T]
                if max(abs(D[c] - T[c]) for D in L for c in TOPO) < eps:
                    A = avg(L)
                    count += 1
                    if not max(abs(A[c] - T[c]) for c in TOPO) < eps:
                        bad += 1
check("exhaustive grid (%d admissible triples): no violation of the averaging step"
      % count, bad == 0 and count > 0)

# --------------------------------------------------------------------------
print("== 8. Fin 4 minimal instance: 3 loci, end to end ==")
q = F(1, 2)
T = truth(q)
D1 = {"ab|cd": F(2, 3), "ac|bd": F(1, 6), "ad|bc": F(1, 6)}
D2 = {"ab|cd": F(7, 10), "ac|bd": F(3, 20), "ad|bc": F(3, 20)}
D3 = {"ab|cd": F(4, 5), "ac|bd": F(1, 10), "ad|bc": F(1, 10)}
L3 = [D1, D2, D3]
A = avg(L3)
check("D1,D2,D3 tables", all(is_table(D) for D in L3))
check("avg(3 loci) = ((2/3+7/10+4/5)/3, ...) exactly",
      A["ab|cd"] == (F(2, 3) + F(7, 10) + F(4, 5)) / 3 and is_table(A))
check("avg's argmax is the TRUE topology ab|cd",
      max(TOPO, key=lambda c: A[c]) == "ab|cd")
delta = T["ab|cd"] - T["ac|bd"]
check("FreqClose(avg, truth, delta/3) holds (so the corrected theorem applies)",
      all(abs(A[c] - T[c]) < delta / 3 for c in TOPO))

print()
if FAIL:
    print("FAIL: %d check(s) failed" % len(FAIL))
    for n in FAIL:
        print("   - " + n)
    sys.exit(1)
print("PASS -- W11f/G1 exact-rational replication: all checks passed")
