"""Verify the two 'Agg_c' collapse claims that the F84 derivation rests on (t39's formulas),
so the derivation agent has an independent reference.

Setup (F84):  K(t) = Pi + e^{-lam t}(B - Pi) + e^{-lam(1+kap)t}(I - B)
  h_c(i,j) := p_c^2 * [i=j] - q_c ,  p_c = sum_{i in c} pi_i ,  q_c = sum_{i in c} pi_i^2
  Agg_c(u; t1, t2) := sum_{i in c} sum_{j in c} h_c(i,j) * K(t1)[u,i] * K(t2)[u,j]
Claims to check:
  (1) Agg_c(u) = 0                for u not in c
  (2) sum_{u in c} pi_u * Agg_c(u) = p_c * X_c * e^{-lam(1+kap)(t1+t2)} ,  X_c = p_c^2 - q_c
"""
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = {A, G}, {C, T}


def build(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, lam


def K(B, pi, kappa, lam, t):
    return (np.tile(pi, (4, 1)) + np.exp(-lam * t) * (B - np.tile(pi, (4, 1)))
            + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B))


rng = np.random.default_rng(2024)
w1 = w2 = 0.0
for _ in range(300):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam = build(pi, kappa)
    t1, t2 = float(rng.random() * 2), float(rng.random() * 2)
    K1, K2 = K(B, pi, kappa, lam, t1), K(B, pi, kappa, lam, t2)
    for c in (R, Y):
        pc = sum(pi[i] for i in c)
        qc = sum(pi[i] ** 2 for i in c)
        Xc = pc ** 2 - qc
        h = np.zeros((4, 4))
        for i in range(4):
            for j in range(4):
                if i in c and j in c:
                    h[i, j] = pc ** 2 * (1.0 if i == j else 0.0) - qc
        # (1) u not in c
        for u in range(4):
            if u in c:
                continue
            agg = sum(h[i, j] * K1[u, i] * K2[u, j] for i in c for j in c)
            w1 = max(w1, abs(agg))
        # (2) weighted sum over u in c
        lhs = sum(pi[u] * sum(h[i, j] * K1[u, i] * K2[u, j] for i in c for j in c) for u in c)
        rhs = pc * Xc * np.exp(-lam * (1 + kappa) * (t1 + t2))
        w2 = max(w2, abs(lhs - rhs) / max(1e-12, abs(rhs)))

print("(1) Agg_c(u) = 0 for u not in c        : worst |value|      =", w1)
print("(2) sum_{u in c} pi_u Agg_c(u) = p_c X_c e^{-lam(1+kap)(t1+t2)}: worst rel.err =", w2)
print()
print("pi =", pi.round(4), " kappa =", round(kappa, 4))
for c, nm in ((R, "R"), (Y, "Y")):
    pc = sum(pi[i] for i in c)
    qc = sum(pi[i] ** 2 for i in c)
    print(f"  class {nm}: p_c = {pc:.6f}  q_c = {qc:.6f}  X_c = p_c^2 - q_c = {pc**2-qc:.6f}")
