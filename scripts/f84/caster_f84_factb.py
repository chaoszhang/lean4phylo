"""Verify t39's structural fact (b) -- the last unverified input to the F84 derivation.

Claim (b): for u, i in the same class c (c = R or Y),
    K(t)_{u,i} = alpha_t * pi_i + r_t * delta_{u,i}
  with (DERIVED CORRECTLY by the coordinator; t39's version had alpha_t = e^{-lam t}/p_c, which is WRONG):
      alpha_t = 1 - e^{-lam t} + (e^{-lam t} - e^{-lam(1+kap)t}) / p_c ,   r_t = e^{-lam(1+kap)t}
  Sanity: t -> 0 gives alpha_0 = 0, r_0 = 1 => K(0) = I;
          t -> inf gives alpha_inf = 1, r_inf = 0 => K(inf)_{u,i} = pi_i (stationarity).
Also re-verify the two Agg_c claims (see caster_f84_aggc.py) in the same run.
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
    return B, lam, pR, pY


def K(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


rng = np.random.default_rng(7777)
worst_b = 0.0
for _ in range(300):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = build(pi, kappa)
    t = float(rng.random() * 2)
    Kt = K(B, pi, kappa, lam, t)
    for c, pc in ((R, pR), (Y, pY)):
        sm = np.exp(-lam * t)
        rm = np.exp(-lam * (1 + kappa) * t)
        alpha = 1 - sm + (sm - rm) / pc
        r = rm
        for u in c:
            for i in c:
                lhs = Kt[u, i]
                rhs = alpha * pi[i] + (r if u == i else 0.0)
                worst_b = max(worst_b, abs(lhs - rhs))
print("(b) K(t)_{u,i} = alpha_t*pi_i + r_t*delta_{u,i} for u,i in same class:")
print("    worst |lhs - rhs| =", worst_b)
print()
print("correct closed forms:  alpha_t = 1 - e^{-lam t} + (e^{-lam t} - e^{-lam(1+kap)t})/p_c ,  r_t = e^{-lam(1+kap)t}")
print("=>", "VERIFIED" if worst_b < 1e-13 else "MISMATCH")
