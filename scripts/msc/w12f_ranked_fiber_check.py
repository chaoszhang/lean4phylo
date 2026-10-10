"""W12f: 数值核对 rankedFiberCount_gap (SD2012 Remark 6) —— 穷举合并史。

公式（被核对的对象）：
  |{g ∈ mergeHistories n : cladesOf n g = cladesOf n f}| = (n-1)! / ∏_{C ∈ cladesOf n f, |C| ≥ 2} (|C| - 1)

同时核对 docstring 里两条被否证的「显然」结论：
  (i)  纤维数一般不是 (n-1)!；
  (ii) 纤维大小依赖树形。
"""
import sys
from itertools import product
from math import factorial


def step_map(r, x, y):
    return tuple(x if r[w] == y else r[w] for w in range(len(r)))


def chain_maps(n, f):
    r = tuple(range(n))
    out = [r]
    for k in range(len(f)):
        r = step_map(r, f[k][0], f[k][1])
        out.append(r)
    return out


def is_step(r, x, y):
    return r[x] == x and r[y] == y and x < y


def is_merge_history(n, f):
    cs = chain_maps(n, f)
    for k in range(n - 1):
        if not is_step(cs[k], f[k][0], f[k][1]):
            return False
    last = cs[n - 1]
    return all(last[w] == last[0] for w in range(n))


def blocks_of(n, r):
    return frozenset(frozenset(z for z in range(n) if r[z] == r[w]) for w in range(n))


def clades_of(n, f):
    cs = chain_maps(n, f)
    out = set()
    for L in range(n):
        out |= set(blocks_of(n, cs[L]))
    return frozenset(out)


def check(n):
    dom = list(product(range(n), repeat=2))
    hists = [f for f in product(dom, repeat=n - 1) if is_merge_history(n, f)]
    fibers = {}
    for f in hists:
        fibers.setdefault(clades_of(n, f), []).append(f)
    Hn = factorial(n) * factorial(n - 1) // 2 ** (n - 1)
    print("n=%d  #mergeHistories=%d  H_n=%d  H_n_ok=%s  #clade_sets=%d"
          % (n, len(hists), Hn, Hn == len(hists), len(fibers)))
    bad = 0
    sizes = {}
    for cl, fs in fibers.items():
        num = factorial(n - 1)
        den = 1
        for C in cl:
            if len(C) >= 2:
                den *= (len(C) - 1)
        pred = num // den if num % den == 0 else None
        sizes[len(fs)] = sizes.get(len(fs), 0) + 1
        if pred is None or pred != len(fs):
            bad += 1
            if bad <= 3:
                print("      MISMATCH fiber=%d predicted=%s clades=%s"
                      % (len(fs), pred, sorted(sorted(c) for c in cl)))
    print("      fiber-size histogram=%s  mismatches=%d  (n-1)! = %d"
          % (sizes, bad, factorial(n - 1)))
    return bad == 0


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    ok = True
    for n in range(2, nmax + 1):
        ok = check(n) and ok
    print("ALL_OK" if ok else "HAS_MISMATCH")
    return 0


if __name__ == "__main__":
    sys.exit(main())
