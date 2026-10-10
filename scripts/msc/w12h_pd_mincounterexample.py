#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12h · 自足反例：4 叶树 + 一组权 ⇒ 「极大集套极大集」**不可用**；
但**同组数据**上「注册的修复形态（∃ prev next）」**成立** —— 脚本同时打印正反两面。

    tree = ((('L',0),('L',1)),(('L',2),('L',3)))   4 叶树
    w    = [4, 3, 2, 1, 6, 7]（边按 `pd_cov` 的 DFS 序）

同时检验两种量词形态（W12h ★D-2 自我纠错的核心）：
  (A) `step_maximizer` 形态  ∀ prev(极大 k), ∃ next(极大 k+1), prev ⊆ next  → 有反例（假）
  (B) 注册的修复形态          ∃ prev(极大 k), ∃ next(极大 k+1), prev ⊆ next  → 有见证（成立）
"""
import itertools
import sys

sys.path.insert(0, '.')
from w12h_greedy_gap_check import pd_cov

TREE = ((("L", 0), ("L", 1)), (("L", 2), ("L", 3)))
W = [4.0, 3.0, 2.0, 1.0, 6.0, 7.0]
N = 4


def main():
    cov = pd_cov(TREE, N)
    nedge = max(e for c in cov.values() for e in c) + 1
    w = W[:nedge]

    def PD(S):
        return sum(w[e] for e in cov[frozenset(S)])

    print('tree =', TREE)
    print('w    =', w)
    for s in sorted(cov, key=lambda x: (len(x), sorted(x))):
        print('   cov', sorted(s), '=', sorted(cov[s]), ' PD =', PD(s))

    maxsets = {}
    for k in range(N + 1):
        subs = [frozenset(s) for s in itertools.combinations(range(N), k)]
        mx = max(PD(s) for s in subs)
        maxsets[k] = [sorted(s) for s in subs if abs(PD(s) - mx) < 1e-12]
        print('k=%d: pd_%d = %s   极大集 = %s' % (k, k, mx, maxsets[k]))

    print()
    print('(A) step_maximizer 形态  forall prev(max k), exists next(max k+1), prev <= next')
    bad = []
    for k in range(1, N):
        for A in maxsets[k]:
            if not any(set(A) <= set(B) for B in maxsets[k + 1]):
                bad.append((k, A))
    print('    反例 =', bad if bad else '无', '=>', '假' if bad else '成立')

    print()
    print('(B) 注册的修复形态  exists prev(max k), exists next(max k+1), prev <= next')
    wit = []
    for k in range(1, N):
        ok = None
        for A in maxsets[k]:
            for B in maxsets[k + 1]:
                if set(A) <= set(B):
                    ok = (k, A, B)
                    break
            if ok:
                break
        wit.append(ok)
    for item in wit:
        if item:
            print('    k=%d: 见证 = (%s, %s)' % item)
        else:
            print('    k=%d: 无见证' % 0)
    print('    =>', '成立' if all(wit) else '不成立')

    print()
    print('结论：同一组 (树, 权) 上 (A) 假 而 (B) 成立 —— 两者差一个量词，')
    print('      故 not_step_maximizer 不否证 greedy_gap_correct_shape。')
    return 0


if __name__ == '__main__':
    sys.exit(main())
