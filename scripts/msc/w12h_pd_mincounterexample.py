#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12h · 自足反例：4 叶树 + 一组权 ⇒ 「极大集套极大集」**不可用**；
但**同组数据**上「注册的修复形态（∃ prev next）」**成立** —— 脚本同时打印正反两面。

    tree = ((('L',0),('L',1)),(('L',2),('L',3)))   4 叶树
    w    = [4, 3, 2, 1, 6, 7]（边按 `pd_cov` 的 DFS 序）

同时检验两种量词形态（W12h ★D-2 自我纠错的核心）：
  (A) `step_maximizer` 形态  ∀ prev(极大 k), ∃ next(极大 k+1), prev ⊆ next  → 有反例（假）
  (B) 注册的修复形态          ∃ prev(极大 k), ∃ next(极大 k+1), prev ⊆ next  → 有见证（成立）

退出码：0 ＝ (A) 有反例（该形态为假）且 (B) 全部 k 有见证（该形态成立）—— 两项均复现
        （末尾打印判定词）；1 ＝ 任一判定失败（打印 VERDICT: FAIL 并逐条列出）。
"""
import itertools
import sys

sys.path.insert(0, '.')
from w12h_greedy_gap_check import pd_cov

TREE = ((("L", 0), ("L", 1)), (("L", 2), ("L", 3)))
W = [4.0, 3.0, 2.0, 1.0, 6.0, 7.0]
N = 4


def main():
    fails = []
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
    # (A) 的反例**只**来自「k=2 的唯一极大集是 [0,3]」⇒ 这一条是本脚本全部结论的支点，
    #     故把它也钉成判据（若极大集变了，(A) 的"假"就不再由这里复现）。
    if maxsets[2] != [[0, 3]]:
        fails.append(f"(A) 的支点：k=2 极大集 = {maxsets[2]} ≠ [[0, 3]]")

    print()
    print('(A) step_maximizer 形态  forall prev(max k), exists next(max k+1), prev <= next')
    bad = []
    for k in range(1, N):
        for A in maxsets[k]:
            if not any(set(A) <= set(B) for B in maxsets[k + 1]):
                bad.append((k, A))
    print('    反例 =', bad if bad else '无', '=>', '假' if bad else '成立')
    if not bad:
        fails.append("(A) ∀ prev ∃ next 形态**无反例** ⇒ 未复现『该形态为假』")
    elif len(bad) != 2:
        fails.append(f"(A) 反例数 = {len(bad)} ≠ 2（本脚本实测：k=1 的 [1]、[2] 各一个）")

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
    if not all(wit):
        fails.append("(B) 注册的修复形态 ∃ prev ∃ next 出现『无见证』⇒ 未复现『该形态成立』")

    print()
    print('结论：同一组 (树, 权) 上 (A) 假 而 (B) 成立 —— 两者差一个量词，')
    print('      故 not_step_maximizer 不否证 greedy_gap_correct_shape。')
    if fails:
        print()
        print('VERDICT: FAIL')
        for m in fails:
            print('   x ' + m)
        return 1
    print()
    print('VERDICT: PASS（(A) ∀ 形态有 %d 个反例 / (B) ∃∃ 形态 k=1..3 全有见证 / '
          'k=2 唯一极大集 = [[0, 3]]）' % len(bad))
    return 0


if __name__ == '__main__':
    sys.exit(main())
