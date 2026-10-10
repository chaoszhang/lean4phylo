#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12g-4 生成器：把 `NeighborNet.lean` §9.4（`n = 5` 实例）与 §9.5（★B 具体 `d`/`w`）
机械产出并插入文件。所有 boilerplate（45 条 ne 引理、10 条弧见证、10 条权重公式、
10 项 sum 展开）都由本脚本按同一模式生成，避免手写出错。

用法（在正本目录）：
  python3 scripts/msc/w12g_fin5_instance_gen.py Phylo/Algorithm/NeighborNet.lean
"""

import sys

N = 5
REPS = [(i, j) for i in range(N) for j in range(i, N - 1)]        # 代表弧 [i,j]，j ≤ n−2
NAMES = {p: 'f%d%d' % p for p in REPS}
SUB = {0: '₀', 1: '₁', 2: '₂', 3: '₃', 4: '₄'}


def nm(p):
    return 'f' + SUB[p[0]] + SUB[p[1]]


def setlit(a, b):
    return '{' + ', '.join(str(t) for t in range(a, b + 1)) + '}'


def sideA_lemmas():
    out = []
    for (i, j) in REPS:
        out.append('@[simp] theorem %s_sideA : %s.sideA = ({%s} : Finset (Fin %d)) := by\n'
                   '  simp [%s]' % (nm((i, j)), nm((i, j)), ', '.join(str(t) for t in range(i, j + 1)), N, nm((i, j))))
    return '\n\n'.join(out)


def cyclic_lemmas():
    out = []
    for (i, j) in REPS:
        out.append('theorem isCyclicArc_%s : IsCyclicArc (Equiv.refl (Fin %d)) %s.sideA := by\n'
                   '  refine ⟨%d, %d, by decide, Or.inl ?_⟩\n'
                   '  rw [%s_sideA]; ext x; fin_cases x <;> decide' % (nm((i, j)), N, nm((i, j)), i, j, nm((i, j))))
    return '\n\n'.join(out)


def ne_lemmas():
    """v₅ 的 if 链需要 `f_k ≠ f_j`（j < k）。"""
    out = []
    for k in range(len(REPS)):
        for j in range(k):
            out.append('@[simp] theorem %s_ne_%s : %s ≠ %s := by decide'
                       % (nm(REPS[k]), nm(REPS[j]), nm(REPS[k]), nm(REPS[j])))
    return '\n'.join(out)


def wformula(p):
    i, j = p
    if (i, j) == (0, 0):
        return '(d 0 1 + d 0 %d - d 1 %d) / 2' % (N - 1, N - 1)
    if i == 0:
        return '(d %d %d - d 0 %d - d %d %d + d 0 %d) / 2' % (N - 1, j, j, N - 1, j + 1, j + 1)
    return '(d %d %d - d %d %d - d %d %d + d %d %d) / 2' % (i - 1, j, i, j, i - 1, j + 1, i, j + 1)


def v_lemmas():
    out = []
    for p in REPS:
        out.append('@[simp] theorem v%d_%s (d : Fin %d → Fin %d → ℝ) :\n'
                   '    v%d d %s = %s := by simp [v%d]'
                   % (N, nm(p), N, N, N, nm(p), wformula(p), N))
    return '\n\n'.join(out)


def sum_expansion():
    """10 项 sum 展开：sum_insert 的侧条件用反向 ne 引理。"""
    lines = []
    for k in range(len(REPS) - 1):
        flipped = ', '.join('(%s_ne_%s).symm' % (nm(REPS[j]), nm(REPS[k])) for j in range(k + 1, len(REPS)))
        seps = 'Finset.mem_insert, Finset.mem_singleton' if k + 1 < len(REPS) - 1 else 'Finset.mem_singleton'
        lines.append('    Finset.sum_insert (by simp [%s, %s]),' % (seps, flipped))
    rhs = ''
    for k, p in enumerate(REPS):
        rhs += 'w %s * sepInd %s x y' % (nm(p), nm(p))
        if k < len(REPS) - 1:
            rhs = '(%s + ' % rhs
        else:
            rhs = rhs + ')' * (len(REPS) - 1)
    return ('''theorem phyleticDist_ten (w : Split (Fin %d) → ℝ) (x y : Fin %d) :
    phyleticDist G%d w x y = %s := by
  simp only [phyleticDist, sepInd, G%d]
  rw [%s
    Finset.sum_singleton]
  try ring''' % (N, N, N, rhs, N, '\n'.join(lines)))


def symmetry_facts():
    facts = []
    for a in range(N):
        for b in range(a + 1, N):
            facts.append('h%d%d' % (a, b))
    return ', '.join(facts)


def diagonal_facts():
    return ', '.join('hd%d' % a for a in range(1, N))


def realizes():
    hyp = ' '.join('(h%d%d : d %d %d = d %d %d)' % (a, b, a, b, b, a) for a in range(N) for b in range(a + 1, N))
    return ('''/-- ★★★ **`n = %d` 的恒等**（干净上下文：只带具体的对称/对角等式）。 -/
theorem v%d_realizes (d : Fin %d → Fin %d → ℝ) %s
    %s :
    ∀ x y : Fin %d, x ≠ y → phyleticDist G%d (v%d d) x y = d x y := by
  intro x y hxy
  rw [phyleticDist_ten (v%d d) x y]
  simp only [%s]
  fin_cases x <;> fin_cases y <;>
    simp_all [sepInd, %s] <;>
    linarith [%s]'''
            % (N, N, N, N, hyp,
               ' '.join('(hd%d : d %d %d = 0)' % (a, a, a) for a in range(1, N)),
               N, N, N, N,
               ', '.join('v%d_%s' % (N, nm(p)) for p in REPS),
               ', '.join(nm(p) for p in REPS), symmetry_facts() + ', ' + diagonal_facts()))


def nonneg_branch(p):
    """按 (C) 的路线图给出非负性：L→triangle, H→ineq1, D→ineq2。"""
    i, j = p
    if (i, j) == (0, 0):
        call = 'kalmanson_triangle (Equiv.refl (Fin %d)) d hdiag hd 0 1 %d (by decide) (by decide)' % (N, N - 1)
    elif i == 0:
        call = ('kalmanson_H (Equiv.refl (Fin %d)) d hsym hd 0 %d %d %d (by decide) (by decide) (by decide)'
                % (N, j, j + 1, N - 1))
    else:
        call = ('kalmanson_D (Equiv.refl (Fin %d)) d hd %d %d %d %d (by decide) (by decide) (by decide)'
                % (N, i - 1, i, j, j + 1))
    return ('''    · rw [v%d_%s]
      have h := %s
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith''' % (N, nm(p), call))


def instance():
    circ = '\n'.join('    · exact Or.inl isCyclicArc_%s' % nm(p) for p in REPS)
    nonneg = '\n'.join(nonneg_branch(p) for p in REPS)
    symm_args = ' '.join('(hsym %d %d)' % (a, b) for a in range(N) for b in range(a + 1, N))
    diag_args = ' '.join('(hdiag %d)' % a for a in range(1, N))
    return ('''/-- ★★★ **`n = %d` 实例（修复形态）**：环形（Kalmanson）+ 对称 + 零对角 `d` 由**非负**加权
环形族实现；权重是 §7 逆矩阵的行（`v%d`），非负性用一般 `n` 的 `kalmanson_*` 引理。 -/
theorem circularRealization_fin%d (d : Fin %d → Fin %d → ℝ) (hdiag : ∀ x, d x x = 0)
    (hsym : ∀ x y, d x y = d y x) (hd : IsCircularDist (Equiv.refl (Fin %d)) d) :
    ∃ (F : Finset (Split (Fin %d))) (w : Split (Fin %d) → ℝ),
      Circular (↑F : Set (Split (Fin %d))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
        ∀ x y : Fin %d, x ≠ y → phyleticDist F w x y = d x y := by
  refine ⟨G%d, v%d d, ?_, ?_, ?_⟩
  · refine ⟨%d, Equiv.refl (Fin %d), fun s hs => ?_⟩
    have hs' : s ∈ G%d := hs
    simp only [G%d, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with %s
%s
  · intro s hs
    have hs' : s ∈ G%d := hs
    simp only [G%d, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with %s
%s
  · exact v%d_realizes d %s %s'''
            % (N, N, N, N, N, N, N, N, N, N, N, N, N,
               N, N, N, ' | '.join(['rfl'] * len(REPS)), circ,
               N, N, ' | '.join(['rfl'] * len(REPS)), nonneg,
               N, symm_args, diag_args))


def section94():
    splits = '\n\n'.join(
        '/-- 代表弧 `[%d,%d]` 的 split：`{%s} | 其余`。 -/\ndef %s : Split (Fin %d) := '
        'ofSideA %s (by decide) (by decide)' % (i, j, ', '.join(str(t) for t in range(i, j + 1)),
                                                  nm((i, j)), N, setlit(i, j))
        for (i, j) in REPS)
    gset = ', '.join(nm(p) for p in REPS)
    vbody = '\n'.join(
        ('' if k == 0 else '  else ') + ('if s = %s then %s' % (nm(p), wformula(p))) + ('' if k < len(REPS) - 1 else '\n  else 0')
        for k, p in enumerate(REPS))
    return ('''/-! ### 9.4 `n = %d` 实例（`X = Fin %d`，环序 = 恒等）

代表弧 `[i,j]`（`j ≤ %d`）共 `binom %d 2 = %d` 条；权重由 §7 逆矩阵的行给出。
本节的 boilerplate（%d 条 pairwise 互异、%d 条弧见证、%d 条权重公式）由
`scripts/msc/w12g_fin5_instance_gen.py` 机械生成。 -/

%s

/-- ★ 环形族（`Fin %d`：代表弧 `[i,j]`，`j ≤ %d`）。 -/
def G%d : Finset (Split (Fin %d)) := {%s}

/-- ★ **显式解出的权重**（§7 的逆矩阵行：L / H / D）。 -/
noncomputable def v%d (d : Fin %d → Fin %d → ℝ) : Split (Fin %d) → ℝ := fun s =>
  %s

%s

%s

%s

%s

%s

%s

%s

''' % (N, N, N - 2, N, len(REPS), len(REPS) * (len(REPS) - 1) // 2, len(REPS), len(REPS),
       splits, N, N - 2, N, N, gset,
       N, N, N, N, vbody,
       sideA_lemmas(), cyclic_lemmas(), ne_lemmas(), v_lemmas(), sum_expansion(), realizes(), instance()))


def section95():
    return '''/-! ### 9.5 ★B：`n = 3` 的**具体** `d` 与解出的 `w` -/

/-- ★B 具体距离：非对角 `1`、对角 `0`（`Fin 3`）。 -/
def d3one : Fin 3 → Fin 3 → ℝ := fun x y => if x = y then 0 else 1

theorem d3one_symm (x y : Fin 3) : d3one x y = d3one y x := by
  unfold d3one
  fin_cases x <;> fin_cases y <;> norm_num

theorem d3one_diag (x : Fin 3) : d3one x x = 0 := by
  unfold d3one; simp

/-- ★B **具体实例**：`d3one` 解出的三条权重都是 `1/2`，且族 `G₃` 的系统发生距离**恰**等于 `d3one`。 -/
example : v₃ d3one c₀ = 1 / 2 ∧ v₃ d3one c₁ = 1 / 2 ∧ v₃ d3one c₂ = 1 / 2 ∧
    ∀ x y : Fin 3, x ≠ y → phyleticDist G₃ (v₃ d3one) x y = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v₃_c₀]; norm_num [d3one]
  · rw [v₃_c₁]; norm_num [d3one]
  · rw [v₃_c₂]; norm_num [d3one]
  · intro x y hxy
    rw [v₃_realizes d3one (d3one_symm 0 1) (d3one_symm 0 2) (d3one_symm 1 2)
      (d3one_diag 1) (d3one_diag 2) x y hxy]
    unfold d3one
    simp [hxy]


'''


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'Phylo/Algorithm/NeighborNet.lean'
    src = open(path, encoding='utf-8').read()
    if '### 9.4' in src:
        print('§9.4/§9.5 already present in', path, '— nothing to do (幂等)')
        return
    anchor = 'end CircularRealization\n\nend NeighborNet'
    assert src.count(anchor) == 1, src.count(anchor)
    src = src.replace(anchor, section94() + section95() + 'end CircularRealization\n\nend NeighborNet')
    open(path, 'w', encoding='utf-8', newline='\n').write(src)
    print('generated §9.4/§9.5 into', path)


if __name__ == '__main__':
    main()
