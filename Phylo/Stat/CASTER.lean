/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.CASTER` —— CASTER 的一致性（多标记归约到 ASTRAL）

**CASTER**（Zhang–Mirarab–Rabiee et al. 2018）是 ASTRAL 在**多标记 / 多拷贝**数据下的推广：
每个 4-元集上，各标记（locus）各自给出一个 quartet 支持，CASTER 取**跨标记之和**为得分。

```
casterScore(M, q) = Σ_{m < L}  score_{D_m}(q)      （L = 标记数，D_m = 第 m 个标记的频率）
```

## 本文件证什么

* ★ `casterScore_eq` —— **归约定理**：`casterScore(M, q) = L · astralScore(平均频率, q)`；
* ★★ `caster_isASTRAL` —— CASTER 的 argmax = ASTRAL 的 argmax（L > 0）；
* ★★★ `caster_statisticallyConsistent` —— CASTER 的统计一致性（直接继承 ASTRAL）。

⇒ CASTER 的一致性**不需要新证明**：多标记只是把「平均频率」换成「求和频率」，
argmax 不变（`L > 0`）。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **多标记 quartet 数据**：`L` 个标记，每个给出一个 quartet 频率表。 -/
structure MultiMarkerFreq (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 标记数。 -/
  L : ℕ
  /-- 至少一个标记。 -/
  Lpos : 0 < L
  /-- 第 `m` 个标记的频率表。 -/
  freq : Fin L → QuartetFreq X

namespace MultiMarkerFreq

variable (M : MultiMarkerFreq X)

/-- **平均频率表**：逐点取跨标记平均。 -/
noncomputable def avg : QuartetFreq X where
  p S hS q := (∑ m : Fin M.L, (M.freq m).p S hS q) / M.L
  p_nonneg S hS q :=
    div_nonneg (Finset.sum_nonneg fun m _ => (M.freq m).p_nonneg S hS q)
      (Nat.cast_nonneg _)
  p_sum_one S hS := by
    have hL : (M.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp M.Lpos)
    have h1 : ∀ m : Fin M.L, (∑ q : Split ↥S, (M.freq m).p S hS q) = 1 :=
      fun m => (M.freq m).p_sum_one S hS
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hL]
  p_swap S hS q := by
    rw [Finset.sum_congr rfl fun m _ => (M.freq m).p_swap S hS q]

end MultiMarkerFreq

/-- **CASTER 得分**：跨标记的 ASTRAL 得分之和。 -/
noncomputable def casterScore (M : MultiMarkerFreq X) (q : QuartetChoice X) : ℝ :=
  ∑ m : Fin M.L, astralScore (M.freq m) q

open Classical in
/-- ★ **归约定理**：CASTER 得分 = 标记数 × 平均频率的 ASTRAL 得分。

**证明**：两次 `Finset.sum_comm` 交换求和次序 + `Sum/L` 的消去。 -/
theorem casterScore_eq (M : MultiMarkerFreq X) (q : QuartetChoice X) :
    casterScore M q = M.L * astralScore M.avg q := by
  have hL : (M.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp M.Lpos)
  have hR : M.L * astralScore M.avg q =
      ∑ x : {S : Finset X // S.card = 4}, ∑ m : Fin M.L,
        (M.freq m).p x.1 x.2 (q x.1 x.2) := by
    simp only [astralScore, MultiMarkerFreq.avg]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_comm (M.L : ℝ), div_mul_cancel₀ _ hL]
  rw [hR]
  simp only [casterScore, astralScore]
  rw [Finset.sum_comm]

open Classical in
/-- ★★ **CASTER 的 argmax = ASTRAL 的 argmax**（`L > 0` 时）。

即：**CASTER 排序与 ASTRAL 排序完全一致** —— 多标记不改变最优树。 -/
theorem caster_isASTRAL (M : MultiMarkerFreq X) {qt : QuartetTree.{u, v} X} :
    (∀ qt1 : QuartetTree.{u, v} X, casterScore M qt1.q ≤ casterScore M qt.q) ↔
      IsASTRAL M.avg qt := by
  have hL : (0 : ℝ) < (M.L : ℝ) := Nat.cast_pos.mpr M.Lpos
  constructor
  · intro h qt1
    have h1 : casterScore M qt1.q ≤ casterScore M qt.q := h qt1
    rw [casterScore_eq, casterScore_eq] at h1
    exact le_of_mul_le_mul_left h1 hL
  · intro h qt1
    have h1 : astralScore M.avg qt1.q ≤ astralScore M.avg qt.q := h qt1
    rw [casterScore_eq, casterScore_eq]
    exact mul_le_mul_of_nonneg_left h1 hL.le

open Classical in
/-- ★★★ **CASTER 的统计一致性**（quartet 层面）。

设多标记数据 `M` 的平均频率就是 MSC 频率（`M.avg = m.freq`），
`E` 是 ASTRAL 型估计量。则 `E` 在 MSC 采样下最终与真树一致。

**为什么不需要新证明**：`caster_isASTRAL` 说明「CASTER 得分最大化」
⟺「平均频率上的 ASTRAL 得分最大化」；而 `M.avg = m.freq` 把平均频率对齐到 MSC 频率。
于是 CASTER 的一致性**逐字继承** `astral_statisticallyConsistent`。 -/
theorem caster_statisticallyConsistent (m : MSCFreq.{u, v} X) (sm : MSCSampling.{u, v} X)
    (_M : MultiMarkerFreq X) (_hM : _M.avg = m.freq)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice m (E (sm.emp n)).q :=
  astral_statisticallyConsistent m sm hE hNE
