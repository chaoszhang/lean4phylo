/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# `Phylo.Stat.SVDQuartets` —— SVDQuartets 的秩判据与正确性

**方法**（Chifman–Kubatko 2014, 2015）。对 4 个分类群 `a,b,c,d` 与 3 个候选（无根）拓扑
`ab|cd`、`ac|bd`、`ad|bc`，各构造一个 **展平矩阵（flattening）** `Flat`（皆为 `κ² × κ²`，
`κ` = 状态数，DNA 取 `κ = 4`），**选秩最小者**为推断拓扑。

**理论**（Allman–Long–Rhodes 2023, *Phylogenomic Models from Tree Symmetries*, Thm 3.3 / 3.4）
以一个 **2-clade（根侧的两个叶，即 rooted cherry）** 为核心：

> 若 `{a,b}` 是物种树上的 2-clade，则位点模式分布 `P` 在交换 `a`、`b` 下不变。
> 于是 `Flat_ab|cd` 的第 `(i,j)` 行与第 `(j,i)` 行**完全相同**，
> 故不同的行至多 `κ² − C(κ,2) = C(κ+1,2)` 个，从而

```
rank (Flat_ab|cd P) ≤ C(κ+1, 2)
```

而另两个（"错"的）展平在一般参数下**满秩** `κ²`。因 `C(κ+1,2) < κ²`（`κ ≥ 2`），
SVDQuartets 的"取最小秩"规则**选中真拓扑**。

本文件给出：
* ★★ `rank_le_of_row_symm` —— 「行成对相同 ⟹ 秩 ≤ `C(κ+1,2)`」（纯线性代数，用 `Sym2`）；
* ★★ `rank_flatAB_le` —— `{a,b}` 或 `{c,d}` 是 2-clade ⟹ `rank (Flat_ab|cd) ≤ C(κ+1,2)`；
* ★ `rank_flatAB_le_four` —— DNA（`κ = 4`）：`rank ≤ 10 < 16`；
* ★★ `choose_two_lt_sq` —— `C(κ+1,2) < κ²`（`κ ≥ 2`）；
* ★★★ `svdquartets_selects_true` —— 在"错展平满秩"的一般性假设下，真拓扑被选中。

**诚实边界**："错展平满秩"是 **generic（一般参数）** 陈述（论文用 JC 模型构造出一个满秩点，
并论证该条件定义的是真子簇、测度零）。本文件把它作为**显式假设**传入
（与库内 `MaxZCherryCore` 的惯例一致），**不写 `sorry`**。
-/

universe u

/-! ## 位点模式分布与展平矩阵 -/

/-- **位点模式频率张量**：4 个（有序）分类群，每个取 `κ` 个状态之一。
`P i j k l` = 分类群 `(a,b,c,d)` 分别处于状态 `(i,j,k,l)` 的概率。 -/
abbrev SiteFreq (κ : Type*) := κ → κ → κ → κ → ℝ

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **`ab|cd` 展平**：行指标 = `(a,b)` 的状态对，列指标 = `(c,d)` 的状态对。 -/
def flatAB (P : SiteFreq κ) : Matrix (κ × κ) (κ × κ) ℝ :=
  fun ij kl => P ij.1 ij.2 kl.1 kl.2

/-- **`ac|bd` 展平**：行指标 = `(a,c)`，列指标 = `(b,d)`。 -/
def flatAC (P : SiteFreq κ) : Matrix (κ × κ) (κ × κ) ℝ :=
  fun ik jl => P ik.1 jl.1 ik.2 jl.2

/-- **`ad|bc` 展平**：行指标 = `(a,d)`，列指标 = `(b,c)`。 -/
def flatAD (P : SiteFreq κ) : Matrix (κ × κ) (κ × κ) ℝ :=
  fun il jk => P il.1 jk.1 jk.2 il.2

/-! ## 2-clade 对称性

`UE` 模型（Definition 2.1）要求：对每个子集 `Y`、每个 `ψ⁺|_Y` 上的 2-clade `{a,b}`，
`Y` 上的边缘分布对交换 `a`、`b` 不变。在 4 分类群上只需要 `ψ⁺|{a,b,c,d}` 的某个
2-clade —— 即 `{a,b}` 或 `{c,d}` 二者之一。 -/

/-- 分布对分类群 `a`、`b` **交换对称**（2-clade `{a,b}` 的直接后果）。 -/
def SymmAB (P : SiteFreq κ) : Prop := ∀ i j k l, P i j k l = P j i k l

/-- 分布对分类群 `c`、`d` **交换对称**（2-clade `{c,d}` 的直接后果）。 -/
def SymmCD (P : SiteFreq κ) : Prop := ∀ i j k l, P i j k l = P i j l k

/-! ## ★★ 核心：行成对相同 ⟹ 秩 ≤ `C(κ+1,2)` -/

/-- ★★ **行成对相同 ⟹ 秩 ≤ `C(κ+1,2)`**。

行指标 `(i,j)` 与 `(j,i)` 相同时，行的取值可经**无序对** `Sym2 κ` 分解；
`Sym2 κ` 的基数为 `C(κ+1,2)`，故秩不超过它。

（`Matrix.rank_le_card_height` 给出"行数"上界；`Sym2.card` 给出基数的显式值。） -/
theorem rank_le_of_row_symm {ν : Type*} [Fintype ν] (M : Matrix (κ × κ) ν ℝ)
    (h : ∀ i j v, M (i, j) v = M (j, i) v) :
    M.rank ≤ (Fintype.card κ + 1).choose 2 := by
  classical
  let f : κ → κ → (ν → ℝ) := fun i j => M (i, j)
  have hf : ∀ i j, f i j = f j i := fun i j => funext fun v => h i j v
  let N : Matrix (Sym2 κ) ν ℝ := Sym2.lift ⟨f, hf⟩
  have hN : ∀ i j, N (Sym2.mk i j) = M (i, j) := by
    intro i j
    show Sym2.lift ⟨f, hf⟩ (Sym2.mk i j) = M (i, j)
    rw [Sym2.lift_mk]
  have hMN : M = N.submatrix (fun p : κ × κ => Sym2.mk p.1 p.2) id := by
    funext p v
    exact (congrFun (hN p.1 p.2) v).symm
  rw [hMN]
  calc (N.submatrix (fun p : κ × κ => Sym2.mk p.1 p.2) id).rank
      ≤ N.rank := Matrix.rank_submatrix_le N _ _
    _ ≤ Fintype.card (Sym2 κ) := Matrix.rank_le_card_height N
    _ = (Fintype.card κ + 1).choose 2 := by
        rw [Sym2.card]

/-! ## ★★ SVDQuartets 的秩上界 -/

/-- ★★ **真拓扑的展平秩 ≤ `C(κ+1,2)`**。

若 2-clade 是 `{a,b}`，则 `SymmAB` 使 `Flat_ab|cd` 的行 `(i,j)` 与 `(j,i)` 相同；
若 2-clade 是 `{c,d}`，则 `SymmCD` 使**列** `(k,l)` 与 `(l,k)` 相同 —— 转置后同理。 -/
theorem rank_flatAB_le (P : SiteFreq κ) (h : SymmAB P ∨ SymmCD P) :
    (flatAB P).rank ≤ (Fintype.card κ + 1).choose 2 := by
  classical
  rcases h with h | h
  · -- 行对称
    refine rank_le_of_row_symm (flatAB P) fun i j kl => ?_
    exact h i j kl.1 kl.2
  · -- 列对称：转置后行对称
    have hrow : ∀ k l v, (Matrix.transpose (flatAB P)) (k, l) v
        = (Matrix.transpose (flatAB P)) (l, k) v := by
      intro k l v
      obtain ⟨i, j⟩ := v
      exact h i j k l
    have hh := rank_le_of_row_symm (Matrix.transpose (flatAB P)) hrow
    rwa [Matrix.rank_transpose] at hh

/-- ★ **DNA 情形（`κ = 4`）**：真拓扑的展平秩 `≤ 10`（而满秩为 `16`）。 -/
theorem rank_flatAB_le_four (P : SiteFreq (Fin 4)) (h : SymmAB P ∨ SymmCD P) :
    (flatAB P).rank ≤ 10 := by
  have hh := rank_flatAB_le P h
  rw [Fintype.card_fin] at hh
  norm_num at hh
  exact hh

/-! ## ★★★ SVDQuartets 选中真拓扑 -/

/-- ★★ `C(κ+1,2) < κ²`（`κ ≥ 2`）—— 真拓扑的秩严格小于错拓扑的满秩。 -/
theorem choose_two_lt_sq {n : ℕ} (hn : 2 ≤ n) : (n + 1).choose 2 < n * n := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  nlinarith [hn]

/-- ★★ **若某"错"展平满秩 `κ²`，则真展平秩严格更小**。 -/
theorem rank_lt_full_of_symm (P : SiteFreq κ) (h : SymmAB P ∨ SymmCD P)
    {r : ℕ} (hr : r = Fintype.card κ * Fintype.card κ) (hκ : 2 ≤ Fintype.card κ) :
    (flatAB P).rank < r := by
  rw [hr]
  exact lt_of_le_of_lt (rank_flatAB_le P h) (choose_two_lt_sq hκ)

/-- ★★★ **SVDQuartets 选中真拓扑**：真拓扑 `ab|cd` 的展平秩严格小于两个"错"展平。 -/
theorem svdquartets_selects_true (P : SiteFreq κ) (h : SymmAB P ∨ SymmCD P)
    (hfullAC : (flatAC P).rank = Fintype.card κ * Fintype.card κ)
    (hfullAD : (flatAD P).rank = Fintype.card κ * Fintype.card κ)
    (hκ : 2 ≤ Fintype.card κ) :
    (flatAB P).rank < (flatAC P).rank ∧ (flatAB P).rank < (flatAD P).rank :=
  ⟨rank_lt_full_of_symm P h hfullAC hκ, rank_lt_full_of_symm P h hfullAD hκ⟩

/-! ## ★★★ 分离性：对称性**不**限制"错"展平的秩（具体实例）

`rank_flatAB_le` 只给出真展平秩的上界；要得到 SVDQuartets 的**正确性**，还需要
"错展平满秩"是**可实现**的（论文的 generic 论证给的是"存在一个满秩点"）。

下面给出一个**显式张量族**：取

```
P_c(i,j,k,l) = c · [i = j] · [k = l]      (c ≠ 0)
```

* `P_c` 对 `a,b` 与 `c,d` **都**交换对称；
* `Flat_ac|bd(P_c) = Flat_ad|bc(P_c) = diagonal (fun _ => c)`，秩恰为 `κ²`（**满秩**）；
* `Flat_ab|cd(P_c)` 的行 `(i,j)` 等于 `c·[i=j]·(k=l 的指示向量)`，故秩为 `1`
  （`c ≠ 0` 时），自然 `≤ C(κ+1,2)`。

⇒ 由 `svdquartets_selects_true`，SVDQuartets 在该分布上**无条件**选中真拓扑 `ab|cd`。

（`P_c` 各项非负；`c = 1/κ²` 时总和为 1，即一个真正的位点模式分布。） -/

/-- **分离性例**：`P i j k l = c · [i = j] · [k = l]`（`c ≠ 0`）。 -/
noncomputable def sepFreq (c : ℝ) : SiteFreq κ :=
  fun i j k l => if i = j ∧ k = l then c else 0

/-- `sepFreq c` 对 `a,b` 交换对称。 -/
theorem sepFreq_symmAB (c : ℝ) : SymmAB (sepFreq (κ := κ) c) := by
  intro i j k l
  by_cases h : i = j
  · subst h; rfl
  · have h' : ¬ (j = i) := fun hh => h hh.symm
    simp only [sepFreq, h, h', false_and, if_false]

/-- `sepFreq c` 对 `c,d` 交换对称。 -/
theorem sepFreq_symmCD (c : ℝ) : SymmCD (sepFreq (κ := κ) c) := by
  intro i j k l
  by_cases h : k = l
  · subst h; rfl
  · have h' : ¬ (l = k) := fun hh => h hh.symm
    simp only [sepFreq, h, h', and_false, if_false]

/-- `Flat_ac|bd(sepFreq c)` 是对角矩阵 `diagonal (fun _ => c)`。 -/
theorem sepFreq_flatAC (c : ℝ) :
    flatAC (sepFreq (κ := κ) c) = Matrix.diagonal (fun _ : κ × κ => c) := by
  funext p q
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  show (if i = j ∧ k = l then c else 0)
      = Matrix.diagonal (fun _ : κ × κ => c) (i, k) (j, l)
  rw [Matrix.diagonal_apply]
  by_cases h : (i, k) = (j, l)
  · rw [if_pos h]
    exact if_pos (Prod.ext_iff.mp h)
  · rw [if_neg h]
    exact if_neg fun hh => h (Prod.ext_iff.mpr hh)

/-- `Flat_ad|bc(sepFreq c)` 是对角矩阵 `diagonal (fun _ => c)`。 -/
theorem sepFreq_flatAD (c : ℝ) :
    flatAD (sepFreq (κ := κ) c) = Matrix.diagonal (fun _ : κ × κ => c) := by
  funext p q
  obtain ⟨i, l⟩ := p
  obtain ⟨j, k⟩ := q
  show (if i = j ∧ k = l then c else 0)
      = Matrix.diagonal (fun _ : κ × κ => c) (i, l) (j, k)
  rw [Matrix.diagonal_apply]
  by_cases h : (i, l) = (j, k)
  · rw [if_pos h]
    refine if_pos ?_
    exact ⟨(Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2.symm⟩
  · rw [if_neg h]
    refine if_neg fun hh => h ?_
    exact Prod.ext_iff.mpr ⟨hh.1, hh.2.symm⟩

/-- ★★ **"错"展平满秩 `κ²`**（分离性：`SymmAB` 对 `ac|bd` 展平的秩无任何限制）。 -/
theorem sepFreq_flatAC_rank (c : ℝ) (hc : c ≠ 0) :
    (flatAC (sepFreq (κ := κ) c)).rank = Fintype.card κ * Fintype.card κ := by
  rw [sepFreq_flatAC, Matrix.rank_diagonal]
  have hf : (Finset.univ.filter fun _ : κ × κ => c ≠ 0) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => hc
  rw [Fintype.card_subtype, hf, Finset.card_univ, Fintype.card_prod]

/-- ★★ `ad|bc` 展平也满秩 `κ²`。 -/
theorem sepFreq_flatAD_rank (c : ℝ) (hc : c ≠ 0) :
    (flatAD (sepFreq (κ := κ) c)).rank = Fintype.card κ * Fintype.card κ := by
  rw [sepFreq_flatAD, Matrix.rank_diagonal]
  have hf : (Finset.univ.filter fun _ : κ × κ => c ≠ 0) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => hc
  rw [Fintype.card_subtype, hf, Finset.card_univ, Fintype.card_prod]

/-- ★★★ **SVDQuartets 正确性的无条件实例**。

对 `P_c(i,j,k,l) = c[i=j][k=l]`（`c ≠ 0`，`κ ≥ 2`），真拓扑 `ab|cd` 的展平秩
**严格小于**两个"错"展平 —— 故 SVDQuartets 选中真拓扑。

（这就是论文"构造一个满秩点"那一步在库内的落地；一般参数下的版本是
`svdquartets_selects_true`，其"满秩"假设由本条说明**并非空**。） -/
theorem svdquartets_concrete (c : ℝ) (hc : c ≠ 0) (hκ : 2 ≤ Fintype.card κ) :
    (flatAB (sepFreq (κ := κ) c)).rank < (flatAC (sepFreq (κ := κ) c)).rank ∧
      (flatAB (sepFreq (κ := κ) c)).rank < (flatAD (sepFreq (κ := κ) c)).rank :=
  svdquartets_selects_true (sepFreq (κ := κ) c) (Or.inl (sepFreq_symmAB c))
    (sepFreq_flatAC_rank c hc) (sepFreq_flatAD_rank c hc) hκ
