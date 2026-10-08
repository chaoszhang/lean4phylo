/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.SVDQuartets

/-!
# `Phylo.Stat.InvariantsRank` —— I4：边缘化 ⟹ 展平秩 ≤ κ ⟹ 五阶子式为零

**文献**：E. S. Allman, J. A. Rhodes, *Phylogenetic ideals and varieties for the general Markov
model*，库内文本 `references/md/AllmanRhodes2006_PhyloIdealsVarietiesGeneralMarkov.md`
（共 1834 行；下列行号均指该文件，**不是** `NEXT.md` 的状态栏）：

* **§4 "Flattenings and phylogenetic invariants"（697–779 行）**
  * **704–712 行**：沿边 `e` 的**展平** `F = F late(P)` 的定义（`κ^k × κ^(n−k)` 矩阵）；
  * **714–725 行 + Fig. 2（758 行）**：展平 = 「**1 个 κ 状态隐变量** + 2 个观测量」的
    **粗化图模型** —— 即「**沿一条边把 site-pattern 概率对一端的状态求和（边缘化）**」；
  * **760–768 行**：`F late(P) = M₁ᵀ diag(π_r) M₂`（`M₁ : κ × κ^k`，`M₂ : κ × κ^(n−k)`）
    ⟹ **`rank F late(P) ≤ κ`**；
  * **770 行**：「As a result, all **(κ+1)×(κ+1) minors** of `F late(P)` must vanish.」
    —— 文献把这一步当作经典线性代数事实，**未给证明**（本文件 §1 补上）；
  * **776–779 行**：这些极小式记为 `Fedge(T)`，称沿 `e` 的 **edge invariants**。
* **Theorem 4（§4, 785–788 行；证明在 §8）**：`κ = 2` 时 `Fedge(T)` **生成**整个不变量理想
  —— **本文件不做**（见「诚实边界」）。
* **790–795 行**：`κ > 2` 时仅有边展平**不够**，还需内部顶点上的展平 —— 本文件不做。
* **129–137 行**：以 5 分类群为例说明定理 4 的显式形式（`3 × 3` 子式生成素理想）。

**本文件的数学内容（I4 的代数内核）**

1. **秩 ≤ k ⟹ (k+1) 阶子式为零**：`rank_minor_eq_zero_of_rank_le`（一般 `k`），
   `rank_minor_eq_zero_of_rank_le_five'`（`rank ≤ 4` ⟹ `5×5` 子式为 0）。
2. **因子分解 ⟹ 秩上界**：`rank_flatAB_le_of_factor` ——
   「`P i j k l = ∑ m, A (i,j) m * B m (k,l)`（中间维数 `κ`）」⟹ `(flatAB P).rank ≤ κ`。
   这正是「**树上过一条边的条件独立性（Markov 性）**」的代数形式。
3. **DNA 专门化**：`rank_flatAB_le_four_of_factor`、`rank_flatAB_le_four_iff_minor`
   （`κ = Fin 4` + 因子分解 ⟹ 所有 `5×5` 子式为 0）。
4. **条数**：`invariantMinorCount κ = (κ²).choose 5 ^ 2`；
   `invariantCount_fin_four : invariantMinorCount (Fin 4) = 4368 ^ 2`（`Nat.choose 16 5 = 4368`）。

## 已证清单（全部零 `sorry`、零 `axiom`）

| 声明 | 一句话 |
|---|---|
| `rank_minor_eq_zero_of_rank_le` | ★★ `M.rank ≤ k ⟹ (M.submatrix r c).det = 0`，`r c : Fin (k+1) → _` |
| `rank_minor_eq_zero_of_rank_le_five'` | ★★ `M.rank ≤ 4 ⟹ 任意 5×5 子式 = 0` |
| `rank_flatAB_le_of_factor` | ★★★ 因子分解（中间维数 `κ`）⟹ `(flatAB P).rank ≤ Fintype.card κ` |
| `rank_flatAB_le_four_of_factor` | ★★ `κ = Fin 4` + 因子分解 ⟹ `(flatAB P).rank ≤ 4` |
| `rank_flatAB_le_four_iff_minor` | ★ `κ = Fin 4` + 因子分解 ⟹ 所有 `5×5` 子式为 0 |
| `invariantMinorCount` | ★★ 五阶不变量条数 `= (κ²).choose 5 ^ 2`（`5` 元指标**子集**，非有序组） |
| `invariantCount_fin_four` | ★★ `= 4368 ^ 2`（`Nat.choose 16 5 = 4368`） |
| `card_minorIndexPairs` | ★★ 两个 `5` 元指标子集类型的基数 `= invariantMinorCount κ` |
| `TreeMarkovFactorGap` | **缺口**的类型化陈述（见下） |
| `treeMarkovFactorGap_holds` | 该缺口命题的**已证代数半边** |

## 诚实边界（**纪律 12**）

* **未做（核心缺口）**：从树的 Markov 模型（`Phylo.Stat.JukesCantor` 的 `patternProb`，
  或一般树 GMM）**推出**本文件的因子分解假设。本文件**只**证
  「给定因子分解 ⟹ 秩 ≤ κ ⟹ 子式为零」，
  **不**把因子分解冒充成「由 Markov 模型导出的定理」。
  该欠账以 `TreeMarkovFactorGap` 显式类型化（「一般模型层」的欠账：需要
  一般树 GMM 的 site-pattern 概率定义 + 沿边边缘化公式 + 两侧 Markov 矩阵构造）。
* **未做**：Allman–Rhodes **Theorem 4 / Theorem 11**（`Fedge(T)` **生成**整个不变量理想：
  含「素数性」「理想生成」两层，且 `κ > 2` 还需顶点展平）。本文件只证
  「这些子式是**不变量**（必然为零）」，**不**声称它们是理想生成元。
* **未做（可选阴性对照）**：本文件**没有**给出「无因子分解时存在非零 `5×5` 子式」的
  显式构造。理由是构造需要手工枚举 `Fin 5 → Fin 4 × Fin 4` 的置换型指标
  （在本次实现中该枚举的 `decide`/`simp` 化简开销与出错率都很高），
  故按协调侧建议删去。**因此本文件不声称**「五阶子式能区分拓扑」这一般性结论 ——
  库内 `SVDQuartets.sepFreq_flatAC_rank`（`flatAC (sepFreq c)` 满秩 `κ²`，DNA 即 `16`）
  可作为该方向的**间接**旁证（满秩矩阵的 `5×5` 子式不可能全为零），但它是在
  `SVDQuartets.lean` 里证的，本文件只**引用**、未复述。
* **未做**：`κ^k` 大小的展平（本文件只做 `k = 2`，即 4 分类群、`κ² × κ²` 展平）。
* **未做**：五阶子式**唯一决定**拓扑（需要一般参数下的「另一拓扑存在非零子式」定理）。
* 无 `sorry`、无 `axiom`；`#print axioms` 见文件末尾。
-/

universe u

namespace Phylo.Stat.InvariantsRank

open Matrix

variable {κ : Type*} [Fintype κ]

/-! ## 1. ★★ 一般线性代数：`rank ≤ k` ⟹ `(k+1) × (k+1)` 子式为零 -/

/-- ★★ **秩 ≤ `k` ⟹ `(k+1)` 阶子式为零**（完全一般的线性代数陈述；文献 770 行的那一步）。

证明路线：反设 `(M.submatrix r c).det ≠ 0`。方阵行列式非零 ⟹ 满秩
（`Matrix.rank_of_det_ne_zero`），故 `(M.submatrix r c).rank = k+1`。
再把子矩阵秩**单调性**用两次夹回 `M.rank ≤ k`：

* `(M.submatrix id c).submatrix r id` 与 `M.submatrix r c` **定义相等**（都是 `M (r i) (c j)`）；
* 故 `(M.submatrix r c).rank ≤ (M.submatrix id c).rank ≤ M.rank ≤ k`
  （两次 `Matrix.rank_submatrix_le`）。

于是 `k+1 ≤ k`，矛盾（`omega`）。 -/
theorem rank_minor_eq_zero_of_rank_le {m n : Type*} [Fintype m] [Fintype n] {k : ℕ}
    (M : Matrix m n ℝ) (hr : M.rank ≤ k) (r : Fin (k + 1) → m) (c : Fin (k + 1) → n) :
    (M.submatrix r c).det = 0 := by
  by_contra hne
  have hrank : (M.submatrix r c).rank = k + 1 := by
    simpa using Matrix.rank_of_det_ne_zero hne (R := ℝ)
  have hle : (M.submatrix r c).rank ≤ k := by
    calc (M.submatrix r c).rank
        = ((M.submatrix (id : m → m) c).submatrix r (id : Fin (k + 1) → Fin (k + 1))).rank := rfl
      _ ≤ (M.submatrix (id : m → m) c).rank := Matrix.rank_submatrix_le _ r id
      _ ≤ M.rank := Matrix.rank_submatrix_le M id c
      _ ≤ k := hr
  omega

/-- ★★ **`M.rank ≤ 4` ⟹ 一切 `5 × 5` 子式为 0**（任务书点名的形式）。 -/
theorem rank_minor_eq_zero_of_rank_le_five' {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hr : M.rank ≤ 4) (r : Fin 5 → m) (c : Fin 5 → n) :
    (M.submatrix r c).det = 0 :=
  rank_minor_eq_zero_of_rank_le M hr r c

/-! ## 2. ★★★ 因子分解 ⟹ 展平秩 ≤ `κ`（I4 的中心定理） -/

/-- ★★★ **因子分解 ⟹ `rank (flatAB P) ≤ κ`**（**I4 的代数内核**）。

设 `A : Matrix (κ × κ) κ ℝ`、`B : Matrix κ (κ × κ) ℝ` 且

```
∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)
```

（即 `flatAB P` 有一个**中间维数为 `κ` 的因子分解**），则 `(flatAB P).rank ≤ Fintype.card κ`。

**这是「树上过一条边的条件独立性（Markov 性）」的代数形式。** 对照 Allman–Rhodes 2006
**§4, 760–768 行** 的 `F late(P) = M₁ᵀ diag(π_r) M₂`（`M₁ : κ × κ^k`、`M₂ : κ × κ^(n−k)`）：
中间那个维数 `κ` 就是**被边缘化掉的隐内部节点的状态数** —— 沿边 `e` 把一端的隐状态
**求和掉**之后，分布成为「`κ^k` 状态观测量 — `κ` 维桥 — `κ^(n−k)` 状态观测量」的因子分解，
这正是「矩阵秩 ≤ κ」的分解形式。

（本文件**只**证这一条代数蕴含；**不**声称能由树模型推出该因子分解，见文件头「诚实边界」。） -/
theorem rank_flatAB_le_of_factor (P : SiteFreq κ)
    (A : Matrix (κ × κ) κ ℝ) (B : Matrix κ (κ × κ) ℝ)
    (hP : ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)) :
    (flatAB P).rank ≤ Fintype.card κ := by
  classical
  have hmat : flatAB P = A * B := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [flatAB]
    rw [Matrix.mul_apply]
    exact hP i j k l
  rw [hmat]
  exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)

/-- ★★ **DNA 情形（`κ = Fin 4`）**：只要 `P` 有因子分解，展平秩 `≤ 4`（而满秩为 `16`）。 -/
theorem rank_flatAB_le_four_of_factor (P : SiteFreq (Fin 4))
    (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ)
    (hP : ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)) :
    (flatAB P).rank ≤ 4 := by
  simpa using rank_flatAB_le_of_factor P A B hP

/-- ★ **DNA 情形收口**：`κ = Fin 4` 且有因子分解 ⟹ **所有 `5 × 5` 子式为 0**
（即所有五阶 edge invariants 为零）。这是 I4 的最终陈述形式（§1 + §2 合起来）。 -/
theorem rank_flatAB_le_four_iff_minor (P : SiteFreq (Fin 4))
    (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ)
    (hP : ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l))
    (r c : Fin 5 → Fin 4 × Fin 4) :
    ((flatAB P).submatrix r c).det = 0 :=
  rank_minor_eq_zero_of_rank_le (flatAB P) (rank_flatAB_le_four_of_factor P A B hP) r c

/-! ## 3. ★★ 五阶不变量的条数 -/

/-- ★★ **五阶不变量的条数**：展平矩阵为 `κ² × κ²`（DNA 取 `κ = 4`，即 `16 × 16`），
一个 `5 × 5` 子式由「选 5 个行指标」与「选 5 个列指标」**两个 `5` 元子集**唯一确定，
故条数为 `(κ²).choose 5 ^ 2`（`binom(κ², 5)²`）。

⚠️ 注意：这里数的是**子式**（无序的 `5` 元指标子集），
**不是**「有序 `5` 元指标组」（那是 `(κ²)^5 ^ 2`，数值大两个数量级）。
`NEXT.md` I4 行点名的 `binom(16,5)²` 是前者。 -/
def invariantMinorCount (κ : Type*) [Fintype κ] : ℕ :=
  (Fintype.card κ ^ 2).choose 5 ^ 2

/-- ★★ **DNA（`κ = Fin 4`）**：`Nat.choose 16 5 = 4368`，故五阶不变量条数为 `4368 ^ 2`。 -/
theorem invariantCount_fin_four : invariantMinorCount (Fin 4) = 4368 ^ 2 := by
  rw [invariantMinorCount, Fintype.card_fin]
  decide

/-- ★★ 条数的**类型论形式**：`5 × 5` 子式的指标是两个 `5` 元指标**子集**
（各行指标、列指标各一个），其类型基数为 `invariantMinorCount κ`。 -/
theorem card_minorIndexPairs (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Fintype.card ({s : Finset (κ × κ) // s.card = 5} × {s : Finset (κ × κ) // s.card = 5})
      = invariantMinorCount κ := by
  rw [Fintype.card_prod]
  simp only [Fintype.card_subtype]
  have hcard : (Finset.univ.filter fun s : Finset (κ × κ) => s.card = 5)
      = Finset.univ.powersetCard 5 := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, invariantMinorCount,
    Fintype.card_prod]
  ring

/-! ## 4. 诚实边界（显式缺口） -/

/-- **缺口（一般模型层）**：展平的因子分解假设本身。

`TreeMarkovFactorGap P` 表达「`P` 有某个中间维数 `4` 的因子分解 ⟹ 秩 ≤ 4」这一**已证**
的代数半边（见 `treeMarkovFactorGap_holds`）；它是把「模型半边」显式隔离出来的占位。

**未证的是它的前提**：「`P` 来自某棵 4 叶树上的（一般）Markov 模型 ⟹ 存在这样的 `A, B`」。
这需要：(i) 一般树 GMM 的 site-pattern 概率定义（`Phylo.Stat.JukesCantor` 目前只有
JC / 4 叶 / 固定拓扑）；(ii) 沿边**边缘化**（对隐状态求和）的显式公式；
(iii) 分裂两侧各自的 Markov 矩阵（转移矩阵乘积）构造。
这是「一般模型层」的欠账，也是 I5/I6（不变量理想）的前置。 -/
def TreeMarkovFactorGap (P : SiteFreq (Fin 4)) : Prop :=
  ∀ (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ),
    (∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)) → (flatAB P).rank ≤ 4

/-- 缺口陈述的**代数半边确实成立**（由 `rank_flatAB_le_four_of_factor`）；
未证的是「树模型 ⟹ 存在这样的 `A, B`」。 -/
theorem treeMarkovFactorGap_holds (P : SiteFreq (Fin 4)) : TreeMarkovFactorGap P :=
  fun A B h => rank_flatAB_le_four_of_factor P A B h

end Phylo.Stat.InvariantsRank

/-! ## 公理审计 -/

#print axioms Phylo.Stat.InvariantsRank.rank_minor_eq_zero_of_rank_le
#print axioms Phylo.Stat.InvariantsRank.rank_flatAB_le_of_factor
#print axioms Phylo.Stat.InvariantsRank.rank_flatAB_le_four_iff_minor
#print axioms Phylo.Stat.InvariantsRank.invariantCount_fin_four
#print axioms Phylo.Stat.InvariantsRank.card_minorIndexPairs
