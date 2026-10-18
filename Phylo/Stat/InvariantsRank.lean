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
5. ★★★ **模型半边（W25b）**：`gmmFreq`（4 叶 GMM，文献式 (1)）**无条件**可因子分解
   （`gmmFreq_factorizable`）⟹ `rank ≤ 4`（`rank_flatAB_le_four_of_treeModel`）⟹ 五阶子式为零
   （`minor_eq_zero_of_treeModel`）。缺口 `TreeMarkovFactorGap` 由此**证成**
   （`treeMarkovFactorGap_holds`）。

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
| `gmmFreq` | ★★★ 4 叶 GMM 的 site-pattern 概率（文献式 (1)，384–407 行） |
| `IsTreeModelFreq` | ★★ 「`P` 落在 4 叶 GMM 参数像里」的谓词 |
| `gmmFreq_factorizable` | ★★★ **模型半边**：4 叶 GMM ⟹ 中间维数 `4` 的因子分解（无假设） |
| `rank_flatAB_le_four_of_treeModel` | ★★★ 4 叶 GMM ⟹ 展平秩 `≤ 4`（无假设） |
| `minor_eq_zero_of_treeModel` | ★★★ 4 叶 GMM ⟹ 所有 `5×5` 子式为零（无假设） |
| `isTreeModelFreq_zero` | ★ 非空真：零张量是 4 叶 GMM 频率 |
| `deltaFreq` / `flatAB_deltaFreq` | ★ 阴性对照用的单位张量（展平 = 单位阵，秩 `16`） |
| `not_isTreeModelFreq_deltaFreq` | ★★ **阴性对照**：`deltaFreq` **不**是 GMM 频率（秩 `16 > 4`） |
| `TreeMarkovFactorGap` | **缺口**（W25b 改强为模型半边）：4 叶 GMM ⟹ 因子分解 |
| `treeMarkovFactorGap_holds` | ★★★ 该缺口命题的**无假设证明**（证成） |
| `treeMarkovFactorGap_rank_le_four` | ★★ 旧形态结论保留：`IsTreeModelFreq P ⟹ rank ≤ 4` |

## 诚实边界（**纪律 12**）

* **已做（W25b 泳道 b）**：**4 叶 GMM ⟹ 可因子分解 ⟹ 秩 ≤ 4 ⟹ 五阶子式为零** 这条链
  在 `gmmFreq`（文献 384–407 行式 (1) 的 4 叶显式形式）上**无假设**证通：
  `gmmFreq_factorizable`、`rank_flatAB_le_four_of_treeModel`、`minor_eq_zero_of_treeModel`。
  缺口 `TreeMarkovFactorGap` 原先只登记**已证的代数半边**（空转），现按本文件旧 docstring
  自己写明的「未证前提」**改强**为真正的模型半边，并由 `treeMarkovFactorGap_holds`
  **无假设证成**（四要素见 §4.1 的 docstring）。
* **未做（剩余边界）**：`n` 叶**一般树**（任意拓扑、任意 `n`、`κ^k × κ^{n−k}` 展平）的同一结论。
  仍缺三件器材：(i) 一般树 GMM 的 site-pattern 概率定义（`Phylo.JukesCantor.patternProb`
  只有 JC / 4 叶 / 固定拓扑）；(ii) 沿边边缘化的**任意树**版本（式 (1) 的 `H` 求和）；
  (iii) 分裂两侧转移矩阵乘积的构造。本文件的 `gmmFreq` 还允许**非随机**矩阵
  （因子分解与秩是纯代数事实），故**未**形式化「`π` 非负且和为 `1`、`Kᵢ` 行和为 `1`」
  的概率解释；`Phylo.JukesCantor.patternProb` = `gmmFreq (fun _ => 1/4) (kernel (t 0)) … (kernel (t 4))`
  这一 JC 特化是逐项对应（`π = 1/4`），本文件未跨层 import 以保持依赖面不变。
* **未做**：Allman–Rhodes **Theorem 4 / Theorem 11**（`Fedge(T)` **生成**整个不变量理想：
  含「素数性」「理想生成」两层，且 `κ > 2` 还需顶点展平）。本文件只证
  「这些子式是**不变量**（必然为零）」，**不**声称它们是理想生成元。
* **已做（W25b 阴性对照）**：`not_isTreeModelFreq_deltaFreq` —— 单位张量（展平满秩 `16`）
  **不**是 4 叶 GMM 频率，故「4 叶 GMM ⟹ 秩 ≤ 4」是真限制；`deltaFreq` 也是
  `Phylo.Stat.EdgeInvariants.edgeMinor_witness_eval_eq_one` 用的同一个张量。
* **未做（更强的阴性对照）**：本文件**没有**给出「无因子分解时存在非零 `5×5` 子式」的
  显式构造（即「子式能区分拓扑」的构造性版本）。理由是构造需要手工枚举 `Fin 5 → Fin 4 × Fin 4` 的置换型指标
  （在本次实现中该枚举的 `decide`/`simp` 化简开销与出错率都很高），
  故按协调侧建议删去。**因此本文件不声称**「五阶子式能区分拓扑」这一般性结论 ——
  库内 `SVDQuartets.sepFreq_flatAC_rank`（`flatAC (sepFreq c)` 满秩 `κ²`，DNA 即 `16`）
  可作为该方向的**间接**旁证（满秩矩阵的 `5×5` 子式不可能全为零），但它是在
  `SVDQuartets.lean` 里证的，本文件只**引用**、未复述。
* **未做**：`κ^k` 大小的展平（本文件只做 `k = 2`，即 4 分类群、`κ² × κ²` 展平）。
* **未做**：五阶子式**唯一决定**拓扑（需要一般参数下的「另一拓扑存在非零子式」定理）。
* 无 `sorry`、无 `axiom`；公理审计见文件末尾（`#print axioms` 命令已移出文件以免破
  「零 stdout」的单文件门，实测结果记在那里）。
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
  ring_nf

/-! ## 4. ★★★ 模型半边：4 叶一般 Markov 模型（GMM）的频率**确实**可因子分解

本节是 W25 泳道 b 对缺口 `TreeMarkovFactorGap` 的判定：**证成**（旧形态空转，已改强为真缺口）。

文献（Allman–Rhodes 2006，库内文本行号）：

* **346–351 行**：GMM 的参数 = 根分布 `π_r` ＋ 每条边的 `κ × κ` Markov（转移）矩阵 `M_e`；
* **384–407 行（式 (1)）**：`φ^r(s) = P`，
  `P(i₁,…,iₙ) = Σ_{(b_v) ∈ H} π_r(b_r) · ∏_e M_e(b_{s(e)}, b_{f(e)})`
  —— 对**全部内部顶点状态（histories）求和**，这就是沿边**边缘化**；
* **704–712 行**：沿边 `e` 的展平 `F^late(P)`（`κ^k × κ^{n−k}`）；
* **714–725 行 + Fig. 2（758 行）**：展平 = 「1 个 `κ` 状态隐变量 + 2 个观测量」的**粗化图模型**；
* **760–768 行**：`F^late(P) = M₁ᵀ diag(π_r) M₂`（`M₁ : κ × κ^k`、`M₂ : κ × κ^{n−k}`）
  ⟹ `rank F^late(P) ≤ κ`；**770 行**：故所有 `(κ+1) × (κ+1)` 子式为零。
-/

/-- ★★★ **4 叶 GMM 的 site-pattern 概率**（拓扑 `12|34`，根取在左侧内部顶点 `a`）。

文献式 (1)（384–407 行）在 4 叶二元树上的显式形式：两个内部顶点 `a`、`b` 的状态被
**求和（边缘化）**掉，`b` 是内部边 `a—b` 的右端点：

`gmmFreq π K₁ K₂ K₃ K₄ K₅ i j k l = ∑_a ∑_b π a · K₁ a i · K₂ a j · K₃ a b · K₄ b k · K₅ b l`

（`K₁ : a→1`、`K₂ : a→2`、`K₃ : a—b`、`K₄ : b→3`、`K₅ : b→4`，共 5 条边。）

⚠️ 这里**不**要求 `π` 非负 / 和为 `1`、**不**要求 `Kᵢ` 随机（行和为 `1`）：下面要证的因子分解
与秩上界是**纯代数**结论，对任意实参数成立（故 JC 等特化自动覆盖）。 -/
def gmmFreq (π : Fin 4 → ℝ) (K₁ K₂ K₃ K₄ K₅ : Matrix (Fin 4) (Fin 4) ℝ) : SiteFreq (Fin 4) :=
  fun i j k l =>
    ∑ a : Fin 4, ∑ b : Fin 4,
      π a * K₁ a i * K₂ a j * K₃ a b * K₄ b k * K₅ b l

/-- **`P` 落在 4 叶 GMM 的参数像 `φ^r(S)` 里**（文献 375–383 行：`φ^r : S → [0,1]^L`）。

本文件只到**模型层**为止：`IsTreeModelFreq` 说的是「存在一组参数使 `P` 等于 `gmmFreq`」，
它**不**声称 `P` 每一项非负、总和为 `1` —— 那些是概率解释，与不变量无关。 -/
def IsTreeModelFreq (P : SiteFreq (Fin 4)) : Prop :=
  ∃ (π : Fin 4 → ℝ) (K₁ K₂ K₃ K₄ K₅ : Matrix (Fin 4) (Fin 4) ℝ),
    P = gmmFreq π K₁ K₂ K₃ K₄ K₅

/-- ★★★ **模型半边（无假设）**：任何 4 叶 GMM 频率都有**中间维数 `4`** 的因子分解。

中间维数取内部边右端点 `b` 的状态（就是 `M₁ᵀ diag(π_r) M₂` 里那个 `κ` 维**桥**，文献 760–768 行）：

* `A (i,j) m = ∑_a π a · K₁ a i · K₂ a j · K₃ a m`（左子树 `12` 两叶 ＋ 桥的左半边）；
* `B m (k,l) = K₄ m k · K₅ m l`（桥的右半边 ＋ 右子树 `34` 两叶）。

剩下来的只是「对 `a`、对 `b` 的两重求和换序 ＋ 乘积结合」。 -/
theorem gmmFreq_factorizable (π : Fin 4 → ℝ) (K₁ K₂ K₃ K₄ K₅ : Matrix (Fin 4) (Fin 4) ℝ) :
    ∃ (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ),
      ∀ i j k l, gmmFreq π K₁ K₂ K₃ K₄ K₅ i j k l = ∑ m, A (i, j) m * B m (k, l) := by
  refine ⟨fun p m => ∑ a : Fin 4, π a * K₁ a p.1 * K₂ a p.2 * K₃ a m,
    fun m q => K₄ m q.1 * K₅ m q.2, ?_⟩
  intro i j k l
  simp only [gmmFreq]
  calc ∑ a : Fin 4, ∑ b : Fin 4, π a * K₁ a i * K₂ a j * K₃ a b * K₄ b k * K₅ b l
      = ∑ a : Fin 4, ∑ m : Fin 4,
          (π a * K₁ a i * K₂ a j * K₃ a m) * (K₄ m k * K₅ m l) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun m _ => by ring))
    _ = ∑ m : Fin 4, ∑ a : Fin 4,
          (π a * K₁ a i * K₂ a j * K₃ a m) * (K₄ m k * K₅ m l) := Finset.sum_comm
    _ = ∑ m : Fin 4, (∑ a : Fin 4, π a * K₁ a i * K₂ a j * K₃ a m) * (K₄ m k * K₅ m l) := by
        simp only [Finset.sum_mul]

/-- ★★★ **模型半边（合成形式）**：`P` 来自 4 叶 GMM ⟹ `P` 可因子分解。 -/
theorem isTreeModelFreq_factorizable (P : SiteFreq (Fin 4)) (hP : IsTreeModelFreq P) :
    ∃ (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ),
      ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l) := by
  obtain ⟨π, K₁, K₂, K₃, K₄, K₅, rfl⟩ := hP
  exact gmmFreq_factorizable π K₁ K₂ K₃ K₄ K₅

/-- ★★★ **4 叶 GMM 的展平秩 ≤ 4**（文献 760–768 行的 `rank F^late(P) ≤ κ`；**无假设**）。 -/
theorem rank_flatAB_le_four_of_treeModel (P : SiteFreq (Fin 4)) (hP : IsTreeModelFreq P) :
    (flatAB P).rank ≤ 4 := by
  obtain ⟨A, B, hAB⟩ := isTreeModelFreq_factorizable P hP
  exact rank_flatAB_le_four_of_factor P A B hAB

/-- ★★★ **4 叶 GMM 上所有 `5 × 5` 子式为零**（文献 770 行「all `(κ+1)×(κ+1)` minors must vanish」）。

注意这是**无假设**的：不再像 §3 那样把「因子分解」当假设传进来（那正是旧缺口的空转之处）。 -/
theorem minor_eq_zero_of_treeModel (P : SiteFreq (Fin 4)) (hP : IsTreeModelFreq P)
    (r c : Fin 5 → Fin 4 × Fin 4) : ((flatAB P).submatrix r c).det = 0 :=
  rank_minor_eq_zero_of_rank_le (flatAB P) (rank_flatAB_le_four_of_treeModel P hP) r c

/-- **非空真（anti-vacuity）**：零张量是 4 叶 GMM 频率（取 `π = 0`），故 `IsTreeModelFreq` 非空、
上面三条定理**不是**空条件。 -/
theorem isTreeModelFreq_zero : IsTreeModelFreq (fun _ _ _ _ => (0 : ℝ)) :=
  ⟨0, 0, 0, 0, 0, 0, by funext i j k l; simp [gmmFreq]⟩

/-! ### 4.0.1 阴性对照：模型类是**真**子类 -/

/-- **阴性对照用的单位张量**：展平 `flatAB = 1`（满秩 `16`）。
与 `Phylo.Stat.EdgeInvariants.identFreq` 是同一个张量；本文件自带一份以免跨层 import。 -/
def deltaFreq : SiteFreq (Fin 4) := fun i j k l => if (i, j) = (k, l) then (1 : ℝ) else 0

/-- `deltaFreq` 的展平**就是单位阵**。 -/
theorem flatAB_deltaFreq : flatAB deltaFreq = 1 := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  rw [flatAB, deltaFreq, Matrix.one_apply]

/-- `deltaFreq` 的展平秩是 `16`（`κ² = 4²` 满秩）。 -/
theorem rank_flatAB_deltaFreq : (flatAB deltaFreq).rank = 16 := by
  rw [flatAB_deltaFreq, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin]

/-- ★★ **阴性对照（模型的假设有真内容）**：`deltaFreq` **不**是 4 叶 GMM 频率 ——
它的展平满秩 `16`，而 `rank_flatAB_le_four_of_treeModel` 说任何 GMM 频率的秩 `≤ 4`。

这是「非空真」的**强形式**：`IsTreeModelFreq` 既**非空**（`isTreeModelFreq_zero`），
又**不**包含一切张量 —— 故 `treeMarkovFactorGap_holds` 不是在证「∅ 上的空真命题」。 -/
theorem not_isTreeModelFreq_deltaFreq : ¬ IsTreeModelFreq deltaFreq := by
  intro h
  have h4 := rank_flatAB_le_four_of_treeModel deltaFreq h
  rw [rank_flatAB_deltaFreq] at h4
  omega

/-! ### 4.1 缺口 `TreeMarkovFactorGap` 的判定（证成） -/

/-- **`TreeMarkovFactorGap P`（W25b 改强后的形态）：`P` 来自 4 叶 Markov 模型 ⟹ `P` 可因子分解。**

**四要素（改命题必留）**：

* **旧形态**（`ba73f34` 起）：
  `∀ A B, (∀ i j k l, P i j k l = ∑ m, A (i,j) m * B m (k,l)) → (flatAB P).rank ≤ 4`；
* **新形态**：
  `IsTreeModelFreq P → ∃ A B, ∀ i j k l, P i j k l = ∑ m, A (i,j) m * B m (k,l)`；
* **文献**：Allman–Rhodes 2006 **346–351 / 384–407 行**（GMM 与式 (1)：对 histories 求和
  = 边缘化）、**714–725 行**（展平 = 粗化图模型）、**760–768 行**（`F^late(P) = M₁ᵀ diag(π_r) M₂`）；
* **理由**：旧形态是 §2 的 `rank_flatAB_le_four_of_factor` 的**逐字重述**，`ba73f34` 当天就由
  下面同名的 `treeMarkovFactorGap_holds` 证掉了 —— 它把**已证的代数半边**登记成「缺口」，
  于是缺口**空转**（`def` 里没有任何模型内容）。本文件旧 docstring 自己写明的
  「未证的是它的前提：`P` 来自某棵 4 叶树上的（一般）Markov 模型 ⟹ 存在这样的 `A, B`」
  才是真缺口；新形态把它写成**可证伪的命题**，并在本节**无假设地证成**
  （`treeMarkovFactorGap_holds`）。
  旧形态的**结论没有被削弱**：它仍是 §2 的定理，并作为新形态的推论保留为
  `treeMarkovFactorGap_rank_le_four` / `minor_eq_zero_of_treeModel`。

**遗留边界**：本形态只覆盖 **4 叶、拓扑 `12|34`、`κ = 4`**（与全文件边界一致）。
（4 叶二叉树只差叶标号重排，故 `12|34` 即全部 4 叶拓扑；**根的选取**不影响叶上联合分布
—— GMM 的 rerooting 恒等式，本文按标准理解使用、**未**在此形式化。）
`n` 叶一般树（文献 704–712 行的 `κ^k × κ^{n−k}` 展平）仍在外，
见文件头「诚实边界」。 -/
def TreeMarkovFactorGap (P : SiteFreq (Fin 4)) : Prop :=
  IsTreeModelFreq P →
    ∃ (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ),
      ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)

/-- ★★★ **缺口已证成（无假设、零 `sorry`、零 `axiom`）**：`TreeMarkovFactorGap` 是定理。

（`#print axioms` ⇒ `[propext, Classical.choice, Quot.sound]`，见文件头「公理审计」。） -/
theorem treeMarkovFactorGap_holds (P : SiteFreq (Fin 4)) : TreeMarkovFactorGap P :=
  isTreeModelFreq_factorizable P

/-- **旧形态的结论保留为推论**：`TreeMarkovFactorGap` ＋ §2 的代数半边 ⟹ 展平秩 `≤ 4`。 -/
theorem treeMarkovFactorGap_rank_le_four (P : SiteFreq (Fin 4)) (hP : IsTreeModelFreq P) :
    (flatAB P).rank ≤ 4 := by
  obtain ⟨A, B, hAB⟩ := treeMarkovFactorGap_holds P hP
  exact rank_flatAB_le_four_of_factor P A B hAB

end Phylo.Stat.InvariantsRank

/-! ## 公理审计

⚠️ `#print axioms` 的输出走 **stdout**，会破「零 warning / 零 stdout」的单文件门
（W25 的门判据是 `EXIT=0` **且** `STDOUT_BYTES=0`），故本文件**不保留** `#print axioms`
命令，实测结果记在这里（本文件全部定理都只剩三条标准公理）：

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

审计方式（不落在本文件里）：另建临时文件 `import Phylo.Stat.InvariantsRank` ＋
`#print axioms <名字>`，在镜像工作树里 `lake env lean` 跑一次。审计清单：

`rank_minor_eq_zero_of_rank_le`、`rank_flatAB_le_of_factor`、`rank_flatAB_le_four_iff_minor`、
`invariantCount_fin_four`、`card_minorIndexPairs`、`gmmFreq_factorizable`、
`isTreeModelFreq_factorizable`、`rank_flatAB_le_four_of_treeModel`、
`minor_eq_zero_of_treeModel`、`isTreeModelFreq_zero`、`flatAB_deltaFreq`、
`rank_flatAB_deltaFreq`、`not_isTreeModelFreq_deltaFreq`、`treeMarkovFactorGap_holds`、
`treeMarkovFactorGap_rank_le_four`。 -/
