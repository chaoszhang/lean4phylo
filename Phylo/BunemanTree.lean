/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split
import Phylo.Algorithm.NJ
import Phylo.Supertree
import Phylo.SplitsDetermineTree

/-!
# `Phylo.BunemanTree` —— Buneman 指数 `μ_σ(δ)` 与保留树 `B(δ)`（NEXT.md P0-D **F6**）

## 文献出处（逐条核对）

* **Buneman (1971)**, *The recovery of trees from measures of dissimilarity*, in
  *Mathematics in the Archaeological and Historical Sciences* (Hodson–Kendall–Tautu eds.),
  Edinburgh Univ. Press, pp. 387–395。
  * **p. 390**（`references/md/Buneman1971_RecoveryOfTreesFromDissimilarity.md` 第 212–214 行，
    并已对照扫描页 `references/img/Buneman1971_RecoveryOfTreesFromDissimilarity_p04.png` 逐字复核）：

    > `μ_σ = ½ min (d(A,C) + d(B,D) − d(A,B) − d(C,D))`，`for A, B in S⁰ and C, D in S¹`.

    注意：原文**不要求** `A, B`（或 `C, D`）互异 —— 它们遍历**整个** `S⁰`（乃至 `S¹`）。
    本文件的 `bunemanQuad` / `bunemanQuadruples` / `bunemanIndex` 忠实照搬这一点
    （这一点在 §5 的诚实边界里有实质后果）。
  * **p. 390, Lemma 8**（同上 md 第 215–217 行）：

    > 「If σ₁ and σ₂ are splits such that μ_{σ₁} > 0 and μ_{σ₂} > 0 then σ₁ and σ₂ are compatible.」

    = 本文件的 ★★★ `compatible_of_bunemanIndex_pos`。
  * **p. 390**（md 第 228–230 行）：`T_d = {σ : μ_σ > 0}` 是**树**（由 Lemma 8），
    且 `Δ_d = Σ_{σ∈T_d} μ_σ δ_σ` 是「保留」这些 split 的加性树度量。
    = 本文件的 ★★★ `exists_cladogram_displays_bunemanSplits`。
* **Bandelt & Dress (1986)**, *Reconstructing the shape of a tree from observed dissimilarity
  data*, Adv. Appl. Math. **7**, 309–343（`references/md/BandeltDress1986_ReconstructingShapeOfTree.md`）。
  该文以**关系**（neighbors relation）而非指数 `μ` 的形式处理同一件事：
  * **p. 311**（md 第 167–176 行）严格 neighbors relation
    `AB ‖ CD ⟺ d(A,B)+d(C,D) < d(A,C)+d(B,D)` 且 `< d(A,D)+d(B,C)`；
  * **p. 321 Proposition 3**（md 第 757–763 行）：对称 + 反对称的关系所关联的 cluster 系统**必是
    tree-like**；其证明（**p. 320**，md 第 706–708 行）就是下面 Lemma 8 的**四格论证**：
    `A ∈ Y∩Y'`、`B ∈ Y∩Ȳ'`、`C ∈ Ȳ∩Y'`、`D ∈ Ȳ∩Ȳ'` 会同时给出 `AB‖CD` 与 `AC‖BD`，与反对称矛盾；
  * **p. 325 Proposition 5**（md 第 1031–1048 行）：相异度的 neighbors relation 是 tree-like
    **⟺** 它传递。
  * ⚠️ **诚实提示**：BdD 1986 的 OCR 全文中**没有** `μ_σ`（grep `Buneman`/`positive` 均不命中），
    「Buneman 指数」的出处只有 Buneman 1971；BdD 1986 提供的是**同一论证的关系形式**与
    tree test（Prop 5）。本文件的核心证明与 BdD 1986 p. 320 的证明逐字同构。

## 内容

* `bunemanQuad` / `bunemanQuadruples` / `bunemanIndex`：指数定义（§1）；
* ★★ `bunemanIndex_pos_iff`：`μ_σ > 0` ⟺ **每个**四元组取值 `> 0`（定义级的刻画）；
* ★★ `bunemanIndex_le_quad` / `bunemanIndex_swap`：`inf'` 的上界性与两侧对换不变性（§2）；
* ★★★ `compatible_of_bunemanIndex_pos`：**Buneman 1971, Lemma 8**（§3，核心）；
* ★★★ `pairwiseCompatible_bunemanSplits` + `exists_cladogram_displays_bunemanSplits`：
  **保留树 `B(δ)` 存在**并定向展示 `{σ : 0 < μ_σ(δ)}`（§4，复用库内 Aho/supertree 件）；
* ★★ `iso_of_displays_bunemanSplits`：`B(δ)` 在同构意义下**唯一**（复用
  `Cladogram.iso_of_isSplitOf_iff`，即 §3.8「树由 split 系统决定」）；
* ★ `exists_neighbor_not_bunemanIndex_pos`：**诚实边界的显式反例**（§5）。

## 诚实边界

1. **「树度量 ⟹ 该 split 正指数」未形式化**。Buneman 1971 的另一半（`Δ_d ≤ d`、`T_d` 是 `d` 的
   「保留树」、`B(δ)` **恰好**只保留正指数 split）需要把 `δ` 与树上路径距离对齐；本库
   `Phylo.TreeDistance` 已有 `walkDist`/`dist`，但「树度量的四元组下界」尚未接上。
   故本文件给出的是：**正指数 ⟹ 相容 ⟹ 存在展示树**（`⟸` 方向）**+ 同构唯一性（条件形式）**。
2. **`iso_of_displays_bunemanSplits` 是条件形式**：假设存在两棵「展示的 split **恰好**等于
   `bunemanSplits δ`」的 cladogram。若 `δ` 有某个**平凡 split** 指数非正，则这样的树**不存在**
   （任何有 ≥2 片叶的树都展示全部平凡 split，见 `Cladogram.exists_isSplitOf_singleton`）。
   `exists_cladogram_displays_bunemanSplits` 只保证**展示全体**正指数 split（可能多展示一些）。
3. **`bunemanSplits δ` 含两个定向**（`s` 与 `s.swap`，`Phylo/Split.lean` 的 `Fin 2` 有序表示），
   与库内 `Cladogram.splits` 的约定一致；`Split.Compatible` 对换侧不变。
4. §5 的反例说明：原文（不要求互异）的 `μ_σ > 0` **严格强于** BdD 1986 p. 311 的严格
   neighbors relation —— 二者不可混用。
-/

universe u

namespace NJ
namespace Dissimilarity

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. Buneman 指数 `μ_σ(δ)` -/

/-- **四元组取值** `δ(A,C) + δ(B,D) − δ(A,B) − δ(C,D)`（Buneman 1971, p. 390 被取 `min` 的量）。

`q = ((A,B),(C,D))`：第一对 `(A,B)` 落在 `S⁰_σ`、第二对 `(C,D)` 落在 `S¹_σ`
（由 `bunemanQuadruples` 施加这一约束）。 -/
def bunemanQuad (δ : Dissimilarity X) (q : (X × X) × (X × X)) : ℝ :=
  δ.val q.1.1 q.2.1 + δ.val q.1.2 q.2.2 - δ.val q.1.1 q.1.2 - δ.val q.2.1 q.2.2

/-- **取 `min` 的有限集**：`(S⁰ × S⁰) × (S¹ × S¹)`。

原文 p. 390：「`for A, B in S⁰ and C, D in S¹`」—— `A, B` 遍历**整个** `S⁰`（可相等），
`C, D` 遍历**整个** `S¹`（可相等）。 -/
def bunemanQuadruples (s : Split X) : Finset ((X × X) × (X × X)) :=
  (s.sideA ×ˢ s.sideA) ×ˢ (s.sideB ×ˢ s.sideB)

/-- `bunemanQuadruples s` 非空（`Split` 的两侧都非空 —— `KPartition.nonempty`）。 -/
theorem bunemanQuadruples_nonempty (s : Split X) : (bunemanQuadruples s).Nonempty :=
  ((s.nonempty 0).product (s.nonempty 0)).product ((s.nonempty 1).product (s.nonempty 1))

/-- ★★★ **Buneman 指数**（Buneman 1971, p. 390）：

`μ_σ(δ) = ½ · min_{A, B ∈ S⁰_σ, C, D ∈ S¹_σ} (δ(A,C) + δ(B,D) − δ(A,B) − δ(C,D))`。 -/
noncomputable def bunemanIndex (δ : Dissimilarity X) (s : Split X) : ℝ :=
  (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ) / 2

/-- 定义展开（`rfl`）：指数即「四元组取值的下确界除以 2」。 -/
theorem bunemanIndex_def (δ : Dissimilarity X) (s : Split X) :
    bunemanIndex δ s
      = (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ) / 2 :=
  rfl

/-- ★★ **正指数的判据**：`0 < μ_σ(δ)` ⟺ **每个**四元组的取值都 `> 0`。

这把「指数 > 0」这个关于 `inf'` 的陈述化为逐四元组的严格不等式 —— 下面是 Lemma 8 的入口。 -/
theorem bunemanIndex_pos_iff (δ : Dissimilarity X) (s : Split X) :
    0 < bunemanIndex δ s ↔ ∀ q ∈ bunemanQuadruples s, 0 < bunemanQuad δ q := by
  have key : (0 : ℝ) < (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ)
      ↔ ∀ q ∈ bunemanQuadruples s, 0 < bunemanQuad δ q :=
    Finset.lt_inf'_iff (H := bunemanQuadruples_nonempty s) (f := bunemanQuad δ)
  rw [bunemanIndex_def]
  constructor
  · intro h
    exact key.mp (by linarith)
  · intro h
    have h' := key.mpr h
    linarith

/-- ★★ **任一四元组给出指数的上界**：`μ_σ(δ) ≤ (δ(A,C)+δ(B,D)−δ(A,B)−δ(C,D))/2`。 -/
theorem bunemanIndex_le_quad (δ : Dissimilarity X) (s : Split X)
    {q : (X × X) × (X × X)} (hq : q ∈ bunemanQuadruples s) :
    bunemanIndex δ s ≤ bunemanQuad δ q / 2 := by
  have h : (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ)
      ≤ bunemanQuad δ q := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt := (Finset.lt_inf'_iff (H := bunemanQuadruples_nonempty s)
      (f := bunemanQuad δ)).mp hcon
    exact absurd (hlt q hq) (lt_irrefl _)
  rw [bunemanIndex_def]
  linarith

/-! ## 2. 两侧对换不变性（`Split` 是有序表示，指数必须商掉它） -/

/-- 两侧对换：`((A,B),(C,D)) ↦ ((C,D),(A,B))`。 -/
def swapQuad (q : (X × X) × (X × X)) : (X × X) × (X × X) :=
  ((q.2.1, q.2.2), (q.1.1, q.1.2))

omit [Fintype X] [DecidableEq X] in
/-- 四元组取值在两侧对换下不变（对称性 + 加法交换）。 -/
theorem bunemanQuad_swapQuad (δ : Dissimilarity X) (q : (X × X) × (X × X)) :
    bunemanQuad δ (swapQuad q) = bunemanQuad δ q := by
  simp only [bunemanQuad, swapQuad]
  rw [δ.symm q.2.1 q.1.1, δ.symm q.2.2 q.1.2]
  ring

omit [Fintype X] [DecidableEq X] in
/-- `swapQuad` 是对合。 -/
theorem swapQuad_swapQuad (q : (X × X) × (X × X)) : swapQuad (swapQuad q) = q := rfl

/-- `s.swap` 的四元组集恰是 `s` 的四元组集在 `swapQuad` 下的像。 -/
theorem mem_bunemanQuadruples_swap (s : Split X) (q : (X × X) × (X × X)) :
    q ∈ bunemanQuadruples s.swap ↔ swapQuad q ∈ bunemanQuadruples s := by
  simp only [bunemanQuadruples, Finset.mem_product, swapQuad, Split.swap_sideA, Split.swap_sideB]
  tauto

/-- `mem_bunemanQuadruples_swap` 的常用变体（用 `swapQuad` 的对合性把两侧对齐）。 -/
theorem swapQuad_mem_bunemanQuadruples_swap (s : Split X) (q : (X × X) × (X × X)) :
    swapQuad q ∈ bunemanQuadruples s.swap ↔ q ∈ bunemanQuadruples s := by
  rw [mem_bunemanQuadruples_swap s (swapQuad q), swapQuad_swapQuad]

/-- ★★ **指数对两侧对换不变**：`μ_{σ.swap}(δ) = μ_σ(δ)`。

（`Split` 用 `Fin 2` 索引把两侧**有序化**，故这条是「无序 split」良定义性的必要件。） -/
theorem bunemanIndex_swap (δ : Dissimilarity X) (s : Split X) :
    bunemanIndex δ s.swap = bunemanIndex δ s := by
  have hle : (bunemanQuadruples s.swap).inf' (bunemanQuadruples_nonempty s.swap)
        (bunemanQuad δ)
      ≤ (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ) := by
    refine (Finset.le_inf'_iff (bunemanQuadruples_nonempty s) (bunemanQuad δ)).mpr ?_
    intro q hq
    by_contra hcon
    rw [not_le] at hcon
    have hlt := (Finset.lt_inf'_iff (H := bunemanQuadruples_nonempty s.swap)
      (f := bunemanQuad δ)).mp hcon
    have h2 := hlt (swapQuad q) ((swapQuad_mem_bunemanQuadruples_swap s q).mpr hq)
    rw [bunemanQuad_swapQuad] at h2
    exact absurd h2 (lt_irrefl _)
  have hge : (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ)
      ≤ (bunemanQuadruples s.swap).inf' (bunemanQuadruples_nonempty s.swap) (bunemanQuad δ) := by
    refine (Finset.le_inf'_iff (bunemanQuadruples_nonempty s.swap) (bunemanQuad δ)).mpr ?_
    intro q hq
    by_contra hcon
    rw [not_le] at hcon
    have hlt := (Finset.lt_inf'_iff (H := bunemanQuadruples_nonempty s)
      (f := bunemanQuad δ)).mp hcon
    have h2 := hlt (swapQuad q) ((mem_bunemanQuadruples_swap s q).mp hq)
    rw [bunemanQuad_swapQuad] at h2
    exact absurd h2 (lt_irrefl _)
  have heq : (bunemanQuadruples s.swap).inf' (bunemanQuadruples_nonempty s.swap) (bunemanQuad δ)
      = (bunemanQuadruples s).inf' (bunemanQuadruples_nonempty s) (bunemanQuad δ) :=
    le_antisymm hle hge
  rw [bunemanIndex_def, bunemanIndex_def, heq]

/-! ## 3. ★★★ Buneman 1971, Lemma 8：正指数 split 两两相容 -/

/-- ★★★ **Buneman 1971, Lemma 8**（p. 390）：`μ_σ(δ) > 0` 且 `μ_τ(δ) > 0` ⟹ `σ, τ` 相容。

**证明**（原文的四格论证；BdD 1986 p. 320 为同一论证的关系形式）：
反设 `σ, τ` 不相容，则四个交 `S⁰_σ∩S⁰_τ`、`S⁰_σ∩S¹_τ`、`S¹_σ∩S⁰_τ`、`S¹_σ∩S¹_τ` 全非空；
取 `A`、`C` 在前者/次者、`B`、`D` 在第三者/末者。于是
`τ` 分离 `{A,B}` 与 `{C,D}`、`σ` 分离 `{A,C}` 与 `{B,D}`。
`μ_τ > 0` 在四元组 `((A,B),(C,D))` 上给出 `δ(A,C)+δ(B,D) − δ(A,B)−δ(C,D) > 0`，
`μ_σ > 0` 在四元组 `((A,C),(B,D))` 上给出同式的相反严格不等式 —— 矛盾。 -/
theorem compatible_of_bunemanIndex_pos (δ : Dissimilarity X) {s t : Split X}
    (hs : 0 < bunemanIndex δ s) (ht : 0 < bunemanIndex δ t) : Split.Compatible s t := by
  by_contra h
  have h1 : ∃ A : X, A ∈ s.sideA ∧ A ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inl hd)
  have h2 : ∃ C : X, C ∈ s.sideA ∧ C ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inl hd))
  have h3 : ∃ B : X, B ∈ s.sideB ∧ B ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inl hd)))
  have h4 : ∃ D : X, D ∈ s.sideB ∧ D ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inr hd)))
  obtain ⟨A, hAs, hAt⟩ := h1
  obtain ⟨C, hCs, hCt⟩ := h2
  obtain ⟨B, hBs, hBt⟩ := h3
  obtain ⟨D, hDs, hDt⟩ := h4
  have hs' := (bunemanIndex_pos_iff δ s).mp hs
  have ht' := (bunemanIndex_pos_iff δ t).mp ht
  have hqs : ((A, C), (B, D)) ∈ bunemanQuadruples s := by
    simp only [bunemanQuadruples, Finset.mem_product]
    exact ⟨⟨hAs, hCs⟩, ⟨hBs, hDs⟩⟩
  have hqt : ((A, B), (C, D)) ∈ bunemanQuadruples t := by
    simp only [bunemanQuadruples, Finset.mem_product]
    exact ⟨⟨hAt, hBt⟩, ⟨hCt, hDt⟩⟩
  have h1 := hs' ((A, C), (B, D)) hqs
  have h2 := ht' ((A, B), (C, D)) hqt
  simp only [bunemanQuad] at h1 h2
  linarith

/-- ★★ **Lemma 8 的族形式**：若 `fam` 中每个 split 都正指数，则 `fam` 两两相容。 -/
theorem pairwiseCompatible_of_bunemanIndex_pos (δ : Dissimilarity X) {fam : Finset (Split X)}
    (h : ∀ s ∈ fam, 0 < bunemanIndex δ s) : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t :=
  fun s hs t ht => compatible_of_bunemanIndex_pos δ (h s hs) (h t ht)

/-! ## 4. ★★★ 保留树 `B(δ)` -/

/-- **保留树 `B(δ)` 的 split 集**：`{σ : 0 < μ_σ(δ)}`（Buneman 1971, p. 390 的 `T_d`）。 -/
noncomputable def bunemanSplits (δ : Dissimilarity X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s => 0 < bunemanIndex δ s

/-- `B(δ)` 的成员判据。 -/
theorem mem_bunemanSplits {δ : Dissimilarity X} {s : Split X} :
    s ∈ bunemanSplits δ ↔ 0 < bunemanIndex δ s := by
  classical
  simp [bunemanSplits]

/-- ★★★ **`B(δ)` 的 split 集两两相容**（Lemma 8 的族形式）。 -/
theorem pairwiseCompatible_bunemanSplits (δ : Dissimilarity X) :
    ∀ s ∈ bunemanSplits δ, ∀ t ∈ bunemanSplits δ, Split.Compatible s t :=
  pairwiseCompatible_of_bunemanIndex_pos δ fun _ hs => mem_bunemanSplits.mp hs

/-- ★ **`B(δ)` 对两侧对换封闭**（无序 split 良定义性的推论）。 -/
theorem swap_mem_bunemanSplits {δ : Dissimilarity X} {s : Split X}
    (h : s ∈ bunemanSplits δ) : s.swap ∈ bunemanSplits δ := by
  rw [mem_bunemanSplits] at h ⊢
  rwa [bunemanIndex_swap]

/-- ★★★ **保留树 `B(δ)` 存在**：正指数 split 集两两相容，故被某棵 cladogram **定向展示**全体。

（Buneman 1971, p. 390：「From `d` we can derive `T_d = {σ : μ_σ > 0}` and lemma 8 ensures that
`T_d` is a tree.」—— 此处「是树」由库内 Aho–Buneman 收口件
`supertree_displays_of_pairwiseCompatible` 实现，无需重复造轮子。）

⚠️ 结论只保证**展示全体**正指数 split（`M` 可能多展示一些 split）。 -/
theorem exists_cladogram_displays_bunemanSplits (δ : Dissimilarity X) (ρ : X)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s ∈ bunemanSplits δ, M.IsSplitOf s :=
  supertree_displays_of_pairwiseCompatible (bunemanSplits δ) ρ
    (pairwiseCompatible_bunemanSplits δ) h3

/-- ★★ **`B(δ)` 在同构意义下唯一**（刻画方向）：

若两棵 cladogram 展示的 split **恰好**是 `bunemanSplits δ`，则它们同构
（这是 §3.8「树由 split 系统决定」`Cladogram.iso_of_isSplitOf_iff` 的直接推论）。

⚠️ **条件形式**：本文件**没有**证明「展示恰为 `bunemanSplits δ` 的树存在」——
若 `δ` 的某个平凡 split 指数非正，这样的树不存在（任何 ≥2 片叶的树都展示全部平凡 split）。 -/
theorem iso_of_displays_bunemanSplits {δ : Dissimilarity X} {M M' : Cladogram.{u, u} X}
    (h3 : 3 ≤ Fintype.card X)
    (hM : ∀ s : Split X, M.IsSplitOf s ↔ s ∈ bunemanSplits δ)
    (hM' : ∀ s : Split X, M'.IsSplitOf s ↔ s ∈ bunemanSplits δ) :
    Nonempty (Iso M M') :=
  Cladogram.iso_of_isSplitOf_iff h3 fun s => (hM s).trans (hM' s).symm

/-! ## 5. ★ 诚实边界：`μ_σ > 0` 严格强于 BdD 1986 的严格 neighbors relation

原文 p. 390 的 `min` 中 `A, B` **可以取同一个点**（`S⁰` 中任选两个元素，不要求互异）。
于是 `μ_σ > 0` 还要求所有「退化」四元组严格为正，例如 `A = B` 时：

`δ(A,C) + δ(A,D) − δ(A,A) − δ(C,D) = δ(A,C) + δ(A,D) − δ(C,D) > 0`。

而 BdD 1986 p. 311 的严格 neighbors relation 只涉及**四个互异点**。
下面的显式 `Fin 4` 反例说明两者**不可混用**：
`w=0, x=1, y=2, z=3`，`δ(w,x)=δ(w,y)=δ(w,z)=1`、`δ(y,z)=2`、`δ(x,y)=δ(x,z)=3`；
取 `σ = {0,1} | {2,3}` 时严格 neighbors relation 成立
（`1+2 = 3 < 1+3 = 4` 与 `3 < 3+1 = 4`），但 `δ(0,2)+δ(0,3) = 2 = δ(2,3)` 使退化四元组取值为 `0`，
故 `μ_σ ≤ 0`。 -/

/-- 反例的值函数（`Fin 4`，见本节 docstring 的数值表）。 -/
def neighborVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 1 | 1, 0 => 1
  | 0, 2 => 1 | 2, 0 => 1
  | 0, 3 => 1 | 3, 0 => 1
  | 2, 3 => 2 | 3, 2 => 2
  | _, _ => 3

/-- 反例的相异度 `δ`。 -/
def neighborDissim : Dissimilarity (Fin 4) where
  val := neighborVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- `Fin 4` 上的显式 split `{0,1} | {2,3}`（反例用）。 -/
def pairSplit : Split (Fin 4) where
  parts i := if i = 0 then ({0, 1} : Finset (Fin 4)) else {2, 3}
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · decide
    · decide
    · exact absurd rfl hij
  union_eq_univ := by
    ext x
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    fin_cases x
    · exact Finset.mem_biUnion.mpr ⟨0, by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨0, by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simp⟩
  nonempty := by
    intro i
    fin_cases i
    · exact ⟨0, by simp⟩
    · exact ⟨2, by simp⟩

omit [Fintype X] [DecidableEq X] in
theorem pairSplit_sideA : pairSplit.sideA = ({0, 1} : Finset (Fin 4)) := rfl

omit [Fintype X] [DecidableEq X] in
theorem pairSplit_sideB : pairSplit.sideB = ({2, 3} : Finset (Fin 4)) := by
  decide

omit [Fintype X] [DecidableEq X] in
/-- 反例中 `μ_σ ≤ 0`：退化四元组 `((0,0),(2,3))` 的取值为 `0`。 -/
theorem not_bunemanIndex_pos_neighbor : ¬ 0 < bunemanIndex neighborDissim pairSplit := by
  have hmem : ((0, 0), (2, 3)) ∈ bunemanQuadruples pairSplit := by
    simp only [bunemanQuadruples, Finset.mem_product, pairSplit, Split.sideA, Split.sideB]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp
  have hle := bunemanIndex_le_quad neighborDissim pairSplit hmem
  have hval : bunemanQuad neighborDissim ((0, 0), (2, 3)) = 0 := by
    simp only [bunemanQuad, neighborDissim, neighborVal]
    norm_num
  rw [hval] at hle
  intro h
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★ **诚实边界（显式反例）**：原文（不要求互异）的 `μ_σ > 0` **严格强于** BdD 1986 p. 311 的
严格 neighbors relation。 -/
theorem exists_neighbor_not_bunemanIndex_pos :
    ∃ (δ : Dissimilarity (Fin 4)) (s : Split (Fin 4)),
      s.sideA = ({0, 1} : Finset (Fin 4)) ∧ s.sideB = ({2, 3} : Finset (Fin 4)) ∧
      δ.val 0 1 + δ.val 2 3 < δ.val 0 2 + δ.val 1 3 ∧
      δ.val 0 1 + δ.val 2 3 < δ.val 0 3 + δ.val 1 2 ∧
      ¬ 0 < bunemanIndex δ s := by
  refine ⟨neighborDissim, pairSplit, pairSplit_sideA, pairSplit_sideB, ?_, ?_,
    not_bunemanIndex_pos_neighbor⟩
  · simp only [neighborDissim, neighborVal]; norm_num
  · simp only [neighborDissim, neighborVal]; norm_num

end Dissimilarity
end NJ
