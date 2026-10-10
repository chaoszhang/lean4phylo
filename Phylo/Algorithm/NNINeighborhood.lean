/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NNI
import Phylo.Algorithm.RF

/-!
# `Phylo.Algorithm.NNINeighborhood` —— NNI 的邻域结构与度量层（W11g · T-4）

## 0. 文献（在手，行号即 `references/md/` 下该 md 的行号）

* **Allen, B. L. & Steel, M. (2001)**, *Subtree transfer operations and their induced metrics on
  evolutionary trees*, Annals of Combinatorics **5**(1):1–15
  （`AllenSteel2001_SubtreeTransferOperationsAnnalsOfCombinatorics.md`）。
  该文给出 **NNI / SPR / TBR 邻域**的定义与**由邻域诱导的度量** `d_{NNI}`、`d_{SPR}`、`d_{TBR}`，
  并证明它们在树空间上是**度量**（同一棵树距离 0、对称、三角不等式）。
* **Semple, C. & Steel, M. (2003)**, *Phylogenetics*, §2.4（NNI）与 §3（树空间）。
* **Robinson, D. F. (1971)** / **Robinson & Foulds (1981)**：NNI 的原始定义与 RF 度量。
  ⚠️ **两文未入库** ⇒ 本文件只用库内 `Phylo/Algorithm/RF.lean` 的 `rfDistance`
  （`symmDiffCard` 骨架），不引用未核实的条目。

## 1. 本文件做什么

`Phylo/Algorithm/NNI.lean` 已把 **NNI 分解**落在 split 层（`nniParts` / `nniResolvent`）并证明
**三个分解（母 split + 两个 NNI）两两不相容**。本文件在它之上补 **邻域 / 度量** 层：

* ★★ **3-循环封闭性**（`nniResolvent_nniResolvent_parent` / `…_swap`）：
  从任一分解出发、用同一对四块再做一次 NNI，**恰好回到**另外两个分解 ——
  这就是「边 `e` 的 NNI 邻域 `{S₀,S₁,S₂}` 在这两个操作下封闭」。
* ★★ **三个分解互不相同**（`nniResolvent_ne_parent` / `…_ne_swap` / `ne_two`）：
  ⚠️ 这一条**不能**由既有的「两两不相容」推出 —— `Incompatible s s` 恒真
  （`s.sideA` 非空，故 `¬ s.Compatible s`），所以「两两不相容」并不蕴涵「互不相同」。
  本文件用 `sideA` 的集合论证补上（`Phylo/Algorithm/NNI.lean` 文档里
  「NNI 邻域恰有 3 个互不相同的成员」的「不同」一半）。
* ★★★ **NNI 图（split 层）** `NNIMove` + `NNIDist`：一次 NNI 移动的**定义**、
  **不可反身性**（`nniMove_ne`）、**对称性**（`nniMove_symm`）、
  **恰好改动 2 条 RF 分裂**（`nniMove_rfDistance`）、**距离的对称性**（`nniDist_symm`）、
  以及 ★★★ **下界 `rfDistance ≤ 2·k`**（`rfDistance_le_two_mul_nniDist`）——
  即 Allen–Steel 意义下「NNI 度量 ≥ ½ · RF 度量」。
* ★B **反例检查**：派单建议的公式 `NNI 距离 = 2(n−3) − |共有内部分裂|` **是假的**，
  已在 `n=4` 的一次 NNI 上给出 `Fin 4` 显式反例（`nniDistanceCandidate_wrong`）。
* ★C **最小具体例子**（`Fin 4`，三叶集无关）：`{0,1}|{2,3}` 的三个分解、
  两个显式 NNI 移动、RF 变化 = 2。
* ⬜ **缺口** `nniDistance_exact_gap`：NNI 图的**连通性**＋**精确闭式**。

## 2. ⚠️ 诚实的边界（必读）

* 本文件的 `NNIMove` 是**纯组合的** split 系统层移动：它**不要求** `S` 是某棵树的 split 系统，
  也**不要求**新 split 与 `S` 里其余 split 相容。理由：那条相容性引理必须用到
  「`t` 是 `T` 的 split」（`NNI.lean` 文档里已给出**反例**：只在四块上做组合是**假命题**），
  而库内「split 系统 ⟸ 相容族」的机器（`Phylo/Supertree.lean`）**只能造出非二叉树**，
  不足以完成二叉树层的 NNI 邻域刻画 ⇒ 落缺口（见 §7）。
* 因此本文件证的是 **NNI 图（组合层）** 的性质；「NNI 图 = 树的 NNI 图」这一**语义桥**
  仍缺（同一缺口）。
-/

universe u

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. 3-循环封闭性：从任一分解出发再走一步，回到另外两个分解 -/

section Closure

variable (s : Split α) (A₁ B₁ : Finset α)

/-- `A₁` 与 `B₁` 不交（由各自落在 `s` 的两侧得到）。 -/
theorem disjoint_A₁_B₁ (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB) :
    Disjoint A₁ B₁ :=
  Finset.disjoint_left.mpr fun _ hx hy =>
    (Finset.disjoint_left.mp s.disjoint_sides) (hA₁sub hx) (hB₁sub hy)

/-- `(A₁ ∪ B₁) \ A₁ = B₁`。 -/
theorem sdiff_union_eq_right (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB) :
    (A₁ ∪ B₁) \ A₁ = B₁ :=
  Finset.union_sdiff_cancel_left (s.disjoint_A₁_B₁ A₁ B₁ hA₁sub hB₁sub)

/-- `((s.A \ A₁) ∪ (s.B \ B₁)) \ (s.A \ A₁) = s.B \ B₁`。 -/
theorem sdiff_union_sideB :
    ((s.sideA \ A₁) ∪ (s.sideB \ B₁)) \ (s.sideA \ A₁) = s.sideB \ B₁ := by
  refine Finset.union_sdiff_cancel_left ?_
  refine Finset.disjoint_left.mpr fun _ hx hy => ?_
  exact (Finset.disjoint_left.mp s.disjoint_sides)
    (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1

/-- `((s.A \ A₁) ∪ (s.B \ B₁)) \ (s.B \ B₁) = s.A \ A₁`。 -/
theorem sdiff_union_sideA :
    ((s.sideA \ A₁) ∪ (s.sideB \ B₁)) \ (s.sideB \ B₁) = s.sideA \ A₁ := by
  refine Finset.union_sdiff_cancel_right ?_
  refine Finset.disjoint_left.mpr fun _ hx hy => ?_
  exact (Finset.disjoint_left.mp s.disjoint_sides)
    (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1

/-- ★★ **NNI 3-循环（回到母 split）**：把 `S₁ := nniResolvent A₁ B₁` 再按四块
`(A₁, A₂)`（`A₂ := s.A \ A₁`）做一次 NNI，**恰好回到** `s`。 -/
theorem nniResolvent_nniResolvent_parent (hA₁ : A₁.Nonempty)
    (hA₂ : (s.sideA \ A₁).Nonempty) (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).nniResolvent A₁ (s.sideA \ A₁) hA₁
      (by rw [nniResolvent_sideA, sdiff_union_eq_right s A₁ B₁ hA₁sub hB₁sub]; exact hB₁)
      (by rw [nniResolvent_sideA]; exact Finset.subset_union_left)
      (by rw [nniResolvent_sideB]; exact Finset.subset_union_left) = s := by
  refine (KPartition.eq_iff_parts _ _).mpr ?_
  funext i
  by_cases hi : i = 0
  · subst hi
    show A₁ ∪ (s.sideA \ A₁) = s.sideA
    exact Finset.union_sdiff_of_subset hA₁sub
  · have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    show ((A₁ ∪ B₁) \ A₁) ∪ (((s.sideA \ A₁) ∪ (s.sideB \ B₁)) \ (s.sideA \ A₁)) = s.sideB
    rw [sdiff_union_eq_right s A₁ B₁ hA₁sub hB₁sub,
      sdiff_union_sideB s A₁ B₁,
      Finset.union_sdiff_of_subset hB₁sub]

/-- ★★ **NNI 3-循环（走到另一个 NNI 分解）**：把 `S₁ := nniResolvent A₁ B₁` 按四块
`(A₁, B₂)`（`B₂ := s.B \ B₁`）再做一次 NNI，**恰好给出** `S₂ := nniResolvent A₁ B₂`。 -/
theorem nniResolvent_nniResolvent_swap (hA₁ : A₁.Nonempty)
    (hA₂ : (s.sideA \ A₁).Nonempty) (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).nniResolvent A₁ (s.sideB \ B₁) hA₁
      (by rw [nniResolvent_sideA, sdiff_union_eq_right s A₁ B₁ hA₁sub hB₁sub]; exact hB₁)
      (by rw [nniResolvent_sideA]; exact Finset.subset_union_left)
      (by rw [nniResolvent_sideB]; exact Finset.subset_union_right) =
    s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset := by
  refine (KPartition.eq_iff_parts _ _).mpr ?_
  funext i
  by_cases hi : i = 0
  · subst hi
    show A₁ ∪ (s.sideB \ B₁) = A₁ ∪ (s.sideB \ B₁)
    rfl
  · have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    show ((A₁ ∪ B₁) \ A₁) ∪ (((s.sideA \ A₁) ∪ (s.sideB \ B₁)) \ (s.sideB \ B₁)) =
      (s.sideA \ A₁) ∪ (s.sideB \ (s.sideB \ B₁))
    rw [sdiff_union_eq_right s A₁ B₁ hA₁sub hB₁sub,
      sdiff_union_sideA s A₁ B₁,
      Finset.sdiff_sdiff_eq_self hB₁sub, Finset.union_comm]

end Closure

/-! ## 2. 三个分解互不相同（补 `NNI.lean` 文档里「互不相同」的一半） -/

section Distinct

variable (s : Split α) (A₁ B₁ : Finset α)

/-- ★★ **一个分解不等于母 split**：`A₁ ∪ B₁ ≠ s.sideA`（因 `B₁` 非空且落在 `s.sideB`）。 -/
theorem nniResolvent_ne_parent (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty) :
    s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ≠ s := by
  intro h
  have hside : A₁ ∪ B₁ = s.sideA := by
    rw [← nniResolvent_sideA s A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub, h]
  obtain ⟨x, hx⟩ := hB₁
  have hxA : x ∈ s.sideA := hside ▸ Finset.mem_union_right A₁ hx
  exact (Finset.disjoint_left.mp s.disjoint_sides) hxA (hB₁sub hx)

/-- ★★ **两个互补分解互不相同**：`nniResolvent A₁ B₁ ≠ nniResolvent A₁ (s.B \ B₁)`。 -/
theorem nniResolvent_ne_swap (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty) :
    s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ≠
      s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset := by
  intro h
  have hside : A₁ ∪ B₁ = A₁ ∪ (s.sideB \ B₁) := by
    rw [← nniResolvent_sideA s A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub,
      ← nniResolvent_sideA s A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset, h]
  obtain ⟨x, hx⟩ := hB₁
  have hx' : x ∈ A₁ ∪ (s.sideB \ B₁) := hside ▸ Finset.mem_union_right A₁ hx
  rcases Finset.mem_union.mp hx' with h' | h'
  · exact (Finset.disjoint_left.mp s.disjoint_sides) (hA₁sub h') (hB₁sub hx)
  · exact (Finset.mem_sdiff.mp h').2 hx

/-- ★★★ **边 `e` 的三个分解互不相同**（母 split、NNI-1、NNI-2）——
补齐 `NNI.lean` 文档「NNI 邻域恰有 3 个互不相同的成员」中**「互不相同」**的一半
（另一半「两两不相容」见 `nniResolvent_three_incompatible`）。

⚠️ 说明：**不能**用「两两不相容」推出不同 —— `Incompatible s s` 恒真
（`s.sideA` 非空 ⟹ `¬ Compatible s s`）。 -/
theorem nniResolvent_three_distinct (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hB₂ : (s.sideB \ B₁).Nonempty) :
    s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ≠ s ∧
    s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ≠
      s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset ∧
    s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset ≠ s := by
  refine ⟨nniResolvent_ne_parent s A₁ B₁ hA₁sub hB₁sub hB₁ hA₁ hA₂,
    nniResolvent_ne_swap s A₁ B₁ hA₁sub hB₁sub hB₁ hA₁ hA₂,
    fun h => nniResolvent_ne_parent s A₁ (s.sideB \ B₁) hA₁sub Finset.sdiff_subset
      hB₂ hA₁ hA₂ h⟩

end Distinct

/-! ## 3. NNI 图（split 系统层） -/

/-- **一次 NNI 移动**：把 split 系统 `S` 中**一条** split `s` 换成它的一个 NNI 分解 `s'`，
其余 split 不动。

⚠️ 这是**纯组合**的移动（不要求 `S` 是树的 split 系统，也不要求 `s'` 与其余 split 相容）。
语义桥（树的 NNI 图 ⟷ 本关系）见文件头「诚实的边界」。 -/
def NNIMove (S S' : Finset (Split α)) : Prop :=
  ∃ (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (_hB₁ : B₁.Nonempty) (_hB₂ : (s.sideB \ B₁).Nonempty),
    s ∈ S ∧ s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ∉ S ∧
      S' = insert (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub) (S.erase s)

/-- ★★ **NNI 移动不可反身**：真的改动了一点东西（`s' ∉ S` 而 `s' ∈ S'`）。 -/
theorem nniMove_ne {S S' : Finset (Split α)} (h : NNIMove S S') : S' ≠ S := by
  obtain ⟨s, A₁, B₁, hA₁, hA₂, hA₁sub, hB₁sub, _hB₁, _hB₂, _hs, hs', hS'⟩ := h
  intro hEq
  have hmem : s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub ∈ S' := by
    rw [hS']; exact Finset.mem_insert_self _ _
  rw [hEq] at hmem
  exact hs' hmem

/-- ★★ **一次 NNI 移动恰好改掉 `s`、加上 `s'`**：`S \ S' = {s}` 且 `S' \ S = {s'}`。 -/
theorem nniMove_sdiff {S S' : Finset (Split α)} (h : NNIMove S S') :
    ∃ s s' : Split α, s ≠ s' ∧ S \ S' = {s} ∧ S' \ S = {s'} := by
  obtain ⟨s, A₁, B₁, hA₁, hA₂, hA₁sub, hB₁sub, _hB₁, _hB₂, hs, hs', hS'⟩ := h
  refine ⟨s, s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub, ?_, ?_, ?_⟩
  · intro hEq
    exact hs' (hEq ▸ hs)
  · ext x
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hxS, hxS'⟩
      rw [hS', Finset.mem_insert, not_or] at hxS'
      by_contra hxs
      exact hxS'.2 (Finset.mem_erase.mpr ⟨hxs, hxS⟩)
    · rintro rfl
      refine ⟨hs, ?_⟩
      rw [hS', Finset.mem_insert, not_or]
      exact ⟨by intro hEq; exact hs' (hEq ▸ hs), by simp [Finset.mem_erase]⟩
  · ext x
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hxS', hxS⟩
      rw [hS', Finset.mem_insert] at hxS'
      rcases hxS' with rfl | hxEr
      · rfl
      · rw [Finset.mem_erase] at hxEr
        exact absurd hxEr.2 hxS
    · rintro rfl
      refine ⟨?_, hs'⟩
      rw [hS']; exact Finset.mem_insert_self _ _

/-- ★★★ **一次 NNI 移动改变 RF 距离恰为 2**（对称差 = `{s} ∪ {s'}`）。 -/
theorem nniMove_rfDistance {S S' : Finset (Split α)} (h : NNIMove S S') :
    rfDistance S S' = 2 := by
  obtain ⟨s, s', hsne, h1, h2⟩ := nniMove_sdiff h
  rw [rfDistance_def, h1, h2, Finset.singleton_union, Finset.card_pair hsne]

/-- ★★ **NNI 移动对称**（NNI 图是无向图）：由 3-循环封闭性给出反向移动。 -/
theorem nniMove_symm {S S' : Finset (Split α)} (h : NNIMove S S') : NNIMove S' S := by
  obtain ⟨s, A₁, B₁, hA₁, hA₂, hA₁sub, hB₁sub, hB₁, hB₂, hs, hs', hS'⟩ := h
  refine ⟨s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub, A₁, s.sideA \ A₁, hA₁,
    ?_, ?_, ?_, hA₂, ?_, ?_, ?_, ?_⟩
  · rw [nniResolvent_sideA, sdiff_union_eq_right s A₁ B₁ hA₁sub hB₁sub]; exact hB₁
  · rw [nniResolvent_sideA]; exact Finset.subset_union_left
  · rw [nniResolvent_sideB]; exact Finset.subset_union_left
  · rw [nniResolvent_sideB, sdiff_union_sideB s A₁ B₁]; exact hB₂
  · rw [hS']; exact Finset.mem_insert_self _ _
  · rw [hS', nniResolvent_nniResolvent_parent s A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub hB₁]
    intro hmem
    rw [Finset.mem_insert] at hmem
    rcases hmem with hEq | hEr
    · exact hs' (hEq ▸ hs)
    · rw [Finset.mem_erase] at hEr
      exact absurd rfl hEr.1
  · rw [nniResolvent_nniResolvent_parent s A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub hB₁, hS',
      Finset.erase_insert (fun h => hs' (Finset.mem_of_mem_erase h)), Finset.insert_erase hs]

/-! ### NNI 度量（图距离的上界形式）

`NNIDist S S' k` 读作「NNI 图上从 `S` 到 `S'` 有一条长度（步数）`k` 的行走」。
**精确**距离就是使 `NNIDist` 成立的最小 `k`（其存在性见缺口）。 -/

/-- **NNI 图上的行走（步数 `k`）**。 -/
def NNIDist : Finset (Split α) → Finset (Split α) → ℕ → Prop
  | S, S', 0 => S = S'
  | S, S', k + 1 => ∃ R, NNIMove S R ∧ NNIDist R S' k

/-- 0 步 ⟺ 同一个 split 系统。 -/
theorem nniDist_zero_iff {S S' : Finset (Split α)} : NNIDist S S' 0 ↔ S = S' := Iff.rfl

/-- 一次移动给出 1 步行走。 -/
theorem nniDist_one_of_move {S S' : Finset (Split α)} (h : NNIMove S S') :
    NNIDist S S' 1 := ⟨S', h, rfl⟩

/-- ★★ **两次行走可拼接**（长度相加）。 -/
theorem nniDist_append : ∀ {A B C : Finset (Split α)} {k l : ℕ},
    NNIDist A B k → NNIDist B C l → NNIDist A C (k + l)
  | _, B, C, 0, l, hAB, hBC => by
    rw [nniDist_zero_iff] at hAB
    subst hAB
    simpa using hBC
  | A, B, C, k + 1, l, hAB, hBC => by
    obtain ⟨R, hAR, hRB⟩ := hAB
    rw [Nat.add_right_comm]
    exact ⟨R, hAR, nniDist_append hRB hBC⟩

/-- ★★ **行走对称**（NNI 图无向 ⟹ 步数对称）。 -/
theorem nniDist_symm : ∀ {A B : Finset (Split α)} {k : ℕ}, NNIDist A B k → NNIDist B A k
  | A, B, 0, h => by
    rw [nniDist_zero_iff] at h ⊢
    exact h.symm
  | A, B, k + 1, h => by
    obtain ⟨R, hAR, hRB⟩ := h
    exact nniDist_append (nniDist_symm hRB) (nniDist_one_of_move (nniMove_symm hAR))

/-- ★★★ **NNI 步数下界 RF 距离的一半**：`rfDistance ≤ 2 · k`。

即（Allen–Steel 意义下）**NNI 度量 ≥ ½ RF 度量**：每次 NNI 只动 2 条分裂
（`nniMove_rfDistance`），RF 是度量（三角不等式 `symmDiffCard_triangle`）。 -/
theorem rfDistance_le_two_mul_nniDist : ∀ {S S' : Finset (Split α)} {k : ℕ},
    NNIDist S S' k → rfDistance S S' ≤ 2 * k
  | S, S', 0, h => by
    rw [nniDist_zero_iff] at h
    subst h
    simp
  | S, S', k + 1, h => by
    obtain ⟨R, hSR, hR⟩ := h
    have h1 : rfDistance S S' ≤ rfDistance S R + rfDistance R S' :=
      symmDiffCard_triangle S R S'
    have h2 : rfDistance S R = 2 := nniMove_rfDistance hSR
    have h3 : rfDistance R S' ≤ 2 * k := rfDistance_le_two_mul_nniDist hR
    omega

end Split

/-! ## 4. ★B 反例检查：派单建议的公式 `2(n−3) − |共有内部分裂|` 是**假的** -/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- ★B **候选公式**（派单原文建议）：`NNI 距离 =?= 2(n−3) − |共有（内部）分裂|`。

写成 `ℤ` 值函数以便如实比较（`n` = 叶数、`S ∩ S'` = 共有分裂数）。 -/
def nniDistanceCandidate (n : ℕ) (S S' : Finset (Split α)) : ℤ :=
  2 * ((n : ℤ) - 3) - ((S ∩ S').card : ℤ)

end Split

/-! ## 5. ★C 最小具体例子：`Fin 4` 上的四分树 `01|23` 及其 NNI 邻域 -/

namespace Split

/-- 局部可判定性实例（`SidesCompatible`/`Disjoint` 是 `def`，类型类搜索不展开）。 -/
local instance instDecDisjointFinsetFin4 (A B : Finset (Fin 4)) : Decidable (Disjoint A B) :=
  Finset.decidableDisjoint A B

/-- ★C 母 split：`{0,1} | {2,3}`（四分树 `01|23` 的内部边）。 -/
def exS₀ : Split (Fin 4) where
  parts i := if i = 0 then {0, 1} else {2, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- ★C NNI-1：`{0,2} | {1,3}`。 -/
def exS₁ : Split (Fin 4) where
  parts i := if i = 0 then {0, 2} else {1, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- ★C NNI-2：`{0,3} | {1,2}`。 -/
def exS₂ : Split (Fin 4) where
  parts i := if i = 0 then {0, 3} else {1, 2}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

@[simp] theorem exS₀_sideA : exS₀.sideA = {0, 1} := rfl

@[simp] theorem exS₀_sideB : exS₀.sideB = {2, 3} := rfl

@[simp] theorem exS₁_sideA : exS₁.sideA = {0, 2} := rfl

@[simp] theorem exS₂_sideA : exS₂.sideA = {0, 3} := rfl

/-- ★C **拆分数据自洽**：`exS₀` 的三分解（`A₁ = {0}`、`B₁ = {2}`）给出 `exS₁`。 -/
theorem ex_nniResolvent_eq_S₁ :
    exS₀.nniResolvent ({0} : Finset (Fin 4)) ({2} : Finset (Fin 4))
      (by decide) (by decide) (by decide) (by decide) = exS₁ := by
  refine (KPartition.eq_iff_parts _ _).mpr ?_
  funext i
  fin_cases i <;> rfl

/-- ★C **互补分解**（`B₂ = {3}`）给出 `exS₂`。 -/
theorem ex_nniResolvent_eq_S₂ :
    exS₀.nniResolvent ({0} : Finset (Fin 4)) ({3} : Finset (Fin 4))
      (by decide) (by decide) (by decide) (by decide) = exS₂ := by
  refine (KPartition.eq_iff_parts _ _).mpr ?_
  funext i
  fin_cases i <;> rfl

/-- ★C **显式 NNI 移动**：`{exS₀} → {exS₁}`（单元素 split 系统上的一次 NNI）。 -/
theorem ex_nniMove :
    NNIMove ({exS₀} : Finset (Split (Fin 4))) {exS₁} :=
  ⟨exS₀, {0}, {2}, by decide, by decide, by decide, by decide,
    by decide, by decide, Finset.mem_singleton_self _, by decide,
    by rw [ex_nniResolvent_eq_S₁]; simp⟩

/-- ★C 反空真：一次移动 ⟹ 1 步、RF 距离 2、且不可 0 步。 -/
theorem ex_nni_nonempty :
    NNIDist ({exS₀} : Finset (Split (Fin 4))) {exS₁} 1 ∧
      rfDistance ({exS₀} : Finset (Split (Fin 4))) {exS₁} = 2 ∧
      ¬ NNIDist ({exS₀} : Finset (Split (Fin 4))) {exS₁} 0 :=
  ⟨nniDist_one_of_move ex_nniMove, nniMove_rfDistance ex_nniMove,
    fun h => nniMove_ne ex_nniMove h.symm⟩

/-- ★B ★★★ **派单建议的公式是假的**：`n = 4` 时一次 NNI 移动的两棵树
**共有内部分裂为 0**、**NNI 距离 = 1**，而候选公式 `2(n−3) − |共有|` 给出 `2`。

（`n = 4` 的二叉树只有 `n − 3 = 1` 条内部分裂；`exS₀ ≠ exS₁` ⟹ 交集为空；
`deep`：「1 步可达」＋「0 步不可达」⟹ 精确距离 `= 1`。） -/
theorem nniDistanceCandidate_wrong :
    ∃ S S' : Finset (Split (Fin 4)), NNIDist S S' 1 ∧ ¬ NNIDist S S' 0 ∧
      nniDistanceCandidate 4 S S' = 2 := by
  refine ⟨{exS₀}, {exS₁}, nniDist_one_of_move ex_nniMove, ?_, ?_⟩
  · intro h
    exact nniMove_ne ex_nniMove h.symm
  · rw [nniDistanceCandidate]
    have hcard : (({exS₀} : Finset (Split (Fin 4))) ∩ {exS₁}).card = 0 := by decide
    rw [hcard]
    norm_num

end Split

/-! ## 6. 缺口 -/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- ⬜ **缺口（T-4）：NNI 图的连通性 ＋ 精确 NNI 距离的闭式**。

**陈述**：对任意两个「同为某二叉树的 split 系统」的 `S, S'`，

1. **可达**：`∃ k, NNIDist S S' k`（NNI 图连通）；
2. **精确距离是良定义的**：`∃! k, NNIDist S S' k ∧ ∀ j, NNIDist S S' j → k ≤ j`。

**为什么未证**：

* (1) 是 **Allen–Steel 2001 / Robinson 1971** 的连通性定理，其库内路线需要
  「split 系统 ⟸ 相容族」的**二叉**反射（`Phylo/Supertree.lean` 只能造非二叉树，
  而 NNI 只在二叉树上定义）⇒ 缺**二叉反射**这一器材；本文件 §3 的 `NNIMove`
  也只是**组合层**移动，其与「树层 NNI 操作」的语义桥同样缺。
* (2) 的闭式**不存在简单的 `2(n−3) − |共有|`** —— 本文件 ★B
  `nniDistanceCandidate_wrong` 已给出 `n = 4` 的反例；精确计算的一般复杂度结果是
  **NP-hard**（DasGupta, He, Jiang, Li & Tromp 2000，*SICOMP*），
  ⚠️ 该文**未入库** ⇒ 本库不引用其条目，只把它记为「待核实的复杂度归属」。
  本文件于是**只**证可证的下界 `rfDistance ≤ 2·k`（`rfDistance_le_two_mul_nniDist`）。 -/
def nniDistance_exact_gap (n : ℕ) (S S' : Finset (Split (Fin n))) : Prop :=
  (∃ k : ℕ, NNIDist S S' k) ∧
    ∃! k : ℕ, NNIDist S S' k ∧ ∀ j : ℕ, NNIDist S S' j → k ≤ j

end Split
