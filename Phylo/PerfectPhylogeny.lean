/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Compatibility

/-!
# `Phylo.PerfectPhylogeny` —— **完美系统发生（perfect phylogeny）与 Four Gamete 条件**

**任务**：W11d / X2（Gusfield 1991 完美系统发生）。

## 0. 文献（**逐字核读 + 行号**）

⚠️ **来源边界（诚实声明）**：派单点名的两篇**都不在库内** ——

* **Gusfield 1991**, *Efficient algorithms for inferring evolutionary trees*,
  *Networks* **21**:257–269 —— 见 `W11_MISSING_LITERATURE.md:50`：
  「**Gusfield 1991**（→ X2 完美系统发生算法）｜*Networks* **21**:257–269｜
  `10.1002/net.3230210104`（⚠️ **不是** `…304`）｜`LamGusfieldSridhar2009`（已入库）」。
  ⇒ 该篇属本库**已知缺失、非阻塞**的原始出处；**指定替代**（已入库、Gusfield 本人为作者）：
  `references/md/LamGusfieldSridhar2009_PerfectPhylogenyThreeStateCharactersarXiv0905.1417.md`。
  （⚠️ 派单里的出处「*Networks* **1**(2):133–151」与已联网核实的 **21**:257–269 **不符** —— 见上文。）
* **Semple & Steel 2003**, *Phylogenetics*（第 4 章）—— 库内 `references/` **只有**该书的
  `SempleSteel2000_MinCutSupertree` 与 `SempleSteel2002_TreeReconstructionMultiStateCharacters`
  两篇**论文**，**教科书本体不在库内**。故本文件**不**引用该书页码/行号。

以下定理陈述**逐字**引自替代文献（行号为该 `.md` 文件行号）：

* **完美系统发生的定义**（193–205 行）：

  > The perfect phylogeny problem is to determine whether an input set S can be
  > displayed on a tree such that
  > (1) each sequence in input set S labels exactly one leaf in T
  > (2) each vertex of T is labeled by a species
  > (3) for every character χi and for every state χi_j of character χi, the set of all
  > vertices in T such that the state of character χi is χi_j forms a connected
  > subtree of T .

* ★★★ **Theorem 1.1（Splits Equivalence Theorem / Four Gamete Condition）**（104–106 行）：

  > **Theorem 1.1 (Splits Equivalence Theorem, Four Gamete Condition
  > [11, 15, 27]).** A perfect phylogeny exists for binary input sequences if and only if no
  > pair of characters contains all four possible binary pairs 00, 01, 10, 11.

* ★ **Theorem 2.4**（276–278 行）—— 为什么 two-state 特殊：

  > **Theorem 2.4.** Given an input set S on m characters with at most three states per
  > character (r ≤ 3), S admits a perfect phylogeny if and only if every subset of three
  > characters of S admits a perfect phylogeny.

* ★★ **两两相容对多状态不充分**（131–140 行）：

  > In 1975, Fitch gave an example of input S over three states such that every pair
  > of characters in S allows a perfect phylogeny while the entire set of characters S
  > does not [12, 13, 14, 30]. …
  > “The Fitch examples show that any algorithm to determine whether
  > a set of characters is compatible must consider the set as a whole
  > and cannot take the shortcut of only checking pairs of characters.” [27]

* ★★ **Theorem 7.1（Fitch–Meacham `F_r`）**（1290–1292 行）：

  > **Theorem 7.1.** [27] For every r ≥ 2, Fr is a set of input sequences over r state
  > characters such that every r −1 subset of characters allows a perfect phylogeny while
  > the entire set Fr does not allow a perfect phylogeny.

## 1. 本文件的定位（**不重复造库内已有的**）

「两两相容 ⟹ 存在树展示全体」在库内的 **split 层**已证：
`supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）；
**字符层**（EJM 树偏序 / `CharCompatible`）在 `Phylo/Compatibility.lean` 已证
（`pairwise_compatible_characters_have_tree`）。

本文件补的是 **Gusfield Theorem 1.1 的那一层**：**二元字符**的完美系统发生，
其判据是 **`SidesCompatible`**（`Phylo/Split.lean:40`）——
**不是** EJM 的 `BinaryCompatible`（`Phylo/Compatibility.lean:129`）。

### ★B 为什么必须是 `SidesCompatible` 而不是 `BinaryCompatible`（反例检查）

「两两相容是否**充分**？首先，『相容』用哪个谓词？」

库内 `BinaryCompatible A B := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B`（有根 / 祖先态固定的 EJM 判据），
而 Gusfield 条件 (3) 允许**任一侧**作为状态类 ⟹ 正确的相容谓词是
`SidesCompatible A B := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ`（多出的第 4 项
`A ∪ B = univ` 正是「根的状态为 1」的那一支）。

**最小反例**：`X = {0,1,2}`、`A = {0,1}`、`B = {0,2}`。
**完美系统发生存在**（★C，见 `perfectPhylogeny_pair_witness`：三叶星形树，
中心标 `(1,1)`、叶 `0` 标 `(1,1)`、叶 `1` 标 `(1,0)`、叶 `2` 标 `(0,1)`），
但 `BinaryCompatible A B` **为假**（`not_binaryCompatible_witness`）。
⇒ **`BinaryCompatible` 过强，用它会漏掉真正的完美系统发生** ✗；
`CharCompatible`（由 `BinaryCompatible` 定义）因此在 two-state 下**严格强于** Theorem 1.1 的判据
（`charCompatible_imp_sidesCompatible` 是一个方向，另一个方向有反例）。

**多状态呢？不充分** ✗ —— 但那要换**语义**：Gusfield 条件 (3) 用的是**连通子树**，
而库内 `Cladogram.IsSideOf`（`Phylo/Compatibility.lean:228`）只给出「**边侧**」。
对 **2 个状态**两者一致（两状态类都连通 ⟹ 恰换一次 ⟹ 1-类是边侧）；
对 **≥3 个状态**「连通」**严格更弱**（例：毛虫树 `a—v₁—v₂—v₃—v₄—d`、`b@v₂`、`c@v₃`，
`{b,c}` 连通但**不是任何边的侧**），于是 `F₃` 反例（`MultiStatePairwiseInsufficiencyGap`）。
⚠️ 注意：在**边侧**语义下两两 ⟹ 全局**仍成立**（走 `supertree_displays_of_pairwiseCompatible`），
所以多状态的不充分**不可能**在边侧语义里看到 —— 这正是缺口的实质。

## 2. 结论一览

* `sidesCompatible_iff_no_four_gametes` ★★：`SidesCompatible A B` ⟺ 不含四个 gamete
  （`00,01,10,11` 全出现）—— Theorem 1.1 里那个「pairwise test」的组合内核（`O(nm²)` 那一层）；
* `exists_cladogram_displays_of_pairwise_sidesCompatible` ★★：两两 `SidesCompatible` ⟹
  存在 `Cladogram` 展示全体（二元字符）；
* `pairwise_sidesCompatible_of_exists_cladogram_displays` ★★：**反向**（完美系统发生 ⟹ 两两相容）；
* `exists_cladogram_displays_iff_pairwise_sidesCompatible` ★★★：**等价刻画**（`3 ≤ |X|`）；
* `hasPerfectPhylogeny_iff_matrixPairwiseCompatible` ★★★：**字符矩阵**版本（Theorem 1.1 本体的形态）。

## 3. 缺口（显式 `def … : Prop`，**未证**，不得当作已证）

* `BinaryConnectedEqualsSideGap` —— Gusfield 条件 (3) 的「连通子树」语义与库内「边侧」的等价（r = 2）；
* `MultiStatePairwiseInsufficiencyGap` —— `F₃`（5 taxa × 3 字符 × 3 状态）两两相容但全局不相容。
-/

open Phylo
open SimpleGraph

universe u v w

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## §1 Four Gamete 条件的组合内核（`O(nm²)` 那一层）

文献：`LamGusfieldSridhar2009` 104–106 行（Theorem 1.1）。
`SidesCompatible` 的定义在 `Phylo/Split.lean:40`（本库现成，**不重复造**）。 -/

/-- ★★ **Four Gamete 判据（`Phylo/Split.lean:40` 的 `SidesCompatible` 的显式形态）**：
`A`、`B` 两侧相容 ⟺ **不存在**同时出现的四个 gamete
`A∩B`（`11`）、`A∖B`（`10`）、`B∖A`（`01`）、`(A∪B)ᶜ`（`00`）。

文献（逐字，`LamGusfieldSridhar2009` 104–106 行）：
"A perfect phylogeny exists for binary input sequences if and only if no pair of characters
contains all four possible binary pairs 00, 01, 10, 11."

这就是 Theorem 1.1 里那个**逐对检查**的组合内核；配 `binaryFactor` 后即 `O(nm²)` 的判据。 -/
theorem sidesCompatible_iff_no_four_gametes {A B : Finset X} :
    SidesCompatible A B ↔
      ¬ ∃ w x y z : X,
        w ∈ A ∩ B ∧ x ∈ A \ B ∧ y ∈ B \ A ∧ z ∈ (A ∪ B)ᶜ := by
  constructor
  · rintro (h | h | h | h) ⟨w, x, y, z, hw, hx, hy, hz⟩
    · exact (Finset.mem_sdiff.mp hx).2 (h (Finset.mem_sdiff.mp hx).1)
    · exact (Finset.mem_sdiff.mp hy).2 (h (Finset.mem_sdiff.mp hy).1)
    · exact (Finset.disjoint_left.mp h) (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    · exact (Finset.mem_compl.mp hz) (by rw [h]; exact Finset.mem_univ z)
  · intro h
    by_cases hAB : A ⊆ B
    · exact Or.inl hAB
    · by_cases hBA : B ⊆ A
      · exact Or.inr (Or.inl hBA)
      · by_cases hd : Disjoint A B
        · exact Or.inr (Or.inr (Or.inl hd))
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hx : ∃ x, x ∈ A ∧ x ∉ B := by
            by_contra hc
            exact hAB fun a ha => by
              by_contra h'
              exact hc ⟨a, ha, h'⟩
          have hy : ∃ y, y ∈ B ∧ y ∉ A := by
            by_contra hc
            exact hBA fun a ha => by
              by_contra h'
              exact hc ⟨a, ha, h'⟩
          have hw : ∃ w, w ∈ A ∧ w ∈ B := by
            by_contra hc
            exact hd (Finset.disjoint_left.mpr fun x hxA hxB => hc ⟨x, hxA, hxB⟩)
          by_contra hne
          obtain ⟨z, hz⟩ := compl_nonempty_of_ne_univ hne
          obtain ⟨x, hxA, hxB⟩ := hx
          obtain ⟨y, hyB, hyA⟩ := hy
          obtain ⟨w, hwA, hwB⟩ := hw
          exact h ⟨w, x, y, z, Finset.mem_inter.mpr ⟨hwA, hwB⟩,
            Finset.mem_sdiff.mpr ⟨hxA, hxB⟩, Finset.mem_sdiff.mpr ⟨hyB, hyA⟩, hz⟩

/-! `SidesCompatible` 的**对称性**、**补侧不变**、以及 `Split.Compatible ⟺ SidesCompatible`
**库内现成**，本文件不重复造：

* `sidesCompatible_comm`（`Phylo/Split.lean:106`）；
* `sidesCompatible_compl_left` / `sidesCompatible_compl_right`（`Phylo/Split.lean:47/119`）；
* ★ `Split.compatible_iff_sides`（`Phylo/Split.lean:338`）：
  `Compatible s t ↔ SidesCompatible s.sideA t.sideA`。 -/

/-- ★ **`BinaryCompatible` ⟹ `SidesCompatible`**（EJM 判据 ⟹ Four Gamete 判据）。
前三个析取项逐字相同；`SidesCompatible` 多出的第 4 项 `A ∪ B = univ`
对应「根的状态为 1」这一支 —— 即**允许任一侧**作状态类。 -/
theorem binaryCompatible_imp_sidesCompatible {A B : Finset X}
    (h : BinaryCompatible A B) : SidesCompatible A B := by
  unfold BinaryCompatible at h
  unfold SidesCompatible
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- 二态字符若只有一个状态（`A = ∅` 或 `A = univ`），则它与任何字符相容（**非空真**辅助）。 -/
theorem sidesCompatible_of_eq_empty_or_univ {A B : Finset X}
    (hA : A = ∅ ∨ A = Finset.univ) : SidesCompatible A B := by
  rcases hA with h | h
  · rw [h]; exact Or.inl (Finset.empty_subset B)
  · rw [h]; exact Or.inr (Or.inl (Finset.subset_univ B))

/-- 同上，作用于右侧。 -/
theorem sidesCompatible_of_eq_empty_or_univ_right {A B : Finset X}
    (hB : B = ∅ ∨ B = Finset.univ) : SidesCompatible A B := by
  rcases hB with h | h
  · rw [h]; exact Or.inr (Or.inl (Finset.empty_subset A))
  · rw [h]; exact Or.inl (Finset.subset_univ A)

/-! ## §2 二元字符的「展示」关系与完美系统发生

文献（`LamGusfieldSridhar2009` 193–205 行）：条件 (3) 要求每个状态类
「forms a connected subtree of T」。本库 `Cladogram.IsSideOf`（`Phylo/Compatibility.lean:228`）
给出「是某条边的**叶侧**」——对**二元**字符两者一致（见 §3 缺口声明），故此处以 `IsSideOf` 为定义。 -/

/-- `T` **展示**二元字符（以 1-类 `A ⊆ X` 表示）。单态字符（`A = ∅` 或 `A = univ`）
无信息量、恒被展示，故走前两个析取项。 -/
def DisplaysBinary (T : Cladogram X) (A : Finset X) : Prop :=
  A = ∅ ∨ A = Finset.univ ∨ T.IsSideOf A

omit [DecidableEq X] in
/-- 所有非平凡二元字符都是「单次替换」（**非空真**辅助）。 -/
theorem displaysBinary_of_isSideOf {T : Cladogram X} {A : Finset X} (h : T.IsSideOf A) :
    DisplaysBinary T A :=
  Or.inr (Or.inr h)

/-- **二元字符矩阵的 1-类**：`{x | M i x = true}`（EJM Definition 6 的 `binaryFactor` 在 `Bool` 的特例）。 -/
noncomputable def charOneClass {ι : Type v} (M : ι → X → Bool) (i : ι) : Finset X :=
  binaryFactor (M i) true

/-- ★★ **二元字符矩阵的完美系统发生**（Gusfield 193–205 行条件 (1)(2)(3) 的二元形态）：
存在一棵 `Cladogram`，使每个字符的 1-类是它的一条边侧（⟺ 每个字符**至多改变一次**，无同塑性）。 -/
def HasPerfectPhylogeny {ι : Type v} (M : ι → X → Bool) : Prop :=
  ∃ T : Cladogram.{u, u} X, ∀ i : ι, DisplaysBinary T (charOneClass M i)

/-- ★★ **矩阵两两相容**（Four Gamete 条件的否定形式，逐对检查）。 -/
def MatrixPairwiseCompatible {ι : Type v} (M : ι → X → Bool) : Prop :=
  ∀ i j : ι, i ≠ j → SidesCompatible (charOneClass M i) (charOneClass M j)

/-- **相容性无需比较字符自身**（自反性）：同一字符的两个 1-类相同 ⟹ 相容。 -/
theorem sidesCompatible_self (A : Finset X) : SidesCompatible A A :=
  Or.inl (Finset.Subset.refl A)

/-- **库内 `CharCompatible`（EJM 判据）⟹ 本文件的 two-state 判据**。
反向**不成立**（`not_binaryCompatible_witness`）⟹ EJM 的 `CharCompatible` **严格强于**
Gusfield Theorem 1.1 的判据。 -/
theorem charCompatible_imp_sidesCompatible {K L : X → Bool}
    (h : CharCompatible K L) :
    SidesCompatible (binaryFactor K true) (binaryFactor L true) :=
  binaryCompatible_imp_sidesCompatible (h true true)

/-- **库内 `RealizesChar` 是一类完美系统发生**：`RealizesChar T K` ⟹ `T` 展示 `K` 的 1-类。
（把 `Phylo/Compatibility.lean` 的树偏序层与本文件的 two-state 层接起来。） -/
theorem displaysBinary_of_realizesChar {T : Cladogram X} {K : X → Bool}
    (h : RealizesChar T K) : DisplaysBinary T (binaryFactor K true) := by
  by_cases hne : (binaryFactor K true).Nonempty
  · by_cases hun : binaryFactor K true = Finset.univ
    · exact Or.inr (Or.inl hun)
    · exact Or.inr (Or.inr (h true hne hun))
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-! ## §3 ★★ 充分性：两两 `SidesCompatible` ⟹ 存在 `Cladogram` 展示全体

**证明路线**：非平凡 1-类 ↦ split `A | Aᶜ`（`splitOf`）；
`SidesCompatible` ⟹ `Split.Compatible`（`Split.compatible_of_sides`，`Phylo/Split.lean:293`）；
再用库内 ★★★ `supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）。
这与 `Phylo/Compatibility.lean` 的 `exists_cladogram_of_pairwise_binaryCompatible` 同构，
但**输入谓词是较弱的 `SidesCompatible`**，故**不能**由它代劳。 -/

theorem exists_cladogram_displays_of_pairwise_sidesCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (A : ι → Finset X)
    (hpair : ∀ i j, i ≠ j → SidesCompatible (A i) (A j)) (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i) := by
  classical
  obtain ⟨ρ, -⟩ : (Finset.univ : Finset X).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  -- 剥掉单态字符（`∅` / `univ` 都不可能是边侧，也无需展示）
  set G : Finset ι := Finset.univ.filter fun i => (A i).Nonempty ∧ A i ≠ Finset.univ with hG
  set fam : Finset (Split X) := G.attach.image fun i : ↥G =>
    splitOf (A i.1) (Finset.mem_filter.mp i.2).2.1
      (compl_nonempty_of_ne_univ (Finset.mem_filter.mp i.2).2.2) with hfam
  have hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t := by
    intro s hs t ht
    rw [hfam, Finset.mem_image] at hs ht
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, -, rfl⟩ := ht
    by_cases hij : i.1 = j.1
    · have hsub : i = j := Subtype.ext hij
      subst hsub
      exact Split.compatible_of_subset_left (Finset.Subset.refl _)
    · exact Split.compatible_of_sides (hpair i.1 j.1 hij)
  obtain ⟨M, hM⟩ := supertree_displays_of_pairwiseCompatible fam ρ hcomp h3
  refine ⟨M, fun i => ?_⟩
  by_cases hne : (A i).Nonempty
  · by_cases hun : A i = Finset.univ
    · exact Or.inr (Or.inl hun)
    · refine Or.inr (Or.inr ?_)
      have hiG : i ∈ G := by
        rw [hG]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne, hun⟩
      have hmem : splitOf (A i) hne (compl_nonempty_of_ne_univ hun) ∈ fam := by
        rw [hfam, Finset.mem_image]
        exact ⟨⟨i, hiG⟩, Finset.mem_attach _ _, rfl⟩
      exact Cladogram.isSideOf_of_isSplitOf_sideA (hM _ hmem) (splitOf_sideA (A i) _ _)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- ★★ **必要性（反向）**：完美系统发生 ⟹ 两两相容。

「两条边侧必 `SidesCompatible`」是库内现成的
`Cladogram.sidesCompatible_sideLeaves`（`Phylo/Split.lean:780`）——
**这正是 `SidesCompatible` 第 4 项 `A ∪ B = univ` 不可省的原因**：
取任意根后「向下的 clade」才镶嵌，而 `IsSideOf` 允许**两侧**任取。 -/
theorem pairwise_sidesCompatible_of_exists_cladogram_displays
    {ι : Type v} (A : ι → Finset X)
    (h : ∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i)) :
    ∀ i j, i ≠ j → SidesCompatible (A i) (A j) := by
  intro i j _
  obtain ⟨T, hT⟩ := h
  rcases hT i with hAi | hAi | hAi
  · exact sidesCompatible_of_eq_empty_or_univ (Or.inl hAi)
  · exact sidesCompatible_of_eq_empty_or_univ (Or.inr hAi)
  · rcases hT j with hAj | hAj | hAj
    · exact sidesCompatible_of_eq_empty_or_univ_right (Or.inl hAj)
    · exact sidesCompatible_of_eq_empty_or_univ_right (Or.inr hAj)
    · obtain ⟨a, b, hab, u, hu⟩ := hAi
      obtain ⟨c, d, hcd, w, hw⟩ := hAj
      rw [hu, hw]
      exact Cladogram.sidesCompatible_sideLeaves T hab hcd u w

/-- ★★★ **完美系统发生的等价刻画（two-state / 二元字符）**：

> 存在展示给定二元字符矩阵的完美系统发生 ⟺ 字符两两相容。

文献依据：`LamGusfieldSridhar2009` **Theorem 1.1**（104–106 行，Four Gamete Condition）。
「相容」取 Gusfield 的形态 = 本库 `SidesCompatible`（第 4 项 `A ∪ B = univ` 不可省，见 §B）。
⚠️ `3 ≤ |X|` 是库内 split 层定理的退化条件（`Phylo/Supertree.lean`）。 -/
theorem exists_cladogram_displays_iff_pairwise_sidesCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (A : ι → Finset X)
    (h3 : 3 ≤ Fintype.card X) :
    (∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i)) ↔
      (∀ i j, i ≠ j → SidesCompatible (A i) (A j)) :=
  ⟨fun h => pairwise_sidesCompatible_of_exists_cladogram_displays A h,
   fun h => exists_cladogram_displays_of_pairwise_sidesCompatible A h h3⟩

/-- ★★★ **Theorem 1.1 的字符矩阵形态**：二元字符矩阵有完美系统发生 ⟺ 逐对无四个 gamete
（`MatrixPairwiseCompatible` 经 `sidesCompatible_iff_no_four_gametes` 即「无 00/01/10/11」）。 -/
theorem hasPerfectPhylogeny_iff_matrixPairwiseCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (M : ι → X → Bool)
    (h3 : 3 ≤ Fintype.card X) :
    HasPerfectPhylogeny M ↔ MatrixPairwiseCompatible M :=
  exists_cladogram_displays_iff_pairwise_sidesCompatible (charOneClass M) h3

/-! ## §4 ★C 最小例子（3 taxa / 2 字符）端到端

`X = Fin 3`、字符 1-类 `A = {0,1}`、`B = {0,2}`（即「根的状态为 1」那一支）。
`BinaryCompatible A B` **为假**，但完美系统发生**存在**。
（穷举核验：`scripts/msc/w11d_x2_perfect_phylogeny.py`。） -/

/-- ★B **反例**：`A = {0,1}`、`B = {0,2}`（`X = Fin 3`）**不** `BinaryCompatible`
（`1 ∈ A∖B`、`2 ∈ B∖A`、`0 ∈ A∩B` 三者俱全）——
故 EJM 的 `BinaryCompatible` 对 two-state 完美系统发生**过强** ✗。 -/
theorem not_binaryCompatible_witness :
    ¬ BinaryCompatible ({0, 1} : Finset (Fin 3)) {0, 2} := by
  unfold BinaryCompatible
  decide

/-- ★B/★C 同一对**确实** `SidesCompatible`（第 4 项 `A ∪ B = univ`：`{0,1} ∪ {0,2} = univ`）。 -/
theorem sidesCompatible_witness :
    SidesCompatible ({0, 1} : Finset (Fin 3)) {0, 2} :=
  Or.inr (Or.inr (Or.inr (by decide)))

/-- ★C **端到端**：这 2 个字符的完美系统发生**存在**（3 叶星形树，中心标 `(1,1)`）。 -/
theorem exists_cladogram_displays_pair {A B : Finset X}
    (h : SidesCompatible A B) (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, DisplaysBinary T A ∧ DisplaysBinary T B := by
  classical
  have hpair : ∀ i j : Fin 2, i ≠ j →
      SidesCompatible (if i = 0 then A else B) (if j = 0 then A else B) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h
    · exact sidesCompatible_comm.mp h
    · exact absurd rfl hij
  obtain ⟨T, hT⟩ := exists_cladogram_displays_of_pairwise_sidesCompatible
    (fun i : Fin 2 => if i = 0 then A else B) hpair h3
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  exact ⟨T, by simpa using hT 0, by simpa [h10] using hT 1⟩

/-- ★C 最小例子的实例：`Fin 3` 上的 `{0,1}` 与 `{0,2}` 由同一棵树展示。 -/
theorem perfectPhylogeny_pair_witness :
    ∃ T : Cladogram.{0, 0} (Fin 3),
      DisplaysBinary T ({0, 1} : Finset (Fin 3)) ∧
        DisplaysBinary T ({0, 2} : Finset (Fin 3)) :=
  exists_cladogram_displays_pair sidesCompatible_witness (by decide)

/-- ★B **二元最小障碍（四个 gamete 本体）**：4 个 taxon `Fin 4` ≙ `00,01,10,11`，
字符 `a` 的 1-类 `{2,3}`（`10,11`）、`b` 的 1-类 `{1,3}`（`01,11`）——
`SidesCompatible` **为假**，即 Theorem 1.1 中的四 gamete 反例（`F₂`，`LamGusfieldSridhar2009` 1275–1280 行）。 -/
theorem fourGametes_obstruction :
    ¬ SidesCompatible ({2, 3} : Finset (Fin 4)) {1, 3} := by
  unfold SidesCompatible
  decide

/-- 上面那对字符**确实**含全部四个 gamete：`w=3`(`11`)、`x=2`(`10`)、`y=1`(`01`)、`z=0`(`00`)。 -/
example : ∃ w x y z : Fin 4,
    w ∈ ({2, 3} : Finset (Fin 4)) ∩ {1, 3} ∧
      x ∈ ({2, 3} : Finset (Fin 4)) \ {1, 3} ∧
      y ∈ ({1, 3} : Finset (Fin 4)) \ {2, 3} ∧
      z ∈ (({2, 3} : Finset (Fin 4)) ∪ {1, 3})ᶜ :=
  ⟨3, 2, 1, 0, by decide, by decide, by decide, by decide⟩

/-- **非空真**：相容性不是空话 —— `SidesCompatible` 在具体集合上成立与不成立各有实例。 -/
example : SidesCompatible (∅ : Finset (Fin 3)) {0} :=
  sidesCompatible_of_eq_empty_or_univ (Or.inl rfl)

/-- **非空真**：`HasPerfectPhylogeny` 不是空话 —— 上面那个 2 字符矩阵确实有完美系统发生。 -/
theorem hasPerfectPhylogeny_pair_witness :
    HasPerfectPhylogeny (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) := by
  have h0 : charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 0 = ({0, 1} : Finset (Fin 3)) := by
    ext x
    simp only [charOneClass, mem_binaryFactor, Fin.isValue]
    fin_cases x <;> decide
  have h1 : charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 1 = ({0, 2} : Finset (Fin 3)) := by
    ext x
    simp only [charOneClass, mem_binaryFactor, Fin.isValue]
    fin_cases x <;> decide
  obtain ⟨T, hTA, hTB⟩ := perfectPhylogeny_pair_witness
  refine ⟨T, fun i => ?_⟩
  fin_cases i
  · show DisplaysBinary T (charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 0)
    rw [h0]; exact hTA
  · show DisplaysBinary T (charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 1)
    rw [h1]; exact hTB

/-! ## §5 与 `Phylo/Compatibility.lean`（EJM 树偏序层）的接口 -/

/-- `Bool`（两态）是**树偏序**（全序），故 EJM 的树偏序器材适用于 two-state 字符。 -/
theorem isTreePoset_bool : IsTreePoset Bool := by
  intro a b c _ _
  exact le_total a b

/-! ## §6 缺口（显式 `def … : Prop`，**未证**）

⚠️ 以下两条**只是把目标陈述写清楚**（`def … : Prop`，非 `theorem`，**不引入任何公理**），
以便后续批次对着它们做；**不得**把它们当作已证结论引用。 -/

/-- **顶点集连通**（`SimpleGraph` 上）：`S` 中任意两点可用一条**整条落在 `S` 内**的 walk 相连。

这是 Gusfield 条件 (3)「forms a connected subtree of T」所需的**新词汇**（库内没有）。 -/
def IsConnectedSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ S

/-- **多状态字符的「展示」关系（Gusfield 条件 (3) 的忠实形式化）**：
`χ : X → St` 被 `T` 展示 ⟺ 存在把 `T` **全体顶点**按 `St` 标注的函数 `ℓ`，
使叶上 `ℓ` 与 `χ` 一致、且每个状态的原像在 `T` 中**连通**。

⚠️ 与 `DisplaysBinary`/`IsSideOf` 的关系：对 `|St| = 2` 两者**等价**；
对 `|St| ≥ 3` 「连通」**严格更弱**（`{b,c}` 在毛虫树上连通但非边侧）。 -/
def DisplaysMultiState {St : Type v} (T : Cladogram X) (χ : X → St) : Prop :=
  ∃ ℓ : T.V → St, (∀ x : X, ℓ (T.leaf x) = χ x) ∧
    ∀ s : St, IsConnectedSet T.graph {v | ℓ v = s}

/-- **缺口 G1 —— ✅ 2026-10-17 W22 已收口**（`Phylo.Connectivity` 的
`BinaryConnectedEqualsSideGap_holds`；本 `def` 按纪律**逐字保留**作登记，
故 `scripts/list_gaps.sh` 口径 B 会把它判为「已收口」）。
Gusfield 条件 (3) 的「连通子树」语义对 **r = 2** 与库内
`Cladogram.IsSideOf`（边侧）**一致** —— 即「两个状态类都连通 ⟺ 1-类是某条边的叶侧」。
**缺什么**：~~`IsConnectedSet` 与 `IsSideOf` 之间的树连通性引理（需 `T - e` 的分量分析）~~
⇒ **已补**（W22）：`SimpleGraph.exists_adj_crossing`（跨界 walk 必有跨界边）·
`inSide_of_walk_edges_notMem`（避开 `e` 的 walk ⟹ 同侧）· `compl_inSide`/`compl_inSide'`
（`e` 一侧的补 = 另一端点一侧）· `inSide_iff_of_isConnectedSet`（`⟹` 半引擎）。
★ 实测**不需要**「割边唯一」／圈论证：二分性 `inSide_or_inSide` ＋ 互斥性 `not_inSide_both`
＋「边是桥」`not_reachable_deleteEdges_of_adj` 已足够，全程不出现「圈」。
**为什么**：库内只有「边侧」，而条件 (3) 用的是「连通」，二者的差别正是多状态反例的所在。 -/
def BinaryConnectedEqualsSideGap : Prop :=
  ∀ (T : Cladogram.{u, u} X) (A : Finset X),
    (∃ ℓ : T.V → Bool, (∀ x : X, ℓ (T.leaf x) = true ↔ x ∈ A) ∧
      ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s}) ↔ DisplaysBinary T A

/-- **缺口 G2 —— ✅ 2026-10-21 W26 泳道 e 已收口**（MultiStatePairwiseInsufficiencyGap_holds，文件末尾）：
**多状态时两两相容不充分** —— Fitch–Meacham `F₃`
（5 taxa × 3 字符 × 3 状态：`021, 100, 002, 220, 111`；`LamGusfieldSridhar2009`
1256–1273 行构造、1283–1284 行 `EC1={a0,b2,c1}`/`EC2={a1,b0,c0}`）。

陈述：存在这样的矩阵，使**任意两个**字符都有完美系统发生，而**三个一起**没有。

**文献**：`LamGusfieldSridhar2009` 摘要 48–58 行、**Theorem 2.4**（276–278 行，
`r = 3` 时判据要检查**三元组**而非二元组）、**Theorem 7.1**（1290–1292 行）、Fitch 例（131–140 行）。
**缺什么**：`DisplaysMultiState`（上面已给定义）上的存在/不存在性证明 ——
「不存在」需遍历（同构类下的）全部 `Cladogram`，库内尚无此枚举/不变量。
**为什么**：这正是 two-state（Theorem 1.1）与多状态（Theorem 2.4）的**分界**。 -/
def MultiStatePairwiseInsufficiencyGap : Prop :=
  ∃ M : Fin 3 → Fin 5 → Fin 3,
    (∀ i j : Fin 3, i ≠ j →
      ∃ T : Cladogram.{0, 0} (Fin 5),
        DisplaysMultiState T (M i) ∧ DisplaysMultiState T (M j)) ∧
    ¬ (∃ T : Cladogram.{0, 0} (Fin 5), ∀ i : Fin 3, DisplaysMultiState T (M i))
/-! ### G2 的**反例候选**（`Fitch–Meacham F₃`）与「整体不可解」的**组合内核**

⚠️ 本节**不证明** `MultiStatePairwiseInsufficiencyGap`（缺口本体仍开）。只补两件**器材**：
① 把文献里的 `r = 3` 反例落成具体矩阵 `fitchMeachamF3`；
② 把「整体不可解」中**与树无关**的纯组合内核证掉，好让后续补上唯一缺的那条树引理后一段收口。

文献（`references/md/LamGusfieldSridhar2009_PerfectPhylogenyThreeStateCharactersarXiv0905.1417.md`）：

* **131–136 行**：Fitch 1975 的例子 —— 每**一对**字符都有完美系统发生，整集没有；
* **1256–1273 行**：`F_r` 统一构造（`r + 2` 条序列 × `r` 个字符 × `r` 个状态）；
* **1263–1266 行**：两端团 `EC1`、`EC2`；
* **1283 行**：`r = 3` 时 `EC1 = {a0, b2, c1}`、`EC2 = {a1, b0, c0}`；
* **1290–1292 行**：**Theorem 7.1** —— 任意 `r − 1` 个字符可解、整体不可解。

`r = 3` 的矩阵（**行 = taxon `t₀…t₄`，列 = 字符 `a, b, c`**；由 `EC1`/`EC2` 与三个 tower-clique 读出）：

```
        a  b  c
  t₀    0  2  1
  t₁    1  0  0
  t₂    0  0  2
  t₃    2  2  0
  t₄    1  1  1
```

★ **为什么这个实例可行（分析记录，供补上树引理后收口）**：
5 taxa / 3 状态用鸽笼 ⇒ 每个字符必有一个**单元状态类**（本例三者均为 `(2, 2, 1)` 型）。
于是「`T` 展示该字符」⟺「`T` 的某条边以某个**二元状态类**为叶侧」：

* (⟸) 剪「该二元类为叶侧」的边 ＋ 剪单元类叶子的悬挂边 ⇒ 三个分量恰为三个状态类；
* (⟹) 状态类把 `T.V` 剖成 3 个**连通**块 ⇒ 跨块边数 `= 2`（商图是树）⇒ 三块中**两个**是某条
  边的叶侧 ⇒ 至少一个二元状态类是叶侧。**这一步（商树计数）是本文件尚未形式化的树引理。**

逐字符的候选叶侧（2-元集）：`a: {0,2} / {1,4}`、`b: {1,2} / {0,3}`、`c: {1,3} / {0,4}`。
「两两可解」⟺ 每对字符都能选到一对**不交**候选；「整体不可解」⟺ 无法从每字符选一个候选做到
三三不交 —— 这条纯组合事实正是下面两条定理证掉的东西（配合「`Fin 5` 上两个相交且相异的二元集
`¬ SidesCompatible`」这条一步引理即可收口）。 -/
def fitchMeachamF3 (i : Fin 3) (x : Fin 5) : Fin 3 :=
  if i = 0 then
    (if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 0 else if x = 3 then 2 else 1)
  else if i = 1 then
    (if x = 0 then 2 else if x = 1 then 0 else if x = 2 then 0 else if x = 3 then 2 else 1)
  else
    (if x = 0 then 1 else if x = 1 then 0 else if x = 2 then 2 else if x = 3 then 0 else 1)

/-- **`F₃` 的九个状态类**：确认每个字符恰是 `(2, 2, 1)` 型，且两个二元类就是上面列的候选叶侧
（这是「5 taxa / 3 状态 ⇒ 必有一个单元类」在具体矩阵上的体现）。 -/
theorem fitchMeachamF3_stateClasses :
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 0 x = 0)) = ({0, 2} : Finset (Fin 5)) ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 0 x = 1)) = {1, 4} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 0 x = 2)) = {3} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 1 x = 0)) = {1, 2} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 1 x = 1)) = {4} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 1 x = 2)) = {0, 3} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 2 x = 0)) = {1, 3} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 2 x = 1)) = {0, 4} ∧
    (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 2 x = 2)) = {2} := by
  decide

/-- **「整体不可解」的组合内核**（与树无关）：从 `F₃` 三个字符的候选叶侧里各取一个，
必有一对**相交**；而 `Fin 5` 上两个相交且相异的二元集**不相容**（`SidesCompatible` 的四个析取支
逐一排除：`{0,2} ⊄ {1,2}`、`{1,2} ⊄ {0,2}`、不交为假、并集只有 3 元 `≠ univ`），
故不存在三条边能同时给出这三条叶侧。 -/
theorem fitchMeachamF3_options_meet (A B C : Finset (Fin 5))
    (hA : A = {0, 2} ∨ A = {1, 4}) (hB : B = {1, 2} ∨ B = {0, 3})
    (hC : C = {1, 3} ∨ C = {0, 4}) :
    A ∩ B ≠ ∅ ∨ A ∩ C ≠ ∅ ∨ B ∩ C ≠ ∅ := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> rcases hC with rfl | rfl <;> decide

/-- 上一条的否定形（**两两不交不可能**）：`MultiStatePairwiseInsufficiencyGap` 的「整体不可解」
那一半，在树引理补上之后，唯一剩下的组合障碍就是这条。 -/
theorem fitchMeachamF3_no_pairwise_disjoint (A B C : Finset (Fin 5))
    (hA : A = {0, 2} ∨ A = {1, 4}) (hB : B = {1, 2} ∨ B = {0, 3})
    (hC : C = {1, 3} ∨ C = {0, 4}) :
    ¬ (A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅) := by
  rintro ⟨h1, h2, h3⟩
  rcases fitchMeachamF3_options_meet A B C hA hB hC with h | h | h
  · exact h h1
  · exact h h2
  · exact h h3

/-! ### G2 的**树引理**（W26 泳道 e）：状态类纤维 ⇒ 二元类是某条边的叶侧

W25 已把 `MultiStatePairwiseInsufficiencyGap` 的「整体不可解」半里**与树无关**的组合内核
证掉（上面 `fitchMeachamF3_options_meet` / `fitchMeachamF3_no_pairwise_disjoint`）。
本节补上**唯一缺的树侧器材**，并把该半**整条收口**为定理 `not_exists_displays_all_fitchMeachamF3`。

**要证的树引理**：若 `T` 展示 `F₃` 的第 `i` 个字符（`DisplaysMultiState`：存在 `ℓ : T.V → Fin 3`，
三个状态类都**连通**且叶上等于 `χ`），则其两个**二元**状态类中**至少一个**是 `T` 某条边的
**叶侧**（`Cladogram.sideLeaves`）。

★ **为什么不走「商树计数」**（W25 备忘的路线：三块连通 ⇒ 跨块边 = 类数 − 1 ⇒ 商图是树）：
那条路线要数 `|E| = |V| - 1` 与「诱导子图是树」（`SimpleGraph.IsTree.card_edgeFinset`
＋边集分划记账），代价高。**等价而更短**的路线只用两条初等事实：

1. **有边则并连通**：两块连通集若之间有边，则并集连通（两条 walk 用该边接起来）；
2. **并连通则有边**：并集连通则两块之间**必**有边（跨界 walk 必有跨界边）。

于是三块 `C_p, C_q, C_r` 连通时：若 `C_p ∪ C_r` 与 `C_q ∪ C_r` **都**不连通，则 `C_r` 与
`C_p`、`C_r` 与 `C_q` 之间都没有边 ⇒ `C_r` 的邻居全在 `C_r` 内 ⇒ `C_r` 对邻接封闭 ⇒
（沿 walk 归纳，用 `T` 连通）`C_r = univ`；但 `C_p` 含叶（`T.leaf x_p`）而 `ℓ` 在该叶上
`= p ≠ r`，矛盾。故 `C_p ∪ C_r` 或 `C_q ∪ C_r` 连通 —— 即某个**二元类**的**补也连通**。

最后一步：若 `C` 与 `Cᶜ` 都连通，取跨界边 `x—y`（`x ∈ C`, `y ∉ C`），则
`C = {z | T.inSide s(x,y) z x}`（两侧各用「连通 walk 绕开 `x—y`」，再用「边是桥」
`not_reachable_deleteEdges_of_adj` 收口；与 `Phylo.Connectivity` 的
`inSide_iff_of_isConnectedSet` 同一论证），于是 `T.sideLeaves s(x,y) x = filter (χ · = s)`。

⚠️ **import 方向**：`Phylo/Connectivity.lean` **import 本文件**，故本文件用不到它的
`SimpleGraph.exists_adj_crossing` / `inSide_iff_of_isConnectedSet`。下面 `MultiStateTree`
命名空间前置这两件**最小**引擎（论证与下游同源，命名避开了下游的同名声明）；
其余一律复用 `Phylo/Split.lean` 的 `sideLeaves` / `inSide` / `not_reachable_deleteEdges_of_adj` /
`sidesCompatible_sideLeaves`。 -/

namespace MultiStateTree

omit [Fintype X] [DecidableEq X] in
/-- ★ **跨界 walk 必有跨界边**（`Walk.recOn` 一次归纳；与 `Phylo.Connectivity` 的
`SimpleGraph.exists_adj_crossing` 同一论证 —— 该文件 import 本文件，故此处前置一份）。 -/
theorem exists_adj_crossing {V : Type*} {G : SimpleGraph V} {U : Set V} {a b : V}
    (p : G.Walk a b) (ha : a ∈ U) (hb : b ∉ U) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ x ∈ U ∧ y ∉ U := by
  refine Walk.recOn (motive := fun u v q => u ∈ U → v ∉ U →
      ∃ x ∈ q.support, ∃ y ∈ q.support, G.Adj x y ∧ x ∈ U ∧ y ∉ U) p ?_ ?_ ha hb
  · intro u hu hnu
    exact absurd hu hnu
  · intro u v ww hadj q ih hu hnw
    by_cases hc : v ∈ U
    · obtain ⟨x, hx, y, hy, hadj', hxU, hyU⟩ := ih hc hnw
      exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hadj', hxU, hyU⟩
    · exact ⟨u, Walk.start_mem_support _, v, List.mem_cons_of_mem _ (Walk.start_mem_support q),
        hadj, hu, hc⟩

omit [Fintype X] [DecidableEq X] in
/-- ★ **避开边 `e` 的 walk 落在 `T - e` 里** ⟹ `u` 与 `v` 同侧（`Walk.toDeleteEdge`）。 -/
theorem inSide_of_walk_edges_notMem (T : Cladogram.{u, u} X) {e : Sym2 T.V} {u v : T.V}
    (p : T.graph.Walk u v) (h : e ∉ p.edges) : T.inSide e u v :=
  (p.toDeleteEdge e h).reachable

omit [Fintype X] [DecidableEq X] in
/-- ★ **两块连通 + 之间有边 ⇒ 并集连通**（两条 walk 用该边 `cons`/`append` 接起来）。 -/
theorem isConnectedSet_union_of_adj (T : Cladogram.{u, u} X) {A B : Set T.V}
    (hA : IsConnectedSet T.graph A) (hB : IsConnectedSet T.graph B)
    {x y : T.V} (hxy : T.graph.Adj x y) (hxA : x ∈ A) (hyB : y ∈ B) :
    IsConnectedSet T.graph (A ∪ B) := by
  intro u hu v hv
  rw [Set.mem_union] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · obtain ⟨p, hp⟩ := hA u hu v hv
    exact ⟨p, fun w hw => Or.inl (hp w hw)⟩
  · obtain ⟨p, hp⟩ := hA u hu x hxA
    obtain ⟨q, hq⟩ := hB y hyB v hv
    refine ⟨p.append (Walk.cons hxy q), fun w hw => ?_⟩
    rw [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · exact Or.inl (hp w hw)
    · rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with hwx | hw
      · rw [hwx]; exact Or.inl hxA
      · exact Or.inr (hq w hw)
  · obtain ⟨p, hp⟩ := hB u hu y hyB
    obtain ⟨q, hq⟩ := hA x hxA v hv
    refine ⟨p.append (Walk.cons hxy.symm q), fun w hw => ?_⟩
    rw [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · exact Or.inr (hp w hw)
    · rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with hwy | hw
      · rw [hwy]; exact Or.inr hyB
      · exact Or.inl (hq w hw)
  · obtain ⟨p, hp⟩ := hB u hu v hv
    exact ⟨p, fun w hw => Or.inr (hp w hw)⟩

omit [Fintype X] [DecidableEq X] in
/-- ★ **并集连通 ⇒ 两块之间有边**（跨界 walk 必有跨界边）。 -/
theorem exists_adj_between (T : Cladogram.{u, u} X) {A B : Set T.V}
    (hdisj : ∀ z : T.V, z ∈ A → z ∈ B → False)
    (h : IsConnectedSet T.graph (A ∪ B)) {u v : T.V} (hu : u ∈ A) (hv : v ∈ B) :
    ∃ x ∈ A, ∃ y ∈ B, T.graph.Adj x y := by
  have hvA : v ∉ A := fun hv' => hdisj v hv' hv
  obtain ⟨p, hp⟩ := h u (Or.inl hu) v (Or.inr hv)
  obtain ⟨x, hx, y, hy, hadj, hxA, hyA⟩ := exists_adj_crossing p hu hvA
  exact ⟨x, hxA, y, (hp y hy).resolve_left hyA, hadj⟩

/-- ★★ **`C` 与 `Cᶜ` 都连通 ⟹ `C` 恰是跨界边 `x—y` 的 `x` 一侧**。

（与 `Phylo.Connectivity` 的 `inSide_iff_of_isConnectedSet` 同一论证，此处以 `Set` 表述，
省掉 `Bool` 纤维的来回换算：`→` 用 `C` 的连通 walk，`←` 用 `Cᶜ` 的连通 walk，两侧都绕开 `x—y`。） -/
theorem inSide_iff_mem_of_isConnectedSet (T : Cladogram.{u, u} X) {C : Set T.V}
    (hC : IsConnectedSet T.graph C) (hCc : IsConnectedSet T.graph Cᶜ)
    {x y : T.V} (hxy : T.graph.Adj x y) (hx : x ∈ C) (hy : y ∉ C) :
    ∀ z : T.V, (z ∈ C ↔ T.inSide s(x, y) z x) := by
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := hC z hz x hx
    have hnot : s(x, y) ∉ p.edges := by
      intro hmem
      have hy' : y ∈ p.support :=
        Walk.mem_support_of_mem_edges hmem (by rw [Sym2.mem_iff]; exact Or.inr rfl)
      exact hy (hp y hy')
    exact inSide_of_walk_edges_notMem T p hnot
  · intro hz
    by_contra hzc
    have hzc' : z ∈ Cᶜ := hzc
    obtain ⟨q, hq⟩ := hCc z hzc' y hy
    have hnot : s(x, y) ∉ q.edges := by
      intro hmem
      have hx' : x ∈ q.support :=
        Walk.mem_support_of_mem_edges hmem (by rw [Sym2.mem_iff]; exact Or.inl rfl)
      exact (hq x hx') hx
    have hzy : T.inSide s(x, y) z y := inSide_of_walk_edges_notMem T q hnot
    exact T.not_reachable_deleteEdges_of_adj hxy (((T.inSide_comm _ _ _).mp hz).trans hzy)

/-- **若 `C` 的补也连通，则 `C` 是某条边的叶侧**（以 `inSide` 刻画给出）。 -/
theorem exists_inSide_iff_of_compl_connected (T : Cladogram.{u, u} X) (C : Set T.V)
    (hC : IsConnectedSet T.graph C) (hCc : IsConnectedSet T.graph Cᶜ)
    {u v : T.V} (hu : u ∈ C) (hv : v ∉ C) :
    ∃ (a b : T.V) (_ : T.graph.Adj a b) (w : T.V),
      ∀ z : T.V, (z ∈ C ↔ T.inSide s(a, b) z w) := by
  obtain ⟨p⟩ := T.isTree.connected u v
  obtain ⟨x, -, y, -, hxy, hxC, hyC⟩ := exists_adj_crossing p hu hv
  exact ⟨x, y, hxy, x, inSide_iff_mem_of_isConnectedSet T hC hCc hxy hxC hyC⟩

/-- `Fin 3` 的三分（`Fin` 上没有 `omega`；`fin_cases` 一次拆完）。 -/
theorem fin_three_cases (s : Fin 3) : s = 0 ∨ s = 1 ∨ s = 2 := by
  fin_cases s <;> simp

/-- 把「`C` 是边侧」落到 `Finset`：`sideLeaves` = 状态滤波器。 -/
theorem sideLeaves_eq_filter_of_iff (T : Cladogram.{0, 0} (Fin 5)) (ℓ : T.V → Fin 3)
    (s : Fin 3) {a b w : T.V}
    (hiff : ∀ z : T.V, (z ∈ {v : T.V | ℓ v = s} ↔ T.inSide s(a, b) z w)) :
    T.sideLeaves s(a, b) w = Finset.univ.filter (fun x : Fin 5 => ℓ (T.leaf x) = s) := by
  ext x
  rw [T.mem_sideLeaves_iff_inSide, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_univ _, (hiff (T.leaf x)).mpr ((T.inSide_comm _ _ _).mpr h)⟩
  · rintro ⟨-, h⟩
    exact (T.inSide_comm _ _ _).mp ((hiff (T.leaf x)).mp h)

/-- ★★ **三块连通纤维（状态 `p, q, r`）：`{ℓ=p} ∪ {ℓ=r}` 或 `{ℓ=q} ∪ {ℓ=r}` 必有一个连通**
（即「某个二元类的补也连通」）。证明路线见本节开头。 -/
theorem union_pq_or_pr (T : Cladogram.{0, 0} (Fin 5)) (ℓ : T.V → Fin 3) (p q r : Fin 3)
    (hpr : p ≠ r) (htri : ∀ s : Fin 3, s = p ∨ s = q ∨ s = r)
    (hcon : ∀ s : Fin 3, IsConnectedSet T.graph {v : T.V | ℓ v = s})
    (hp : ∃ x : Fin 5, ℓ (T.leaf x) = p) (hr : ∃ x : Fin 5, ℓ (T.leaf x) = r) :
    IsConnectedSet T.graph ({v : T.V | ℓ v = p} ∪ {v : T.V | ℓ v = r}) ∨
      IsConnectedSet T.graph ({v : T.V | ℓ v = q} ∪ {v : T.V | ℓ v = r}) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hA, hB⟩ := h
  obtain ⟨xp, hxp⟩ := hp
  obtain ⟨xr, hxr⟩ := hr
  have hnoA : ∀ x : T.V, ℓ x = p → ∀ y : T.V, ℓ y = r → ¬ T.graph.Adj x y := by
    intro x hx y hy hadj
    exact hA (isConnectedSet_union_of_adj T (hcon p) (hcon r) hadj hx hy)
  have hnoB : ∀ x : T.V, ℓ x = q → ∀ y : T.V, ℓ y = r → ¬ T.graph.Adj x y := by
    intro x hx y hy hadj
    exact hB (isConnectedSet_union_of_adj T (hcon q) (hcon r) hadj hx hy)
  have hclosed : ∀ v : T.V, ℓ v = r → ∀ w : T.V, T.graph.Adj v w → ℓ w = r := by
    intro v hv w hadj
    rcases htri (ℓ w) with h | h | h
    · exact absurd hadj.symm (hnoA w h v hv)
    · exact absurd hadj.symm (hnoB w h v hv)
    · exact h
  have hreach : ∀ v : T.V, T.graph.Reachable (T.leaf xr) v → ℓ v = r := by
    intro v hr'
    obtain ⟨w⟩ := hr'
    refine Walk.recOn (motive := fun u v _ => ℓ u = r → ℓ v = r) w ?_ ?_ hxr
    · intro u hu
      exact hu
    · intro u v ww hadj q ih hu
      exact ih (hclosed u hu v hadj)
  have hall : ℓ (T.leaf xp) = r :=
    hreach (T.leaf xp) (T.isTree.connected (T.leaf xr) (T.leaf xp))
  rw [hxp] at hall
  exact hpr hall

/-- ★★★ **树引理（G2 收口用）**：展示 `F₃` 第 `i` 个字符的树上，其两个**二元**状态类
（状态 `p` 与 `q`；`r` 是单元类）中**至少一个**是某条边的叶侧。 -/
theorem exists_binary_side_of_display (T : Cladogram.{0, 0} (Fin 5)) (i : Fin 3)
    (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hrq : r ≠ q)
    (htri : ∀ s : Fin 3, s = p ∨ s = q ∨ s = r)
    (ℓ : T.V → Fin 3) (hleaf : ∀ x : Fin 5, ℓ (T.leaf x) = fitchMeachamF3 i x)
    (hcon : ∀ s : Fin 3, IsConnectedSet T.graph {v : T.V | ℓ v = s}) :
    ∃ (a b : T.V) (_ : T.graph.Adj a b) (w : T.V),
      T.sideLeaves s(a, b) w = Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 i x = p) ∨
      T.sideLeaves s(a, b) w = Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 i x = q) := by
  have hex : ∀ s : Fin 3, ∃ x : Fin 5, fitchMeachamF3 i x = s := by
    intro s
    fin_cases i <;> fin_cases s <;> decide
  have hp : ∃ x : Fin 5, ℓ (T.leaf x) = p := by
    obtain ⟨x, hx⟩ := hex p
    exact ⟨x, by rw [hleaf]; exact hx⟩
  have hq : ∃ x : Fin 5, ℓ (T.leaf x) = q := by
    obtain ⟨x, hx⟩ := hex q
    exact ⟨x, by rw [hleaf]; exact hx⟩
  have hr : ∃ x : Fin 5, ℓ (T.leaf x) = r := by
    obtain ⟨x, hx⟩ := hex r
    exact ⟨x, by rw [hleaf]; exact hx⟩
  have hpp : ∃ x : Fin 5, ℓ (T.leaf x) = p := hp
  have hrr : ∃ x : Fin 5, ℓ (T.leaf x) = r := hr
  obtain ⟨xp, hxp⟩ := hp
  obtain ⟨xq, hxq⟩ := hq
  obtain ⟨xr, hxr⟩ := hr
  have hfilter : ∀ s : Fin 3,
      Finset.univ.filter (fun x : Fin 5 => ℓ (T.leaf x) = s) =
        Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 i x = s) := by
    intro s
    refine Finset.filter_congr ?_
    intro x _
    rw [hleaf x]
  have hsetq : ({v : T.V | ℓ v = q}ᶜ : Set T.V) = {v : T.V | ℓ v = p} ∪ {v : T.V | ℓ v = r} := by
    ext z
    show ¬ (ℓ z = q) ↔ (ℓ z = p ∨ ℓ z = r)
    constructor
    · intro hz
      rcases htri (ℓ z) with h | h | h
      · exact Or.inl h
      · exact absurd h hz
      · exact Or.inr h
    · rintro (h | h) hz
      · exact hpq (h.symm.trans hz)
      · exact hrq (h.symm.trans hz)
  have hsetp : ({v : T.V | ℓ v = p}ᶜ : Set T.V) = {v : T.V | ℓ v = q} ∪ {v : T.V | ℓ v = r} := by
    ext z
    show ¬ (ℓ z = p) ↔ (ℓ z = q ∨ ℓ z = r)
    constructor
    · intro hz
      rcases htri (ℓ z) with h | h | h
      · exact absurd h hz
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h) hz
      · exact hpq (hz.symm.trans h)
      · exact hpr (hz.symm.trans h)
  rcases union_pq_or_pr T ℓ p q r hpr htri hcon hpp hrr with hA | hA
  · -- `{ℓ=p} ∪ {ℓ=r}` 连通 ⇒ `{ℓ=q}` 的补连通 ⇒ 状态 `q` 类是边侧
    have hCc : IsConnectedSet T.graph ({v : T.V | ℓ v = q}ᶜ) := by
      rw [hsetq]; exact hA
    have hvp : T.leaf xp ∉ ({v : T.V | ℓ v = q} : Set T.V) := by
      intro h
      change ℓ (T.leaf xp) = q at h
      rw [hxp] at h
      exact hpq h
    obtain ⟨a, b, hab, w, hiff⟩ :=
      exists_inSide_iff_of_compl_connected T {v : T.V | ℓ v = q} (hcon q) hCc
        (u := T.leaf xq) (v := T.leaf xp) hxq hvp
    refine ⟨a, b, hab, w, Or.inr ?_⟩
    rw [sideLeaves_eq_filter_of_iff T ℓ q hiff, hfilter q]
  · -- `{ℓ=q} ∪ {ℓ=r}` 连通 ⇒ `{ℓ=p}` 的补连通 ⇒ 状态 `p` 类是边侧
    have hCc : IsConnectedSet T.graph ({v : T.V | ℓ v = p}ᶜ) := by
      rw [hsetp]; exact hA
    have hvq : T.leaf xq ∉ ({v : T.V | ℓ v = p} : Set T.V) := by
      intro h
      change ℓ (T.leaf xq) = p at h
      rw [hxq] at h
      exact hpq h.symm
    obtain ⟨a, b, hab, w, hiff⟩ :=
      exists_inSide_iff_of_compl_connected T {v : T.V | ℓ v = p} (hcon p) hCc
        (u := T.leaf xp) (v := T.leaf xq) hxp hvq
    refine ⟨a, b, hab, w, Or.inl ?_⟩
    rw [sideLeaves_eq_filter_of_iff T ℓ p hiff, hfilter p]

/-! #### 组合收口：三个二元叶侧两两 `SidesCompatible`，但与 `F₃` 的候选集矛盾 -/

/-- `Fin 5` 上两个**二元**集若相交且相异，则**不相容**（`SidesCompatible` 四支逐一排除）。 -/
theorem not_sidesCompatible_of_binary_meet {A B : Finset (Fin 5)}
    (hA : A.card = 2) (hB : B.card = 2) (hne : A ≠ B) (hmeet : A ∩ B ≠ ∅) :
    ¬ SidesCompatible A B := by
  intro h
  unfold SidesCompatible at h
  rcases h with h | h | h | h
  · exact hne (Finset.eq_of_subset_of_card_le h (by omega))
  · exact hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
  · exact hmeet (Finset.disjoint_iff_inter_eq_empty.mp h)
  · have h1 : (A ∪ B).card = 5 := by rw [h, Finset.card_univ]; simp
    have h2 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
    omega

/-- 候选叶侧集的基数都是 2（`a` 列）。 -/
theorem card_two_of_optionA {A : Finset (Fin 5)} (h : A = {0, 2} ∨ A = {1, 4}) :
    A.card = 2 := by
  rcases h with h | h <;> rw [h] <;> decide

/-- 候选叶侧集的基数都是 2（`b` 列）。 -/
theorem card_two_of_optionB {B : Finset (Fin 5)} (h : B = {1, 2} ∨ B = {0, 3}) :
    B.card = 2 := by
  rcases h with h | h <;> rw [h] <;> decide

/-- 候选叶侧集的基数都是 2（`c` 列）。 -/
theorem card_two_of_optionC {C : Finset (Fin 5)} (h : C = {1, 3} ∨ C = {0, 4}) :
    C.card = 2 := by
  rcases h with h | h <;> rw [h] <;> decide

/-- 不同字符的候选叶侧**必不相等**（三列候选两两无交集）。 -/
theorem optionA_ne_optionB {A B : Finset (Fin 5)} (hA : A = {0, 2} ∨ A = {1, 4})
    (hB : B = {1, 2} ∨ B = {0, 3}) : A ≠ B := by
  intro hAB
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB] at hAB
  all_goals exact absurd hAB (by decide)

/-- 不同字符的候选叶侧**必不相等**。 -/
theorem optionA_ne_optionC {A C : Finset (Fin 5)} (hA : A = {0, 2} ∨ A = {1, 4})
    (hC : C = {1, 3} ∨ C = {0, 4}) : A ≠ C := by
  intro hAC
  rcases hA with hA | hA <;> rcases hC with hC | hC <;> rw [hA, hC] at hAC
  all_goals exact absurd hAC (by decide)

/-- 不同字符的候选叶侧**必不相等**。 -/
theorem optionB_ne_optionC {B C : Finset (Fin 5)} (hB : B = {1, 2} ∨ B = {0, 3})
    (hC : C = {1, 3} ∨ C = {0, 4}) : B ≠ C := by
  intro hBC
  rcases hB with hB | hB <;> rcases hC with hC | hC <;> rw [hB, hC] at hBC
  all_goals exact absurd hBC (by decide)

end MultiStateTree

open MultiStateTree in
/-- ★★★★ **`MultiStatePairwiseInsufficiencyGap` 的「整体不可解」半（`F₃` 实例）**

`fitchMeachamF3` 的三个字符**同时**被一棵 `Cladogram (Fin 5)` 展示是**不可能**的
（Gusfield 条件 (3) 的「连通子树」语义）。证明链：

1. 逐字符取树引理 `exists_binary_side_of_display`：每个字符有一个**二元状态类是边侧**；
2. 同一棵树上三条边侧两两 `SidesCompatible`（`Cladogram.sidesCompatible_sideLeaves`）；
3. 但 `F₃` 的三列候选叶侧**任取三个必有一对相交**（`fitchMeachamF3_options_meet`），
   而 `Fin 5` 上相交且相异的二元集**不相容**（`not_sidesCompatible_of_binary_meet`）—— 矛盾。

⇒ 这就是 `MultiStatePairwiseInsufficiencyGap` 里的第二个合取项（取 `M := fitchMeachamF3`）；
缺口本体还差**两两可解**那一半（每对字符的一棵具体 `Cladogram`，需 `Cladogram` 构造 + 展示证明）。 -/
theorem not_exists_displays_all_fitchMeachamF3 :
    ¬ (∃ T : Cladogram.{0, 0} (Fin 5), ∀ i : Fin 3, DisplaysMultiState T (fitchMeachamF3 i)) := by
  rintro ⟨T, hdisp⟩
  obtain ⟨ℓ0, hleaf0, hcon0⟩ := hdisp 0
  obtain ⟨ℓ1, hleaf1, hcon1⟩ := hdisp 1
  obtain ⟨ℓ2, hleaf2, hcon2⟩ := hdisp 2
  have e00 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 0 x = 0)) = ({0, 2} : Finset (Fin 5)) :=
    fitchMeachamF3_stateClasses.1
  have e01 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 0 x = 1)) = {1, 4} :=
    fitchMeachamF3_stateClasses.2.1
  have e10 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 1 x = 0)) = {1, 2} :=
    fitchMeachamF3_stateClasses.2.2.2.1
  have e12 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 1 x = 2)) = {0, 3} :=
    fitchMeachamF3_stateClasses.2.2.2.2.2.1
  have e20 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 2 x = 0)) = {1, 3} :=
    fitchMeachamF3_stateClasses.2.2.2.2.2.2.1
  have e21 : (Finset.univ.filter (fun x : Fin 5 => fitchMeachamF3 2 x = 1)) = {0, 4} :=
    fitchMeachamF3_stateClasses.2.2.2.2.2.2.2.1
  obtain ⟨a0, b0, hab0, w0, h0⟩ :=
    exists_binary_side_of_display T 0 0 1 2 (by decide) (by decide) (by decide) (by decide)
      ℓ0 hleaf0 hcon0
  obtain ⟨a1, b1, hab1, w1, h1⟩ :=
    exists_binary_side_of_display T 1 0 2 1 (by decide) (by decide) (by decide) (by decide)
      ℓ1 hleaf1 hcon1
  obtain ⟨a2, b2, hab2, w2, h2⟩ :=
    exists_binary_side_of_display T 2 0 1 2 (by decide) (by decide) (by decide) (by decide)
      ℓ2 hleaf2 hcon2
  have hAopt : T.sideLeaves s(a0, b0) w0 = {0, 2} ∨ T.sideLeaves s(a0, b0) w0 = {1, 4} := by
    rcases h0 with h | h
    · left; rw [h, e00]
    · right; rw [h, e01]
  have hBopt : T.sideLeaves s(a1, b1) w1 = {1, 2} ∨ T.sideLeaves s(a1, b1) w1 = {0, 3} := by
    rcases h1 with h | h
    · left; rw [h, e10]
    · right; rw [h, e12]
  have hCopt : T.sideLeaves s(a2, b2) w2 = {1, 3} ∨ T.sideLeaves s(a2, b2) w2 = {0, 4} := by
    rcases h2 with h | h
    · left; rw [h, e20]
    · right; rw [h, e21]
  have hAB : SidesCompatible (T.sideLeaves s(a0, b0) w0) (T.sideLeaves s(a1, b1) w1) :=
    T.sidesCompatible_sideLeaves hab0 hab1 w0 w1
  have hAC : SidesCompatible (T.sideLeaves s(a0, b0) w0) (T.sideLeaves s(a2, b2) w2) :=
    T.sidesCompatible_sideLeaves hab0 hab2 w0 w2
  have hBC : SidesCompatible (T.sideLeaves s(a1, b1) w1) (T.sideLeaves s(a2, b2) w2) :=
    T.sidesCompatible_sideLeaves hab1 hab2 w1 w2
  rcases fitchMeachamF3_options_meet (T.sideLeaves s(a0, b0) w0) (T.sideLeaves s(a1, b1) w1)
    (T.sideLeaves s(a2, b2) w2) hAopt hBopt hCopt with hm | hm | hm
  · exact not_sidesCompatible_of_binary_meet (card_two_of_optionA hAopt)
      (card_two_of_optionB hBopt) (optionA_ne_optionB hAopt hBopt) hm hAB
  · exact not_sidesCompatible_of_binary_meet (card_two_of_optionA hAopt)
      (card_two_of_optionC hCopt) (optionA_ne_optionC hAopt hCopt) hm hAC
  · exact not_sidesCompatible_of_binary_meet (card_two_of_optionB hBopt)
      (card_two_of_optionC hCopt) (optionB_ne_optionC hBopt hCopt) hm hBC

namespace MultiStateTree

/-- ★ **一条边的一侧连通**（`Phylo/Connectivity.lean` 的 `inSide_isConnectedSet` 的**前置副本**：
该文件 **import 本文件**，故此处不能引用它）。 -/
theorem inSide_isConnectedSet (T : Cladogram.{u, u} X) (e : Sym2 T.V) (u : T.V) :
    IsConnectedSet T.graph {v | T.inSide e u v} := by
  intro u' hu' v' hv'
  obtain ⟨r⟩ := ((T.inSide_comm e u u').mp hu').trans hv'
  refine ⟨r.mapLe (SimpleGraph.deleteEdges_le {e}), ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro w hw
  exact hu'.trans (SimpleGraph.reachable_of_mem_support r hw)

/-- ★ **`e` 一侧的补恰是另一端点一侧**（`Phylo/Connectivity.lean` 的 `compl_inSide` 的前置副本）。 -/
theorem compl_inSide (T : Cladogram.{u, u} X) {a b u : T.V} (hab : T.graph.Adj a b)
    (hua : T.inSide s(a, b) u a) :
    {v : T.V | ¬ T.inSide s(a, b) u v} = {v : T.V | T.inSide s(a, b) b v} := by
  ext v
  constructor
  · intro hv
    rcases T.inSide_or_inSide hab (x := v) with h | h
    · exact absurd (hua.trans ((T.inSide_comm _ _ _).mp h)) hv
    · exact (T.inSide_comm _ _ _).mp h
  · intro hv hu
    exact T.not_inSide_both hab
      ⟨(T.inSide_comm _ _ _).mp hua, hv.trans ((T.inSide_comm _ _ _).mp hu)⟩

omit [Fintype X] [DecidableEq X] in
/-- **单点集连通**（唯一的 walk 是 `nil`）。 -/
theorem isConnectedSet_singleton (T : Cladogram.{u, u} X) (w : T.V) :
    IsConnectedSet T.graph ({w} : Set T.V) := by
  intro u hu v hv
  rw [Set.mem_singleton_iff] at hu hv
  subst hu
  subst hv
  exact ⟨Walk.nil, by intro z hz; simpa using hz⟩

omit [Fintype X] [DecidableEq X] in
/-- **度 1 顶点的邻居唯一**（叶只有唯一邻居）。 -/
theorem eq_of_adj_of_degree_one (T : Cladogram.{u, u} X) {v a b : T.V}
    (h : T.graph.degree v = 1) (ha : T.graph.Adj v a) (hb : T.graph.Adj v b) : a = b := by
  obtain ⟨w, -, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h
  rw [huniq a ha, huniq b hb]

omit [Fintype X] [DecidableEq X] in
/-- ★ **简单路不过叶的「内部」**：`T.leaf x` 既不是起点也不是终点 ⟹ 它不在路的支持集里。

（若 `T.leaf x` 出现在路中间，则路在该点用了两条**不同**的边；但叶的度是 1，
两条边必是同一端点矛盾 —— 内层 `Walk.recOn` 把「路的第二步」显式展开。） -/
theorem leaf_notMem_support_of_isPath (T : Cladogram.{u, u} X) {x : X} {u v : T.V}
    (q : T.graph.Walk u v) (hq : q.IsPath) (hu : u ≠ T.leaf x) (hv : v ≠ T.leaf x) :
    T.leaf x ∉ q.support := by
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    Cladogram.IsLeaf.degree_eq_one (T := T) (v := T.leaf x) ⟨x, rfl⟩
  have key : ∀ {a b : T.V} (r : T.graph.Walk a b), r.IsPath → a ≠ T.leaf x →
      b ≠ T.leaf x → T.leaf x ∉ r.support := by
    intro a b r
    refine Walk.recOn (motive := fun a b r => r.IsPath → a ≠ T.leaf x → b ≠ T.leaf x →
      T.leaf x ∉ r.support) r ?_ ?_
    · intro a' _ ha' _
      simp only [Walk.support_nil, List.mem_singleton]
      exact ha'.symm
    · intro a' w' b' hadj r' ih hp ha' hb'
      rw [Walk.support_cons]
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact ha' heq.symm
      · by_cases hw : w' = T.leaf x
        · subst hw
          have hnotu : a' ∉ r'.support := ((Walk.cons_isPath_iff hadj r').mp hp).2
          have hinner : ∀ {c d : T.V} (s : T.graph.Walk c d), s.IsPath → c = T.leaf x →
              d ≠ T.leaf x → a' ∉ s.support → False := by
            intro c d s
            refine Walk.recOn (motive := fun c d s => s.IsPath → c = T.leaf x →
              d ≠ T.leaf x → a' ∉ s.support → False) s ?_ ?_
            · intro c' _ hc' hd' _
              exact hd' hc'
            · intro c' w2 d' hadj2 s' _ _ hc' hd' hnot
              have ha2 : T.graph.Adj (T.leaf x) w2 := by rw [← hc']; exact hadj2
              have hw2 : w2 = a' := eq_of_adj_of_degree_one T hdeg ha2 hadj.symm
              have hmem2 : a' ∈ s'.support := by
                rw [← hw2]
                exact s'.start_mem_support
              exact hnot (by
                rw [Walk.support_cons]
                exact List.mem_cons_of_mem _ hmem2)
          exact hinner r' ((Walk.cons_isPath_iff hadj r').mp hp).1 rfl hb' hnotu
        · exact ih ((Walk.cons_isPath_iff hadj r').mp hp).1 hw hb' hmem'
  exact key q hq hu hv

omit [Fintype X] [DecidableEq X] in
/-- ★★ **叶不是割点**：连通的 `S` 去掉其中的一片叶 `T.leaf x` 仍连通。

**证明**：`S` 连通给出行走在 `S` 里的 walk；用 `Walk.bypass` 约成**简单路**（支持集只减不增），
再由 `leaf_notMem_support_of_isPath` 该路不含 `T.leaf x`（端点都不是它）⇒ 支持集落在
`S ∖ {T.leaf x}` 里。 -/
theorem isConnectedSet_sdiff_leaf (T : Cladogram.{u, u} X) {S : Set T.V}
    (hS : IsConnectedSet T.graph S) {x : X} (_hx : T.leaf x ∈ S) :
    IsConnectedSet T.graph (S \ {T.leaf x}) := by
  intro u hu v hv
  have huS : u ∈ S := hu.1
  have hvS : v ∈ S := hv.1
  have hux : u ≠ T.leaf x := fun h => hu.2 (by simp [h])
  have hvx : v ≠ T.leaf x := fun h => hv.2 (by simp [h])
  obtain ⟨p, hp⟩ := hS u huS v hvS
  have hsub : ∀ w : T.V, w ∈ p.bypass.support → w ∈ S := fun w hw =>
    hp w (Walk.support_bypass_subset_support p hw)
  have hnot : T.leaf x ∉ p.bypass.support :=
    leaf_notMem_support_of_isPath T p.bypass p.bypass_isPath hux hvx
  refine ⟨p.bypass, fun w hw => ⟨hsub w hw, fun hw' => hnot (hw' ▸ hw)⟩⟩

/-- ★★★ **单字符展示引擎**：`χ` 是 `(2,2,1)` 型（`p` 类 `A` 是**边侧**、`r` 类单元在 `x₀`、
`q` 类是剩下的二元类），则 `T` 展示 `χ`。

标注：`p` 取在 `a` 侧，`r` 取在 `T.leaf x₀`，`q` 取在「补侧去掉 `T.leaf x₀`」。三个纤维连通性：
`inSide_isConnectedSet` / `isConnectedSet_singleton` / `isConnectedSet_sdiff_leaf`（＋`compl_inSide`）。 -/
theorem displaysMultiState_of_side (T : Cladogram.{u, u} X) (χ : X → Fin 3)
    (p q r : Fin 3) (x0 : X) (A : Finset X) {a b : T.V} (hab : T.graph.Adj a b)
    (hside : A = T.sideLeaves s(a, b) a) (hx0side : x0 ∉ T.sideLeaves s(a, b) a)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (htri : ∀ s : Fin 3, s = p ∨ s = q ∨ s = r)
    (hx0 : χ x0 = r) (huniq : ∀ x : X, χ x = r → x = x0)
    (hpA : ∀ x : X, x ∈ A ↔ χ x = p)
    (hval : ∀ x : X, χ x = p ∨ χ x = q ∨ χ x = r) :
    DisplaysMultiState T χ := by
  classical
  have hside' : ∀ x : X, x ∈ A ↔ T.inSide s(a, b) a (T.leaf x) := by
    intro x
    rw [hside, T.mem_sideLeaves_iff_inSide]
  have hx0notin : ¬ T.inSide s(a, b) a (T.leaf x0) := by
    intro hin
    exact hx0side ((T.mem_sideLeaves_iff_inSide).mpr hin)
  let ℓ : T.V → Fin 3 :=
    fun v => if T.inSide s(a, b) a v then p else if v = T.leaf x0 then r else q
  have hℓv : ∀ v : T.V,
      ℓ v = if T.inSide s(a, b) a v then p else if v = T.leaf x0 then r else q := fun _ => rfl
  have hp_fiber : {v : T.V | ℓ v = p} = {v : T.V | T.inSide s(a, b) a v} := by
    ext v
    change (ℓ v = p) ↔ T.inSide s(a, b) a v
    rw [hℓv v]
    by_cases hin : T.inSide s(a, b) a v
    · rw [ite_eq_left hin]
      exact ⟨fun _ => hin, fun _ => rfl⟩
    · by_cases hw : v = T.leaf x0
      · rw [ite_eq_right hin, ite_eq_left hw]
        exact ⟨fun h => absurd h.symm hpr, fun h => absurd h hin⟩
      · rw [ite_eq_right hin, ite_eq_right hw]
        exact ⟨fun h => absurd h.symm hpq, fun h => absurd h hin⟩
  have hr_fiber : {v : T.V | ℓ v = r} = {T.leaf x0} := by
    ext v
    change (ℓ v = r) ↔ v = T.leaf x0
    rw [hℓv v]
    constructor
    · intro hv
      by_cases hin : T.inSide s(a, b) a v
      · rw [ite_eq_left hin] at hv
        exact absurd hv hpr
      · by_cases hw : v = T.leaf x0
        · exact hw
        · rw [ite_eq_right hin, ite_eq_right hw] at hv
          exact absurd hv hqr
    · intro hv
      subst hv
      rw [ite_eq_right hx0notin, ite_eq_left rfl]
  have hq_fiber : {v : T.V | ℓ v = q} = {v : T.V | ¬ T.inSide s(a, b) a v} \ {T.leaf x0} := by
    ext v
    change (ℓ v = q) ↔ (¬ T.inSide s(a, b) a v ∧ v ≠ T.leaf x0)
    rw [hℓv v]
    constructor
    · intro hv
      have hnin : ¬ T.inSide s(a, b) a v := by
        intro hin
        rw [ite_eq_left hin] at hv
        exact absurd hv hpq
      have hw : v ≠ T.leaf x0 := by
        intro hw
        rw [ite_eq_right hnin, ite_eq_left hw] at hv
        exact absurd hv hqr.symm
      exact ⟨hnin, hw⟩
    · rintro ⟨hnin, hw⟩
      rw [ite_eq_right hnin, ite_eq_right hw]
  refine ⟨ℓ, ?_, ?_⟩
  · intro x
    rw [hℓv (T.leaf x)]
    by_cases hxA : x ∈ A
    · have hin : T.inSide s(a, b) a (T.leaf x) := (hside' x).mp hxA
      rw [ite_eq_left hin]
      exact ((hpA x).mp hxA).symm
    · have hnin : ¬ T.inSide s(a, b) a (T.leaf x) := fun hin => hxA ((hside' x).mpr hin)
      by_cases hx : x = x0
      · subst hx
        rw [ite_eq_right hnin, ite_eq_left rfl]
        exact hx0.symm
      · have hleaf : T.leaf x ≠ T.leaf x0 := fun h => hx (T.leaf.injective h)
        rw [ite_eq_right hnin, ite_eq_right hleaf]
        have hq : χ x = q := by
          rcases hval x with h | h | h
          · exact absurd ((hpA x).mpr h) hxA
          · exact h
          · exact absurd (huniq x h) hx
        exact hq.symm
  · intro s
    rcases htri s with rfl | rfl | rfl
    · rw [hp_fiber]
      exact inSide_isConnectedSet T s(a, b) a
    · rw [hq_fiber]
      have hcompl : {v : T.V | ¬ T.inSide s(a, b) a v} = {v : T.V | T.inSide s(a, b) b v} :=
        compl_inSide T hab (T.inSide_self s(a, b) a)
      rw [hcompl]
      refine isConnectedSet_sdiff_leaf T (x := x0) (inSide_isConnectedSet T s(a, b) b) ?_
      rw [← hcompl]
      exact hx0notin
    · rw [hr_fiber]
      exact isConnectedSet_singleton T (T.leaf x0)

/-- 把「边侧」的两种定向合成一条：`A` 是边 `s(a,b)` 的 `a` 侧**或** `b` 侧皆可。 -/
theorem displaysMultiState_of_side_or (T : Cladogram.{u, u} X) (χ : X → Fin 3)
    (p q r : Fin 3) (x0 : X) (A : Finset X) {a b : T.V} (hab : T.graph.Adj a b)
    (hside : A = T.sideLeaves s(a, b) a ∨ A = T.sideLeaves s(a, b) b)
    (hx0side : x0 ∉ A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (htri : ∀ s : Fin 3, s = p ∨ s = q ∨ s = r)
    (hx0 : χ x0 = r) (huniq : ∀ x : X, χ x = r → x = x0)
    (hpA : ∀ x : X, x ∈ A ↔ χ x = p)
    (hval : ∀ x : X, χ x = p ∨ χ x = q ∨ χ x = r) :
    DisplaysMultiState T χ := by
  rcases hside with h | h
  · exact displaysMultiState_of_side T χ p q r x0 A hab h (by rw [← h]; exact hx0side) hpq hpr hqr
      htri hx0 huniq hpA hval
  · refine displaysMultiState_of_side T χ p q r x0 A hab.symm ?_ ?_ hpq hpr hqr htri hx0 huniq
      hpA hval
    · rw [← Sym2.eq_swap]; exact h
    · rw [← Sym2.eq_swap, ← h]; exact hx0side

/-- `IsSideOf` 给出「边 ＋ 端点定向」的形式（两种定向取其一）。 -/
theorem exists_side_disj_of_isSideOf (T : Cladogram.{u, u} X) {A : Finset X}
    (h : T.IsSideOf A) :
    ∃ (a b : T.V), ∃ (_ : T.graph.Adj a b),
      A = T.sideLeaves s(a, b) a ∨ A = T.sideLeaves s(a, b) b := by
  obtain ⟨a, b, hab, w, hw⟩ := h
  refine ⟨a, b, hab, ?_⟩
  rcases T.inSide_or_inSide hab (x := w) with h' | h'
  · exact Or.inl (by rw [hw, T.sideLeaves_eq_of_inSide h'])
  · exact Or.inr (by rw [hw, T.sideLeaves_eq_of_inSide h'])

end MultiStateTree

open MultiStateTree in
/-- ★★★ **`F₃` 的第 0、1 个字符同时被一棵 `Cladogram (Fin 5)` 展示**（叶侧 `{1,4}` 与 `{0,3}`）。 -/
theorem exists_cladogram_displays_fitchMeachamF3_01 :
    ∃ T : Cladogram.{0, 0} (Fin 5),
      DisplaysMultiState T (fitchMeachamF3 0) ∧ DisplaysMultiState T (fitchMeachamF3 1) := by
  have hpair : ∀ A ∈ ({{1, 4}, {0, 3}} : Finset (Finset (Fin 5))),
      ∀ B ∈ ({{1, 4}, {0, 3}} : Finset (Finset (Fin 5))), BinaryCompatible A B := by
    intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> (unfold BinaryCompatible; decide)
  obtain ⟨T, hT⟩ := exists_cladogram_of_pairwise_binaryCompatible
    ({{1, 4}, {0, 3}} : Finset (Finset (Fin 5))) hpair (by decide)
  have h1 : T.IsSideOf ({1, 4} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  have h2 : T.IsSideOf ({0, 3} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  obtain ⟨a1, b1, hab1, hd1⟩ := exists_side_disj_of_isSideOf T h1
  obtain ⟨a2, b2, hab2, hd2⟩ := exists_side_disj_of_isSideOf T h2
  exact ⟨T,
    displaysMultiState_of_side_or T (fitchMeachamF3 0) 1 0 2 3 {1, 4} hab1 hd1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    displaysMultiState_of_side_or T (fitchMeachamF3 1) 2 0 1 4 {0, 3} hab2 hd2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)⟩

open MultiStateTree in
/-- ★★★ **`F₃` 的第 0、2 个字符同时被一棵 `Cladogram (Fin 5)` 展示**（叶侧 `{0,2}` 与 `{1,3}`）。 -/
theorem exists_cladogram_displays_fitchMeachamF3_02 :
    ∃ T : Cladogram.{0, 0} (Fin 5),
      DisplaysMultiState T (fitchMeachamF3 0) ∧ DisplaysMultiState T (fitchMeachamF3 2) := by
  have hpair : ∀ A ∈ ({{0, 2}, {1, 3}} : Finset (Finset (Fin 5))),
      ∀ B ∈ ({{0, 2}, {1, 3}} : Finset (Finset (Fin 5))), BinaryCompatible A B := by
    intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> (unfold BinaryCompatible; decide)
  obtain ⟨T, hT⟩ := exists_cladogram_of_pairwise_binaryCompatible
    ({{0, 2}, {1, 3}} : Finset (Finset (Fin 5))) hpair (by decide)
  have h1 : T.IsSideOf ({0, 2} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  have h2 : T.IsSideOf ({1, 3} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  obtain ⟨a1, b1, hab1, hd1⟩ := exists_side_disj_of_isSideOf T h1
  obtain ⟨a2, b2, hab2, hd2⟩ := exists_side_disj_of_isSideOf T h2
  exact ⟨T,
    displaysMultiState_of_side_or T (fitchMeachamF3 0) 0 1 2 3 {0, 2} hab1 hd1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    displaysMultiState_of_side_or T (fitchMeachamF3 2) 0 1 2 2 {1, 3} hab2 hd2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)⟩

open MultiStateTree in
/-- ★★★ **`F₃` 的第 1、2 个字符同时被一棵 `Cladogram (Fin 5)` 展示**（叶侧 `{1,2}` 与 `{0,4}`）。 -/
theorem exists_cladogram_displays_fitchMeachamF3_12 :
    ∃ T : Cladogram.{0, 0} (Fin 5),
      DisplaysMultiState T (fitchMeachamF3 1) ∧ DisplaysMultiState T (fitchMeachamF3 2) := by
  have hpair : ∀ A ∈ ({{1, 2}, {0, 4}} : Finset (Finset (Fin 5))),
      ∀ B ∈ ({{1, 2}, {0, 4}} : Finset (Finset (Fin 5))), BinaryCompatible A B := by
    intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> (unfold BinaryCompatible; decide)
  obtain ⟨T, hT⟩ := exists_cladogram_of_pairwise_binaryCompatible
    ({{1, 2}, {0, 4}} : Finset (Finset (Fin 5))) hpair (by decide)
  have h1 : T.IsSideOf ({1, 2} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  have h2 : T.IsSideOf ({0, 4} : Finset (Fin 5)) := hT _ (by simp) (by decide) (by decide)
  obtain ⟨a1, b1, hab1, hd1⟩ := exists_side_disj_of_isSideOf T h1
  obtain ⟨a2, b2, hab2, hd2⟩ := exists_side_disj_of_isSideOf T h2
  exact ⟨T,
    displaysMultiState_of_side_or T (fitchMeachamF3 1) 0 2 1 4 {1, 2} hab1 hd1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    displaysMultiState_of_side_or T (fitchMeachamF3 2) 1 0 2 2 {0, 4} hab2 hd2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)⟩

/-- ★★★★★ **`MultiStatePairwiseInsufficiencyGap` 的「两两可解」半**：`F₃` 的任两个字符
都被某一棵 `Cladogram (Fin 5)` 同时展示。 -/
theorem pairwise_displays_fitchMeachamF3 :
    ∀ i j : Fin 3, i ≠ j → ∃ T : Cladogram.{0, 0} (Fin 5),
      DisplaysMultiState T (fitchMeachamF3 i) ∧ DisplaysMultiState T (fitchMeachamF3 j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact exists_cladogram_displays_fitchMeachamF3_01
  · exact exists_cladogram_displays_fitchMeachamF3_02
  · obtain ⟨T, h1, h2⟩ := exists_cladogram_displays_fitchMeachamF3_01
    exact ⟨T, h2, h1⟩
  · exact absurd rfl hij
  · exact exists_cladogram_displays_fitchMeachamF3_12
  · obtain ⟨T, h1, h2⟩ := exists_cladogram_displays_fitchMeachamF3_02
    exact ⟨T, h2, h1⟩
  · obtain ⟨T, h1, h2⟩ := exists_cladogram_displays_fitchMeachamF3_12
    exact ⟨T, h2, h1⟩
  · exact absurd rfl hij

/-- ★★★★★★ **`MultiStatePairwiseInsufficiencyGap` 收口**（`M := fitchMeachamF3`）：
两两可解（`pairwise_displays_fitchMeachamF3`）＋整体不可解（`not_exists_displays_all_fitchMeachamF3`）。 -/
theorem MultiStatePairwiseInsufficiencyGap_holds : MultiStatePairwiseInsufficiencyGap :=
  ⟨fitchMeachamF3, pairwise_displays_fitchMeachamF3, not_exists_displays_all_fitchMeachamF3⟩
