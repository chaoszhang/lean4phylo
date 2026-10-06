/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Phylo.Split

/-! 供 `↥F` / `Finset α` 使用的 `Fintype`（本版 Mathlib 未为 `Finset α` 提供实例）。 -/
instance instFintypeFinset {α : Type*} [Fintype α] [DecidableEq α] : Fintype (Finset α) where
  elems := (Finset.univ : Finset α).powerset
  complete := fun S => Finset.mem_powerset.mpr (Finset.subset_univ S)

instance instFintypeSubtype {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Fintype ↥F :=
  ⟨F.attach, fun x => Finset.mem_attach F x⟩


/-!
# `Phylo.Laminar` —— 镶嵌族 ⟹ 树（「相容 ⟹ 存在树」的构造层）

`CONCEPTS.md` §3.4 / §3.11：Splits-Equivalence 的另一半
「Σ ⊆ Σ' 两两相容 ⟹ 存在树 T 使 Σ' ⊆ Σ(T)」走**镶嵌族建树**路线：

1. 固定 `ρ`，取相容 split 的**规范 cluster** `s.cluster ρ`（全部避开 `ρ`，故两两镶嵌
   —— `Split.laminar_of_compatible_clusters` 已证）；
2. 在镶嵌族上建树：顶点 = 簇 ∪ 元素，`A ~ B ⟺ A ⊊ B` 且 `B` 是 `A` 的最小严格包含者，
   叶 `x` 挂在包含它的最小簇下；
3. 验证 `no_degree_two`（镶嵌构造可能产生度 2 顶点）与 `isTree`。

本文件搭**构造层骨架**：顶点类型、叶嵌入、严格包含者、父函数。
-/

namespace Phylo

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **镶嵌树的顶点**：`Sum.inl A` 是簇（内部顶点），`Sum.inr x` 是元素（叶）。

用 `Sum` 而非自建 `inductive` —— 免费获得 `DecidableEq` / `Fintype` 实例。 -/
abbrev TreeVertex (α : Type*) := Finset α ⊕ α

/-- **叶嵌入**。 -/
def leafEmb : α ↪ TreeVertex α :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- 簇 `A` 对应的顶点。 -/
def nodeV (A : Finset α) : TreeVertex α := Sum.inl A

/-- `F` 中含 `x` 的簇。 -/
def clustersOf (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter fun A => x ∈ A

/-- `A` 在 `F` 中的**严格包含者**（候选父簇）。 -/
def strictSups (F : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  F.filter fun B => A ⊂ B

/-- 严格包含者都真包含 `A`。 -/
theorem mem_strictSups {F : Finset (Finset α)} {A B : Finset α} :
    B ∈ strictSups F A ↔ B ∈ F ∧ A ⊂ B := by
  simp [strictSups]

/-- **父簇**：镶嵌族中 `A` 的**最小严格包含者**。

镶嵌性 ⟹ 严格包含者两两嵌套 ⟹ 其下确界（`Finset.inf`，即交集）落在族中，
且正是最小者。无严格包含者时 `Finset.inf` 给 `⊤ = univ`。

（`Finset α` 本身是 `SemilatticeInf` + `OrderTop`，故 `Finset.inf` 可直接用。） -/
noncomputable def parentOf (F : Finset (Finset α)) (A : Finset α) : Finset α :=
  (strictSups F A).inf id

/-- **`B` 是 `A`（在族 `F` 中）的父**：`B ∈ F`，`A ⊊ B`，且 `B` 含于任一严格包含 `A` 的族成员。 -/
def IsParentOf (F : Finset (Finset α)) (A B : Finset α) : Prop :=
  B ∈ F ∧ A ⊂ B ∧ ∀ C ∈ F, A ⊂ C → B ⊆ C

variable {F : Finset (Finset α)}

/-- **`parentOf` 确实是父**（镶嵌族、`univ ∈ F`、族元素非空、`A ≠ univ`）。

`univ ∈ strictSups F A`（因 `A ⊂ univ`）⟹ `A` 有严格包含者；
镶嵌性 ⟹ 严格包含者对 `∩` 封闭 ⟹ `Finset.inf_mem` 给出 `parentOf F A` 在族中且 ⊋ `A`；
`Finset.inf_le` 给出最小性。 -/
theorem isParentOf_parentOf (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty)
    (huniv : (Finset.univ : Finset α) ∈ F) {A : Finset α} (hA : A ∈ F)
    (hAuniv : A ≠ Finset.univ) :
    IsParentOf F A (parentOf F A) := by
  have hmem : parentOf F A ∈ {B : Finset α | B ∈ F ∧ A ⊂ B} := by
    refine Finset.inf_mem ({B : Finset α | B ∈ F ∧ A ⊂ B})
      ⟨huniv, lt_of_le_of_ne (Finset.subset_univ A) hAuniv⟩ ?_ _ _ ?_
    · intro x hx y hy
      obtain ⟨hxF, hxA⟩ := hx
      obtain ⟨hyF, hyA⟩ := hy
      rcases hl x hxF y hyF with hxy | hyx | hd
      · rw [inf_eq_left.mpr hxy]; exact ⟨hxF, hxA⟩
      · rw [inf_eq_right.mpr hyx]; exact ⟨hyF, hyA⟩
      · exfalso
        obtain ⟨a, ha⟩ := hne A hA
        rw [Finset.disjoint_iff_inter_eq_empty] at hd
        have hmem' : a ∈ x ∩ y := Finset.mem_inter.mpr ⟨hxA.1 ha, hyA.1 ha⟩
        rw [hd] at hmem'
        exact Finset.notMem_empty a hmem'
    · intro B hB
      exact mem_strictSups.mp hB
  exact ⟨hmem.1, hmem.2, fun C hC hAC => Finset.inf_le (mem_strictSups.mpr ⟨hC, hAC⟩)⟩

/-- **镶嵌族中同一簇的严格包含者两两嵌套**（`A` 非空时「相离」被排除）。

这正是「交集 = 最小者」（`parentOf` 语义）的依据。 -/
theorem laminar_strictSups {A B C : Finset α} (hl : LaminarFamily F)
    (hne : A.Nonempty) (hB : B ∈ strictSups F A) (hC : C ∈ strictSups F A) :
    B ⊆ C ∨ C ⊆ B := by
  rcases hl B (mem_strictSups.mp hB).1 C (mem_strictSups.mp hC).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨x, hx⟩ := hne
    exact (Finset.disjoint_left.mp h) ((mem_strictSups.mp hB).2.1 hx)
      ((mem_strictSups.mp hC).2.1 hx)

/-- 严格包含者集合在镶嵌族下**两两嵌套**（`Finset` 版的 `laminar_strictSups`）。 -/
theorem laminar_strictSups_pairwise {A : Finset α} (hl : LaminarFamily F)
    (hne : A.Nonempty) :
    ∀ B ∈ strictSups F A, ∀ C ∈ strictSups F A, B ⊆ C ∨ C ⊆ B :=
  fun _ hB _ hC => laminar_strictSups hl hne hB hC

/-! ### 父关系的特征性质 -/

/-- **父唯一**（两个父互相包含）。 -/
theorem isParentOf_unique {A B B' : Finset α}
    (h : IsParentOf F A B) (h' : IsParentOf F A B') : B = B' :=
  Finset.Subset.antisymm (h.2.2 B' h'.1 h'.2.1) (h'.2.2 B h.1 h.2.1)

/-- 父是严格包含者。 -/
theorem isParentOf_mem_strictSups {A B : Finset α} (h : IsParentOf F A B) :
    B ∈ strictSups F A :=
  mem_strictSups.mpr ⟨h.1, h.2.1⟩

/-- **父最小性**（直接取自定义）：父含于任一严格包含 `A` 的族成员。 -/
theorem isParentOf_subset_of_strictSup {A B C : Finset α}
    (h : IsParentOf F A B) (hC : C ∈ F) (hAC : A ⊂ C) : B ⊆ C :=
  h.2.2 C hC hAC

/-- **`A` 是含 `x` 的最小簇**（叶 `x` 的父簇）。 -/
def IsMinClusterOf (F : Finset (Finset α)) (x : α) (A : Finset α) : Prop :=
  A ∈ F ∧ x ∈ A ∧ ∀ C ∈ F, x ∈ C → A ⊆ C

/-- 含 `x` 的最小簇唯一。 -/
theorem isMinClusterOf_unique {x : α} {A A' : Finset α}
    (h : IsMinClusterOf F x A) (h' : IsMinClusterOf F x A') : A = A' :=
  Finset.Subset.antisymm (h.2.2 A' h'.1 h'.2.1) (h'.2.2 A h.1 h.2.1)

/-- 含 `x` 的最小簇是最小的含 `x` 成员。 -/
theorem isMinClusterOf_subset {x : α} {A C : Finset α}
    (h : IsMinClusterOf F x A) (hC : C ∈ F) (hxC : x ∈ C) : A ⊆ C :=
  h.2.2 C hC hxC

/-! ### 镶嵌树的图

顶点 = 簇 ∪ 元素；边 = 「父子」（簇之间）与「叶挂最小簇」（叶–簇）。 -/

/-- **镶嵌树的邻接关系**（无向）。

* 簇 `A` — 簇 `B`：一方是另一方的父（取 `∨` 使得对称）；
* 叶 `x` — 簇 `A`：`A` 是含 `x` 的最小簇；
* 叶 — 叶：无边。 -/
def laminarAdj (F : Finset (Finset α)) (u v : TreeVertex α) : Prop :=
  match u, v with
  | Sum.inl A, Sum.inl B => IsParentOf F A B ∨ IsParentOf F B A
  | Sum.inr x, Sum.inl A => IsMinClusterOf F x A
  | Sum.inl A, Sum.inr x => IsMinClusterOf F x A
  | Sum.inr _, Sum.inr _ => False

/-- **镶嵌树的图**（无自环 + 对称内联证毕）。 -/
def laminarGraph (F : Finset (Finset α)) : SimpleGraph (TreeVertex α) where
  Adj := laminarAdj F
  symm := ⟨fun u v h => by
    match u, v with
    | Sum.inl _, Sum.inl _ => exact h.symm
    | Sum.inl _, Sum.inr _ => exact h
    | Sum.inr _, Sum.inl _ => exact h
    | Sum.inr _, Sum.inr _ => exact h⟩
  loopless := ⟨fun u h => by
    match u with
    | Sum.inl A =>
      rcases h with h | h
      · exact h.2.1.2 (Finset.Subset.refl A)
      · exact h.2.1.2 (Finset.Subset.refl A)
    | Sum.inr _ => exact h⟩

/-! ### 通往连通性的阶梯：父关系是全序的「上溯」结构

镶嵌性 ⟹ 两个簇若都在 `A` 之上且非嵌套，则「相离」与「都 ⊋ A」矛盾；
于是**严格包含者链是全序** ⇒ 父链唯一 ⇒ 可沿父链上溯到根。 -/

/-- **父严格单调**（用于排除回路 / 保证链有界）。 -/
theorem isParentOf_ssubset {A B : Finset α} (h : IsParentOf F A B) : A ⊂ B :=
  h.2.1

/-- `A` 的全部**幂集意义下**的超集链：`A ⊂ B`。 -/
theorem isParentOf_card_lt {A B : Finset α} (h : IsParentOf F A B) : A.card < B.card :=
  Finset.card_lt_card h.2.1

/-- **父链的相邻步**：`u` 是 `v` 的父（簇视角）。 -/
def IsParentVertex (F : Finset (Finset α)) (u v : TreeVertex α) : Prop :=
  match u, v with
  | Sum.inl A, Sum.inl B => IsParentOf F A B
  | Sum.inr x, Sum.inl B => IsMinClusterOf F x B
  | _, _ => False

/-- 父关系确实是图上的边（顺带确认 `laminarAdj` 与 `IsParentVertex` 相容）。 -/
theorem isParentVertex_adj {F : Finset (Finset α)} {u v : TreeVertex α}
    (h : IsParentVertex F u v) : (laminarGraph F).Adj u v := by
  match u, v with
  | Sum.inl A, Sum.inl B => exact Or.inl h
  | Sum.inr x, Sum.inl B => exact h
  | Sum.inl _, Sum.inr _ => exact h.elim
  | Sum.inr _, Sum.inr _ => exact h.elim

/-! ### 修正构造：删单元素簇 + 加 `univ` 作根（解决「度 2」问题）

原 `laminarGraph F` 有两处毛病：

* 元素 `ρ ∉ ⋃F` 时**孤立** ⟹ 图不连通（需 `univ` 作根）；
* 单元素簇 `{x}` 与叶 `x` 重复（它们本是同一条**叶边**）⟹ 产生度 2 顶点。

**修正**：`normFinset F` 删掉单元素簇、加入 `univ`。下面给出配套的构件。 -/

/-- **正规化簇族**：删掉单元素簇（叶边不需要内部顶点），加入 `univ` 作根。 -/
def normFinset (F : Finset (Finset α)) : Finset (Finset α) :=
  insert Finset.univ (F.filter fun A => 2 ≤ A.card)

theorem mem_normFinset {A : Finset α} :
    A ∈ normFinset F ↔ A = Finset.univ ∨ (A ∈ F ∧ 2 ≤ A.card) := by
  simp [normFinset]

theorem univ_mem_normFinset : (Finset.univ : Finset α) ∈ normFinset F :=
  Finset.mem_insert_self _ _

/-- **正规化保持镶嵌性**（`univ` 包含一切；删元素保持镶嵌）。 -/
theorem laminarFamily_normFinset (hl : LaminarFamily F) : LaminarFamily (normFinset F) := by
  intro A hA B hB
  rw [mem_normFinset] at hA hB
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact Or.inl (Finset.Subset.refl _)
    · exact Or.inr (Or.inl (Finset.subset_univ B))
  · rcases hB with rfl | hB
    · exact Or.inl (Finset.subset_univ A)
    · exact hl A hA.1 B hB.1

/-- 正规化后族元素都非空（`univ` 非空需 `α` 非空；其余 `|A| ≥ 2`）。 -/
theorem normFinset_nonempty [Nonempty α] : ∀ B ∈ normFinset F, B.Nonempty := by
  intro B hB
  rw [mem_normFinset] at hB
  rcases hB with rfl | ⟨_, hcard⟩
  · exact Finset.univ_nonempty
  · exact Finset.card_pos.mp (by omega)

/-- **`B` 是 `A` 的孩子**：`B` 是 `A` 在 `F` 中的**极大真子集**。 -/
def IsChildOf (F : Finset (Finset α)) (A B : Finset α) : Prop :=
  B ∈ F ∧ B ⊂ A ∧ ∀ C ∈ F, B ⊂ C → ¬ C ⊂ A

/-- **孩子是父关系的反向**：`IsChildOf F A B ⟹ IsParentOf F B A`。

证：任取 `C ∈ F` 使 `B ⊂ C`；`C` 与 `A` 都由镶嵌性可比（都真包含非空的 `B`，故不相离）；
`C ⊊ A` 会与「`B` 是极大真子集」矛盾，故 `A ⊆ C` —— 正是 `IsParentOf F B A` 的第三项。 -/
theorem isChildOf_isParentOf (hl : LaminarFamily F) {A B : Finset α}
    (hA : A ∈ F) (hne : B.Nonempty) (h : IsChildOf F A B) : IsParentOf F B A := by
  obtain ⟨hBF, hBA, hmax⟩ := h
  refine ⟨hA, hBA, ?_⟩
  intro C hC hBC
  have hne' : (A ∩ C).Nonempty := hne.mono (Finset.subset_inter hBA.1 hBC.1)
  rcases hl A hA C hC with hsub | hsub | hdisj
  · exact hsub
  · -- `C ⊆ A`：若 `A ⊄ C` 则 `C ⊊ A`，与「`B` 是极大真子集」矛盾
    by_contra hAC
    exact hmax C hC hBC
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hCA => hAC (by rw [hCA])⟩)
  · exfalso
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    obtain ⟨a, ha⟩ := hne'
    rw [hdisj] at ha
    exact absurd ha (Finset.notMem_empty a)

/-- **`A` 的直接元素**：`x ∈ A` 且**不被任何含 `x` 的族成员真包含于 `A`**（`x` 直接挂在 `A` 上）。 -/
def directElems (F : Finset (Finset α)) (A : Finset α) : Finset α :=
  A.filter fun x => ∀ B ∈ F, x ∈ B → A ⊆ B

theorem mem_directElems {A : Finset α} {x : α} :
    x ∈ directElems F A ↔ x ∈ A ∧ ∀ B ∈ F, x ∈ B → A ⊆ B := by
  classical
  simp [directElems]

/-- **直接元素挂在 `A` 上**：`x ∈ directElems F A ⟹ IsMinClusterOf F x A`。 -/
theorem directElems_isMinClusterOf {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F)
    {x : α} (h : x ∈ directElems F A) : IsMinClusterOf F x A := by
  rw [mem_directElems] at h
  exact ⟨hA, h.1, h.2⟩

/-! ### 极大真子集（孩子）的存在性 —— 取 `card` 最大者

`Finset.exists_mem_eq_sup` 是关键工具（`Finset.max'` / `exists_max_image` 在本版 Mathlib 不存在）。 -/

/-- **`A` 有真子集 ⟹ `A` 有孩子**（`A` 的真子集中 `card` 最大者）。 -/
theorem exists_isChildOf {A : Finset α} (h : ∃ B ∈ F, B ⊂ A) : ∃ B, IsChildOf F A B := by
  classical
  have hne : (F.filter fun B => B ⊂ A).Nonempty :=
    h.imp fun B hB => Finset.mem_filter.mpr hB
  obtain ⟨B, hB, hBmax⟩ := Finset.exists_mem_eq_sup (F.filter fun B => B ⊂ A) hne Finset.card
  obtain ⟨hBF, hBA⟩ := Finset.mem_filter.mp hB
  refine ⟨B, hBF, hBA, fun C hC hBC hCA => ?_⟩
  have hCS : C ∈ F.filter fun B => B ⊂ A := Finset.mem_filter.mpr ⟨hC, hCA⟩
  have h1 : C.card ≤ B.card := hBmax ▸ Finset.le_sup hCS
  have h2 : B.card < C.card := Finset.card_lt_card hBC
  omega

/-- **含 `x` 的极大真子集存在**：若 `x ∈ A` 且 `x` 被某个 `A` 的真子集含，则存在孩子含 `x`。 -/
theorem exists_isChildOf_mem {A : Finset α} {x : α}
    (h : ∃ B ∈ F, x ∈ B ∧ B ⊂ A) : ∃ B, IsChildOf F A B ∧ x ∈ B := by
  classical
  have hne : (F.filter fun B => x ∈ B ∧ B ⊂ A).Nonempty :=
    h.imp fun B hB => Finset.mem_filter.mpr hB
  obtain ⟨B, hB, hBmax⟩ :=
    Finset.exists_mem_eq_sup (F.filter fun B => x ∈ B ∧ B ⊂ A) hne Finset.card
  obtain ⟨hBF, hxB, hBA⟩ := Finset.mem_filter.mp hB
  refine ⟨B, ⟨hBF, hBA, fun C hC hBC hCA => ?_⟩, hxB⟩
  have hxS : x ∈ C := hBC.1 hxB
  have hCS : C ∈ F.filter fun B => x ∈ B ∧ B ⊂ A := Finset.mem_filter.mpr ⟨hC, hxS, hCA⟩
  have h1 : C.card ≤ B.card := hBmax ▸ Finset.le_sup hCS
  have h2 : B.card < C.card := Finset.card_lt_card hBC
  omega

/-- **非直接元素 ⟹ 落在某个真子集里**。 -/
theorem exists_ssubset_of_not_mem_directElems (hl : LaminarFamily F) {A : Finset α}
    (hA : A ∈ F) {t : α} (ht : t ∈ A) (hd : t ∉ directElems F A) :
    ∃ B ∈ F, t ∈ B ∧ B ⊂ A := by
  classical
  rw [mem_directElems, not_and_or] at hd
  rcases hd with h | h
  · exact absurd ht h
  · push_neg at h
    obtain ⟨B, hB, htB, hAB⟩ := h
    refine ⟨B, hB, htB, ?_⟩
    rcases hl A hA B hB with hsub | hsub | hdisj
    · exact absurd hsub hAB
    · exact Finset.ssubset_iff_subset_ne.mpr
        ⟨hsub, fun heq => hAB (heq ▸ Finset.Subset.refl A)⟩
    · exfalso
      rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
      have : t ∈ A ∩ B := Finset.mem_inter.mpr ⟨ht, htB⟩
      rw [hdisj] at this
      exact Finset.notMem_empty t this

/-! ### ★ 核心计数：孩子数 + 直接元素数 ≥ 2

这是「非 `univ` 簇的度 ≥ 3」的全部内容（`A ≠ univ` 时另有父，故总邻居 ≥ 1 + 2 = 3）。

**论证**（设孩子数 `k`）：
* `k = 0`：`A` 无真子集 ⟹ 每个 `t ∈ A` 的**最小簇就是 `A`** ⟹ `A ⊆ directElems` ⟹ `|A| ≤ |dirs|`，而 `|A| ≥ 2`；
* `k = 1`（孩子 `B`）：`B ⊊ A` ⟹ 取 `t ∈ A \ B`；若 `t` 不是直接元素，
  则由 `exists_isChildOf_mem` 还有**另一个**含 `t` 的孩子 ≠ `B`，与 `k = 1` 矛盾 ⟹ `dirs ≥ 1`；
* `k ≥ 2`：显然。 -/
theorem two_le_card_children_add_card_directElems (hl : LaminarFamily F)
    {A : Finset α} (hA : A ∈ F) (hcard : 2 ≤ A.card) :
    2 ≤ (F.filter fun B => IsChildOf F A B).card + (directElems F A).card := by
  classical
  rcases Nat.lt_or_ge (F.filter fun B => IsChildOf F A B).card 2 with hlt | hge
  · have hK : (F.filter fun B => IsChildOf F A B).card = 0 ∨
        (F.filter fun B => IsChildOf F A B).card = 1 := by omega
    rcases hK with h0 | h1
    · -- 无孩子 ⟹ `A ⊆ directElems`
      have hempty : (F.filter fun B => IsChildOf F A B) = ∅ := Finset.card_eq_zero.mp h0
      have hsub : A ⊆ directElems F A := by
        intro t ht
        rw [mem_directElems]
        refine ⟨ht, fun B hB htB => ?_⟩
        by_contra hAB
        have hBA : B ⊂ A := by
          rcases hl A hA B hB with hsub | hsub | hdisj
          · exact absurd hsub hAB
          · exact Finset.ssubset_iff_subset_ne.mpr
              ⟨hsub, fun heq => hAB (heq ▸ Finset.Subset.refl A)⟩
          · exfalso
            rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
            have ht' : t ∈ A ∩ B := Finset.mem_inter.mpr ⟨ht, htB⟩
            rw [hdisj] at ht'
            exact Finset.notMem_empty t ht'
        obtain ⟨C, hC⟩ := exists_isChildOf (F := F) ⟨B, hB, hBA⟩
        have hmem : C ∈ F.filter fun B => IsChildOf F A B :=
          Finset.mem_filter.mpr ⟨hC.1, hC⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty C hmem
      have : A.card ≤ (directElems F A).card := Finset.card_le_card hsub
      omega
    · -- 恰一个孩子 `B`
      obtain ⟨B, hBset⟩ := Finset.card_eq_one.mp h1
      have hBchild : IsChildOf F A B := by
        have hmem : B ∈ F.filter fun B => IsChildOf F A B := by
          rw [hBset]; exact Finset.mem_singleton_self B
        exact (Finset.mem_filter.mp hmem).2
      have hnotsub : ¬ A ⊆ B := hBchild.2.1.2
      obtain ⟨t, htA, htB⟩ := Finset.not_subset.mp hnotsub
      have htd : t ∈ directElems F A := by
        by_contra htd'
        obtain ⟨C, hC, htC, hCA⟩ :=
          exists_ssubset_of_not_mem_directElems hl hA htA htd'
        obtain ⟨D, hDchild, htD⟩ := exists_isChildOf_mem (F := F) ⟨C, hC, htC, hCA⟩
        have hDB : D ≠ B := fun heq => htB (heq ▸ htD)
        have hmem : D ∈ F.filter fun B => IsChildOf F A B :=
          Finset.mem_filter.mpr ⟨hDchild.1, hDchild⟩
        rw [hBset] at hmem
        exact hDB (Finset.mem_singleton.mp hmem)
      have : 0 < (directElems F A).card := Finset.card_pos.mpr ⟨t, htd⟩
      omega
  · omega

/-! ### ★ 非 `univ` 簇的度 ≥ 3（修正构造的核心性质）

邻居由三部分组成，**互不相交**：
1. 父 `inl (parentOf F' A)`（`A ≠ univ` ⟹ 父存在）；
2. 孩子 `inl B`（`B ∈ kids`）；
3. 直接元素 `inr t`（`t ∈ dirs`）。

计数 `two_le_card_children_add_card_directElems` 给出 `|kids| + |dirs| ≥ 2`，
故 `|邻居| ≥ 1 + 2 = 3`。**这就是「度 2 问题」的解**（`univ` 自身的度另论）。 -/
theorem three_le_degree_of_ne_univ (hl : LaminarFamily F) [Nonempty α]
    {A : Finset α} (hA : A ∈ normFinset F) (hAuniv : A ≠ Finset.univ) :
    3 ≤ (laminarGraph (normFinset F)).degree (Sum.inl A) := by
  classical
  set F' := normFinset F with hF'
  have hl' : LaminarFamily F' := laminarFamily_normFinset hl
  have hne' : ∀ B ∈ F', B.Nonempty := fun B hB => normFinset_nonempty B (hF' ▸ hB)
  have huniv : (Finset.univ : Finset α) ∈ F' := hF' ▸ univ_mem_normFinset
  obtain ⟨hAF, hcard⟩ : A ∈ F ∧ 2 ≤ A.card := by
    rcases (mem_normFinset.mp hA) with h | h
    · exact absurd h hAuniv
    · exact h
  have hAF' : A ∈ F' := hA
  have hPA : IsParentOf F' A (parentOf F' A) := isParentOf_parentOf hl' hne' huniv hAF' hAuniv
  set kids := F'.filter fun B => IsChildOf F' A B with hkids
  set dirs := directElems F' A with hdirs
  have hcount : 2 ≤ kids.card + dirs.card :=
    two_le_card_children_add_card_directElems hl' hAF' hcard
  -- 三个互不相交的邻居族
  have hd1 : Disjoint ({Sum.inl (parentOf F' A)} : Finset (TreeVertex α))
      (kids.image (Sum.inl : Finset α → TreeVertex α) ∪ dirs.image (Sum.inr : α → TreeVertex α)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_singleton] at hu
    subst hu
    simp only [Finset.mem_union, Finset.mem_image] at hu'
    rcases hu' with ⟨B, hBk, hPB⟩ | ⟨t, -, hPt⟩
    · obtain ⟨hBF, hBchild⟩ := Finset.mem_filter.mp (hkids ▸ hBk)
      have hPB' : B = parentOf F' A := Sum.inl.inj hPB
      rw [hPB'] at hBchild
      exact absurd hPA.2.1.1 hBchild.2.1.2
    · exact Sum.inl_ne_inr hPt.symm
  have hd2 : Disjoint (kids.image (Sum.inl : Finset α → TreeVertex α)) (dirs.image (Sum.inr : α → TreeVertex α)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨B, -, hBu⟩ := Finset.mem_image.mp hu
    obtain ⟨t, -, htu⟩ := Finset.mem_image.mp hu'
    exact Sum.inl_ne_inr (hBu ▸ htu).symm
  have hk : (kids.image (Sum.inl : Finset α → TreeVertex α)).card = kids.card :=
    Finset.card_image_of_injOn fun a _ b _ h => Sum.inl.inj h
  have hdr : (dirs.image (Sum.inr : α → TreeVertex α)).card = dirs.card :=
    Finset.card_image_of_injOn fun a _ b _ h => Sum.inr.inj h
  have hcard3 : 3 ≤ ({(Sum.inl (parentOf F' A) : TreeVertex α)} ∪
      (kids.image (Sum.inl : Finset α → TreeVertex α) ∪ dirs.image (Sum.inr : α → TreeVertex α))).card := by
    rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      Finset.card_singleton, hk, hdr]
    omega
  have hsub : ({(Sum.inl (parentOf F' A) : TreeVertex α)} ∪ (kids.image (Sum.inl : Finset α → TreeVertex α) ∪ dirs.image (Sum.inr : α → TreeVertex α)))
      ⊆ (laminarGraph F').neighborFinset (Sum.inl A) := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hu
    rcases hu with rfl | ⟨B, hBk, rfl⟩ | ⟨t, htd, rfl⟩
    · exact Or.inl hPA
    · obtain ⟨hBF, hBchild⟩ := Finset.mem_filter.mp (hkids ▸ hBk)
      exact Or.inr (isChildOf_isParentOf hl' hAF' (hne' B hBF) hBchild)
    · exact directElems_isMinClusterOf hAF' (hdirs ▸ htd)
  calc 3 ≤ ({(Sum.inl (parentOf F' A) : TreeVertex α)} ∪ (kids.image (Sum.inl : Finset α → TreeVertex α) ∪ dirs.image (Sum.inr : α → TreeVertex α))).card :=
        hcard3
    _ ≤ ((laminarGraph F').neighborFinset (Sum.inl A)).card := Finset.card_le_card hsub
    _ = (laminarGraph F').degree (Sum.inl A) := SimpleGraph.card_neighborFinset_eq_degree _ _

/-! ### 受限顶点类型的图（连通性 / `isTree` 用）

`laminarGraph F` 的顶点是**所有** `Finset α`（族外者孤立）⟹ 不连通。
故另给**顶点受限**的版本：顶点 = 族成员 + 元素 —— 这才是真正的树。 -/

/-- **受限顶点类型**：`F` 的成员（内部顶点）+ 元素（叶）。 -/
abbrev LaminarVertex (F : Finset (Finset α)) := ↥F ⊕ α

/-- 到「无限顶点」版本顶点的强制映射。 -/
def coerceV (F : Finset (Finset α)) : LaminarVertex F → TreeVertex α
  | Sum.inl A => Sum.inl A.1
  | Sum.inr x => Sum.inr x

@[simp] theorem coerceV_inl (F : Finset (Finset α)) (A : ↥F) :
    coerceV F (Sum.inl A) = Sum.inl A.1 := rfl

@[simp] theorem coerceV_inr (F : Finset (Finset α)) (x : α) :
    coerceV F (Sum.inr x) = Sum.inr x := rfl

/-- **受限图**：顶点 = 族成员 + 元素；边经 `coerceV` 由 `laminarAdj` 给出。 -/
def treeGraph (F : Finset (Finset α)) : SimpleGraph (LaminarVertex F) where
  Adj u v := laminarAdj F (coerceV F u) (coerceV F v)
  symm := ⟨fun u v h => by
    match u, v with
    | Sum.inl _, Sum.inl _ => exact h.symm
    | Sum.inl _, Sum.inr _ => exact h
    | Sum.inr _, Sum.inl _ => exact h
    | Sum.inr _, Sum.inr _ => exact h⟩
  loopless := ⟨fun u h => by
    match u with
    | Sum.inl A =>
      rcases h with h | h
      · exact h.2.1.2 (Finset.Subset.refl A.1)
      · exact h.2.1.2 (Finset.Subset.refl A.1)
    | Sum.inr _ => exact h⟩

@[simp] theorem treeGraph_adj_inl_inl (F : Finset (Finset α)) (A B : ↥F) :
    (treeGraph F).Adj (Sum.inl A) (Sum.inl B) ↔
      IsParentOf F A.1 B.1 ∨ IsParentOf F B.1 A.1 := Iff.rfl

@[simp] theorem treeGraph_adj_inl_inr (F : Finset (Finset α)) (A : ↥F) (x : α) :
    (treeGraph F).Adj (Sum.inl A) (Sum.inr x) ↔ IsMinClusterOf F x A.1 := Iff.rfl

@[simp] theorem treeGraph_adj_inr_inl (F : Finset (Finset α)) (x : α) (A : ↥F) :
    (treeGraph F).Adj (Sum.inr x) (Sum.inl A) ↔ IsMinClusterOf F x A.1 := Iff.rfl

/-! ### 连通性：一切顶点可达根 `univ` -/

/-- **含 `x` 的最小簇存在**（假设 `x` 被某族成员含）：取含 `x` 的族成员中 `card` 最小者。 -/
theorem exists_isMinClusterOf {F : Finset (Finset α)} (hl : LaminarFamily F) {x : α}
    (h : ∃ A ∈ F, x ∈ A) : ∃ A, IsMinClusterOf F x A := by
  classical
  have hne : (F.filter fun A => x ∈ A).Nonempty := h.imp fun A hA => Finset.mem_filter.mpr hA
  obtain ⟨A, hA, hAmax⟩ := Finset.exists_mem_eq_sup (F.filter fun A => x ∈ A) hne
    (fun A => (Finset.univ : Finset α).card - A.card)
  obtain ⟨hAF, hxA⟩ := Finset.mem_filter.mp hA
  refine ⟨A, hAF, hxA, fun C hC hxC => ?_⟩
  have hCS : C ∈ F.filter fun A => x ∈ A := Finset.mem_filter.mpr ⟨hC, hxC⟩
  have h1 : (Finset.univ : Finset α).card - C.card ≤ (Finset.univ : Finset α).card - A.card :=
    hAmax ▸ Finset.le_sup (f := fun A => (Finset.univ : Finset α).card - A.card) hCS
  have hcA := Finset.card_le_card (Finset.subset_univ A)
  have hcC := Finset.card_le_card (Finset.subset_univ C)
  have hCA : A.card ≤ C.card := by omega
  rcases hl A hAF C hC with hsub | hsub | hdisj
  · exact hsub
  · have hEq : C = A := Finset.eq_of_subset_of_card_le hsub hCA
    rw [hEq]
  · exfalso
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    have : x ∈ A ∩ C := Finset.mem_inter.mpr ⟨hxA, hxC⟩
    rw [hdisj] at this
    exact Finset.notMem_empty x this

/-- **族成员可达根**（沿 `parentOf` 链上溯；`card` 严格递增保证终止）。 -/
theorem treeGraph_reachable_root {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) :
    ∀ A : ↥F, (treeGraph F).Reachable (Sum.inl A) (Sum.inl ⟨Finset.univ, huniv⟩) := by
  suffices h : ∀ n, ∀ A : ↥F, (Finset.univ : Finset α).card - A.1.card ≤ n →
      (treeGraph F).Reachable (Sum.inl A) (Sum.inl ⟨Finset.univ, huniv⟩) by
    intro A; exact h _ A le_rfl
  intro n
  induction n with
  | zero =>
    intro A hle
    have hcard : A.1.card = (Finset.univ : Finset α).card := by
      have := Finset.card_le_card (Finset.subset_univ A.1); omega
    have hAuniv : A.1 = Finset.univ := Finset.eq_univ_of_card _ hcard
    have : A = ⟨Finset.univ, huniv⟩ := Subtype.ext hAuniv
    rw [this]
  | succ n ih =>
    intro A hle
    by_cases hAuniv : A.1 = Finset.univ
    · have : A = ⟨Finset.univ, huniv⟩ := Subtype.ext hAuniv
      rw [this]
    · have hPA := isParentOf_parentOf (F := F) (A := A.1) hl hne huniv A.2 hAuniv
      have hcard : A.1.card < (parentOf F A.1).card := Finset.card_lt_card hPA.2.1
      have hle' : (Finset.univ : Finset α).card - (parentOf F A.1).card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ (parentOf F A.1)); omega
      have hadj : (treeGraph F).Adj (Sum.inl A) (Sum.inl ⟨parentOf F A.1, hPA.1⟩) :=
        (treeGraph_adj_inl_inl F A ⟨parentOf F A.1, hPA.1⟩).mpr (Or.inl hPA)
      exact hadj.reachable.trans (ih ⟨parentOf F A.1, hPA.1⟩ hle')

/-- **元素可达根**（元素连到其最小簇，再沿父链上溯）。 -/
theorem treeGraph_reachable_root_of_elem {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) (x : α) :
    (treeGraph F).Reachable (Sum.inr x) (Sum.inl ⟨Finset.univ, huniv⟩) := by
  obtain ⟨A, hA⟩ := exists_isMinClusterOf (F := F) hl ⟨Finset.univ, huniv, Finset.mem_univ x⟩
  have hadj : (treeGraph F).Adj (Sum.inr x) (Sum.inl ⟨A, hA.1⟩) :=
    (treeGraph_adj_inr_inl F x ⟨A, hA.1⟩).mpr hA
  exact hadj.reachable.trans (treeGraph_reachable_root hl hne huniv ⟨A, hA.1⟩)

/-- **★ 受限图连通**（一切顶点经根 `univ` 互达）。 -/
theorem connected_treeGraph {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) :
    (treeGraph F).Connected := by
  haveI : Nonempty (LaminarVertex F) := ⟨Sum.inl ⟨Finset.univ, huniv⟩⟩
  refine ⟨fun u v => ?_⟩
  have hu : (treeGraph F).Reachable u (Sum.inl ⟨Finset.univ, huniv⟩) := by
    match u with
    | Sum.inl A => exact treeGraph_reachable_root hl hne huniv A
    | Sum.inr x => exact treeGraph_reachable_root_of_elem hl hne huniv x
  have hv : (treeGraph F).Reachable v (Sum.inl ⟨Finset.univ, huniv⟩) := by
    match v with
    | Sum.inl A => exact treeGraph_reachable_root hl hne huniv A
    | Sum.inr x => exact treeGraph_reachable_root_of_elem hl hne huniv x
  exact hu.trans hv.symm

/-! ### 边数（`isTree` 的最后一环）

**省力关键**：只需 `parEdge` **满射**（不必双射）——
配合连通性 `Connected.card_vert_le_card_edgeSet_add_one`（`|V| ≤ |E| + 1`）
即可夹出 `|E| = |V| - 1`，再用 `isTree_iff_connected_and_card` 得 `IsTree`。 -/

/-- **根顶点**。 -/
def rootV {F : Finset (Finset α)} (huniv : (Finset.univ : Finset α) ∈ F) :
    LaminarVertex F := Sum.inl ⟨Finset.univ, huniv⟩

/-- 元素的最小簇（选函数版本，边数计数用）。 -/
noncomputable def minClusterV {F : Finset (Finset α)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F) (x : α) : ↥F :=
  let h := exists_isMinClusterOf (F := F) hl ⟨Finset.univ, huniv, Finset.mem_univ x⟩
  ⟨h.choose, h.choose_spec.1⟩

theorem minClusterV_spec {F : Finset (Finset α)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F) (x : α) :
    IsMinClusterOf F x (minClusterV hl huniv x).1 :=
  (exists_isMinClusterOf (F := F) hl ⟨Finset.univ, huniv, Finset.mem_univ x⟩).choose_spec

/-- 簇的父顶点（`A ≠ univ`）。 -/
noncomputable def parentV {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) (A : ↥F)
    (hA : A.1 ≠ Finset.univ) : ↥F :=
  ⟨parentOf F A.1, (isParentOf_parentOf (A := A.1) hl hne huniv A.2 hA).1⟩

/-- **父顶点函数**：簇 ↦ 其父（根 ↦ 自身）；元素 ↦ 其最小簇。 -/
noncomputable def parV {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) :
    LaminarVertex F → LaminarVertex F
  | Sum.inl A => if h : A.1 = Finset.univ then Sum.inl A
      else Sum.inl (parentV hl hne huniv A h)
  | Sum.inr x => Sum.inl (minClusterV hl huniv x)

/-- **`v` 与其父顶点相邻**（`v ≠ root`）。 -/
theorem adj_parV {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    {v : LaminarVertex F} (hv : v ≠ rootV huniv) :
    (treeGraph F).Adj v (parV hl hne huniv v) := by
  rcases v with A | x
  · show (treeGraph F).Adj (Sum.inl A) _
    rw [show parV hl hne huniv (Sum.inl A) =
        (if h : A.1 = Finset.univ then Sum.inl A
          else Sum.inl (parentV hl hne huniv A h)) from rfl]
    split_ifs with h
    · exact absurd (congrArg Sum.inl (Subtype.ext h)) hv
    · exact (treeGraph_adj_inl_inl F A (parentV hl hne huniv A h)).mpr
        (Or.inl (isParentOf_parentOf (A := A.1) hl hne huniv A.2 h))
  · show (treeGraph F).Adj (Sum.inr x) _
    exact (treeGraph_adj_inr_inl F x (minClusterV hl huniv x)).mpr
      (minClusterV_spec hl huniv x)

/-- `v` 的**父边**。 -/
noncomputable def parEdge {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    (v : LaminarVertex F) : Sym2 (LaminarVertex F) :=
  s(v, parV hl hne huniv v)

/-- **父边是图的边**（`v ≠ root`）—— 即 `range parEdge ⊆ edgeSet`。 -/
theorem parEdge_mem_edgeSet {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    {v : LaminarVertex F} (hv : v ≠ rootV huniv) :
    parEdge hl hne huniv v ∈ (treeGraph F).edgeSet :=
  (SimpleGraph.mem_edgeSet (treeGraph F)).mpr (adj_parV hl hne huniv hv)

/-- **★ 满射**：每条边都由某个非根顶点的 `parEdge` 给出。

四种邻接情形：簇–簇（用 `isParentOf_unique`）· 簇–元素 / 元素–簇（用 `isMinClusterOf_unique`）·
元素–元素（不可能）。 -/
theorem edgeSet_subset_range {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    {e : Sym2 (LaminarVertex F)} (he : e ∈ (treeGraph F).edgeSet) :
    e ∈ (Finset.univ.erase (rootV huniv)).image (parEdge hl hne huniv) := by
  refine Sym2.ind (f := fun e => e ∈ (treeGraph F).edgeSet →
      e ∈ (Finset.univ.erase (rootV huniv)).image (parEdge hl hne huniv)) ?_ e he
  intro u v huv
  rw [SimpleGraph.mem_edgeSet] at huv
  have hne' : ∀ (A : ↥F) (hA : A.1 ≠ Finset.univ),
      parV hl hne huniv (Sum.inl A) = Sum.inl (parentV hl hne huniv A hA) := by
    intro A hA
    exact dif_neg hA
  rcases u with A | x <;> rcases v with B | y
  · -- 簇–簇
    rcases huv with hAB | hBA
    · have hAu : A.1 ≠ Finset.univ := fun h =>
        hAB.2.1.2 (by rw [h]; exact Finset.subset_univ B.1)
      have hPV : parentV hl hne huniv A hAu =
          B := Subtype.ext (isParentOf_unique
            (isParentOf_parentOf (A := A.1) hl hne huniv A.2 hAu) hAB)
      refine Finset.mem_image.mpr ⟨Sum.inl A, ?_, ?_⟩
      · rw [Finset.mem_erase]
        exact ⟨fun h => hAu (congrArg Subtype.val (Sum.inl.inj h)), Finset.mem_univ _⟩
      · show s(Sum.inl A, parV hl hne huniv (Sum.inl A)) = s(Sum.inl A, Sum.inl B)
        rw [hne' A hAu, hPV]
    · have hBu : B.1 ≠ Finset.univ := fun h =>
        hBA.2.1.2 (by rw [h]; exact Finset.subset_univ A.1)
      have hPV : parentV hl hne huniv B hBu =
          A := Subtype.ext (isParentOf_unique
            (isParentOf_parentOf (A := B.1) hl hne huniv B.2 hBu) hBA)
      refine Finset.mem_image.mpr ⟨Sum.inl B, ?_, ?_⟩
      · rw [Finset.mem_erase]
        exact ⟨fun h => hBu (congrArg Subtype.val (Sum.inl.inj h)), Finset.mem_univ _⟩
      · show s(Sum.inl B, parV hl hne huniv (Sum.inl B)) = s(Sum.inl A, Sum.inl B)
        rw [hne' B hBu, hPV, Sym2.eq_swap]
  · -- 簇–元素
    have hPV : minClusterV hl huniv y = A := Subtype.ext (isMinClusterOf_unique
      (minClusterV_spec hl huniv y) huv)
    refine Finset.mem_image.mpr ⟨Sum.inr y, ?_, ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨fun h => Sum.inr_ne_inl h, Finset.mem_univ _⟩
    · show s(Sum.inr y, parV hl hne huniv (Sum.inr y)) = s(Sum.inl A, Sum.inr y)
      rw [show parV hl hne huniv (Sum.inr y) = Sum.inl (minClusterV hl huniv y) from rfl,
        hPV, Sym2.eq_swap]
  · -- 元素–簇
    have hPV : minClusterV hl huniv x = B := Subtype.ext (isMinClusterOf_unique
      (minClusterV_spec hl huniv x) huv)
    refine Finset.mem_image.mpr ⟨Sum.inr x, ?_, ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨fun h => Sum.inr_ne_inl h, Finset.mem_univ _⟩
    · show s(Sum.inr x, parV hl hne huniv (Sum.inr x)) = s(Sum.inr x, Sum.inl B)
      rw [show parV hl hne huniv (Sum.inr x) = Sum.inl (minClusterV hl huniv x) from rfl, hPV]
  · -- 元素–元素：不可能
    exact absurd huv id

/-- **★ 边数上界**：`|E| ≤ |V| - 1`（由满射 + 像集基数）。 -/
theorem card_edgeFinset_le {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) :
    (treeGraph F).edgeFinset.card ≤ Fintype.card (LaminarVertex F) - 1 := by
  have hsub : (treeGraph F).edgeFinset ⊆
      (Finset.univ.erase (rootV huniv)).image (parEdge hl hne huniv) :=
    fun e he => edgeSet_subset_range hl hne huniv (SimpleGraph.mem_edgeFinset.mp he)
  calc (treeGraph F).edgeFinset.card
      ≤ ((Finset.univ.erase (rootV huniv)).image (parEdge hl hne huniv)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase (rootV huniv)).card := Finset.card_image_le
    _ = (Finset.univ : Finset (LaminarVertex F)).card - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ _)
    _ = Fintype.card (LaminarVertex F) - 1 := by rw [Finset.card_univ]

/-- ★★ **`treeGraph F` 是树**（连通 + 边数 `= |V| - 1`）。

上界由满射 `edgeSet_subset_range` 给出，下界由连通性
`Connected.card_vert_le_card_edgeSet_add_one` 给出，夹出等号后用
`isTree_iff_connected_and_card`。 -/
theorem isTree_treeGraph {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F) :
    (treeGraph F).IsTree := by
  have hconn := connected_treeGraph hl hne huniv
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hcardE : Nat.card (treeGraph F).edgeSet = (treeGraph F).edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card]
    exact Nat.card_eq_fintype_card
  have hcardV : Nat.card (LaminarVertex F) = Fintype.card (LaminarVertex F) :=
    Nat.card_eq_fintype_card
  rw [hcardE, hcardV]
  have hlow := card_edgeFinset_le hl hne huniv
  have hhigh : Fintype.card (LaminarVertex F) ≤ (treeGraph F).edgeFinset.card + 1 := by
    have := hconn.card_vert_le_card_edgeSet_add_one
    rwa [hcardV, hcardE] at this
  have hpos : 0 < Fintype.card (LaminarVertex F) :=
    Fintype.card_pos_iff.mpr ⟨rootV huniv⟩
  omega

/-! ### 叶的度 = 1（`leaf_iff_degree_one` 的一半） -/

/-- **元素的邻居恰为「含它的最小簇」**（唯一性由 `isMinClusterOf_unique`）。 -/
theorem neighborFinset_inr {F : Finset (Finset α)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F) (x : α) :
    ∃ A : ↥F, (treeGraph F).neighborFinset (Sum.inr x) = {Sum.inl A} := by
  classical
  obtain ⟨A, hA⟩ := exists_isMinClusterOf (F := F) hl ⟨Finset.univ, huniv, Finset.mem_univ x⟩
  refine ⟨⟨A, hA.1⟩, ?_⟩
  have hsub : (treeGraph F).neighborFinset (Sum.inr x) ⊆ {Sum.inl ⟨A, hA.1⟩} := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    rcases v with B | y
    · rw [treeGraph_adj_inr_inl] at hv
      have hBeq : B = ⟨A, hA.1⟩ := Subtype.ext (isMinClusterOf_unique hv hA)
      rw [hBeq, Finset.mem_singleton]
    · exact absurd hv id
  have hmem : Sum.inl ⟨A, hA.1⟩ ∈ (treeGraph F).neighborFinset (Sum.inr x) := by
    rw [SimpleGraph.mem_neighborFinset, treeGraph_adj_inr_inl]
    exact hA
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)

/-- **★ 元素的度 = 1**（叶边）。 -/
theorem degree_inr_eq_one {F : Finset (Finset α)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F) (x : α) :
    (treeGraph F).degree (Sum.inr x) = 1 := by
  obtain ⟨A, hA⟩ := neighborFinset_inr hl huniv x
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hA, Finset.card_singleton]

/-! ### 非 `univ` 簇的度 ≥ 3（`no_degree_two` 的主体） -/

/-- **★ `treeGraph` 中非 `univ` 簇的度 ≥ 3**。

用**「三元素」方案**：显式构造父 + 两个孩子（或孩子+元素，或两个元素）三个**互异**邻居，
避开 `Finset.image` 的基数论证。 -/
theorem three_le_degree_treeGraph {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    {A : ↥F} (hAuniv : A.1 ≠ Finset.univ) (hcard : 2 ≤ A.1.card) :
    3 ≤ (treeGraph F).degree (Sum.inl A) := by
  classical
  have hPA := isParentOf_parentOf (A := A.1) hl hne huniv A.2 hAuniv
  have hcount : 2 ≤ (F.filter fun B => IsChildOf F A.1 B).card
      + (directElems F A.1).card :=
    two_le_card_children_add_card_directElems hl A.2 hcard
  -- 父不是任一孩子
  have hPnotKid : ∀ {B : Finset α} (hBF : B ∈ F), IsChildOf F A.1 B →
      (⟨B, hBF⟩ : ↥F) ≠ ⟨parentOf F A.1, hPA.1⟩ := by
    intro B hBF hBc hEq
    have hBeq : B = parentOf F A.1 := congrArg Subtype.val hEq
    have h2 : A.1 ⊆ B := by rw [hBeq]; exact hPA.2.1.1
    exact hBc.2.1.2 h2
  have key : ∃ u₂ u₃ : LaminarVertex F, u₂ ≠ Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F) ∧
      u₃ ≠ Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F) ∧ u₂ ≠ u₃ ∧
      (treeGraph F).Adj (Sum.inl A) u₂ ∧ (treeGraph F).Adj (Sum.inl A) u₃ := by
    rcases Nat.lt_or_ge (F.filter fun B => IsChildOf F A.1 B).card 2 with hk | hk
    · have hk01 : (F.filter fun B => IsChildOf F A.1 B).card = 0 ∨
          (F.filter fun B => IsChildOf F A.1 B).card = 1 := by omega
      rcases hk01 with h0 | h1
      · -- 无孩子 ⟹ 至少两个直接元素
        obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (directElems F A.1).card)
        exact ⟨Sum.inr t₁, Sum.inr t₂, fun h => Sum.inr_ne_inl h,
          fun h => Sum.inr_ne_inl h, fun h => ht12 (Sum.inr.inj h),
          (treeGraph_adj_inl_inr F A t₁).mpr (directElems_isMinClusterOf A.2 ht₁),
          (treeGraph_adj_inl_inr F A t₂).mpr (directElems_isMinClusterOf A.2 ht₂)⟩
      · -- 恰一个孩子 + 至少一个直接元素
        obtain ⟨B, hBeq⟩ := Finset.card_eq_one.mp h1
        have hBk : B ∈ F.filter fun B => IsChildOf F A.1 B := by
          rw [hBeq]; exact Finset.mem_singleton_self B
        obtain ⟨hBF, hBchild⟩ := Finset.mem_filter.mp hBk
        obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < (directElems F A.1).card)
        refine ⟨Sum.inl (⟨B, hBF⟩ : ↥F), Sum.inr t,
          fun h => hPnotKid hBF hBchild (Sum.inl_injective h),
          fun h => Sum.inr_ne_inl h, fun h => Sum.inl_ne_inr h,
          (treeGraph_adj_inl_inl F A (⟨B, hBF⟩ : ↥F)).mpr
            (Or.inr (isChildOf_isParentOf hl A.2 (hne B hBF) hBchild)),
          (treeGraph_adj_inl_inr F A t).mpr (directElems_isMinClusterOf A.2 ht)⟩
    · -- 至少两个孩子
      obtain ⟨B₁, hB₁, B₂, hB₂, hB₁₂⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (F.filter fun B => IsChildOf F A.1 B).card)
      obtain ⟨hB₁F, hB₁c⟩ := Finset.mem_filter.mp hB₁
      obtain ⟨hB₂F, hB₂c⟩ := Finset.mem_filter.mp hB₂
      refine ⟨Sum.inl (⟨B₁, hB₁F⟩ : ↥F), Sum.inl (⟨B₂, hB₂F⟩ : ↥F),
        fun h => hPnotKid hB₁F hB₁c (Sum.inl_injective h),
        fun h => hPnotKid hB₂F hB₂c (Sum.inl_injective h),
        fun h => hB₁₂ (congrArg Subtype.val (Sum.inl_injective h)), ?_, ?_⟩
      · exact (treeGraph_adj_inl_inl F A (⟨B₁, hB₁F⟩ : ↥F)).mpr
          (Or.inr (isChildOf_isParentOf hl A.2 (hne B₁ hB₁F) hB₁c))
      · exact (treeGraph_adj_inl_inl F A (⟨B₂, hB₂F⟩ : ↥F)).mpr
          (Or.inr (isChildOf_isParentOf hl A.2 (hne B₂ hB₂F) hB₂c))
  obtain ⟨u₂, u₃, h21, h31, h23, ha2, ha3⟩ := key
  have ha1 : (treeGraph F).Adj (Sum.inl A) (Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F)) :=
    (treeGraph_adj_inl_inl F A (⟨parentOf F A.1, hPA.1⟩ : ↥F)).mpr (Or.inl hPA)
  have hsub : ({Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F)} ∪
      ({u₂, u₃} : Finset (LaminarVertex F))) ⊆
      (treeGraph F).neighborFinset (Sum.inl A) := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert] at hu
    rw [SimpleGraph.mem_neighborFinset]
    rcases hu with rfl | rfl | rfl
    · exact ha1
    · exact ha2
    · exact ha3
  have hd : Disjoint ({Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F)} : Finset (LaminarVertex F))
      ({u₂, u₃} : Finset (LaminarVertex F)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_singleton] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
    subst hu
    rcases hu' with h | h
    · exact h21 h.symm
    · exact h31 h.symm
  have h3card : ({Sum.inl (⟨parentOf F A.1, hPA.1⟩ : ↥F)} ∪
      ({u₂, u₃} : Finset (LaminarVertex F))).card = 3 := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_singleton,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact h23), Finset.card_singleton]
  calc 3 = _ := h3card.symm
    _ ≤ ((treeGraph F).neighborFinset (Sum.inl A)).card := Finset.card_le_card hsub
    _ = (treeGraph F).degree (Sum.inl A) := SimpleGraph.card_neighborFinset_eq_degree _ _

/-! ### 根 `univ` 的度

`univ` 无父 ⟹ `deg(univ) = |孩子| + |直接元素|`。下面在假设 `|孩子| + |直接元素| ≥ 3` 下证明。

⚠️ **`|孩子| + |直接元素| = 2` 是真正的退化情形**（此时 `deg(univ) = 2`），需合并 `univ` 与某簇
—— 见 `MEMORY.md`。 -/

/-- 簇 `B` 的顶点（`B ∉ F` 时取根 `univ`，不影响 `F` 内元素上的单射性）。 -/
noncomputable def kidVOf (F : Finset (Finset α)) (huniv : (Finset.univ : Finset α) ∈ F)
    (B : Finset α) : LaminarVertex F :=
  if h : B ∈ F then Sum.inl ⟨B, h⟩ else Sum.inl (⟨Finset.univ, huniv⟩ : ↥F)

/-- **★ 根的度 ≥ 3**（假设 `|孩子| + |直接元素| ≥ 3`）。

先取 `min |孩子| 3` 个孩子与 `3 - min |孩子| 3` 个元素，其像集恰 3 个点、
两两不交且全为根的邻居。 -/
theorem three_le_degree_rootV {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    (h : 3 ≤ (F.filter fun B => IsChildOf F Finset.univ B).card
        + (directElems F Finset.univ).card) :
    3 ≤ (treeGraph F).degree (Sum.inl (⟨Finset.univ, huniv⟩ : ↥F)) := by
  classical
  set R := (⟨Finset.univ, huniv⟩ : ↥F) with hR
  set kids := F.filter fun B => IsChildOf F Finset.univ B with hkids
  set dirs := directElems F Finset.univ with hdirs
  have hne_kids : ∀ B ∈ kids, B ∈ F := fun B hB => (Finset.mem_filter.mp (hkids ▸ hB)).1
  have hch_kids : ∀ B ∈ kids, IsChildOf F Finset.univ B :=
    fun B hB => (Finset.mem_filter.mp (hkids ▸ hB)).2
  have hne_dirs : ∀ y ∈ dirs, y ∈ directElems F Finset.univ := fun y hy => hdirs ▸ hy
  -- `kidVOf` 在 `kids` 上单射
  have hkidinj : Set.InjOn (kidVOf F huniv) ↑kids := by
    intro B hB C hC hEq
    simp only [kidVOf] at hEq
    rw [dif_pos (hne_kids B hB), dif_pos (hne_kids C hC)] at hEq
    exact congrArg Subtype.val (Sum.inl_injective hEq)
  -- 每个孩子都是根的邻居
  have hchild : ∀ B ∈ kids, (treeGraph F).Adj (Sum.inl R) (kidVOf F huniv B) := by
    intro B hB
    rw [kidVOf, dif_pos (hne_kids B hB)]
    exact (treeGraph_adj_inl_inl F R (⟨B, hne_kids B hB⟩ : ↥F)).mpr
      (Or.inr (isChildOf_isParentOf (A := Finset.univ) hl huniv (hne B (hne_kids B hB))
        (hch_kids B hB)))
  -- 每个直接元素都是根的邻居
  have hdir : ∀ y ∈ dirs, (treeGraph F).Adj (Sum.inl R) (Sum.inr y) := fun y hy =>
    (treeGraph_adj_inl_inr F R y).mpr
      (directElems_isMinClusterOf (A := Finset.univ) huniv (hne_dirs y hy))
  -- 取 `min |kids| 3` 个孩子
  obtain ⟨ks, hkssub, hkscard⟩ := Finset.exists_subset_card_eq (s := kids) (min_le_left _ _)
  have hkscard' : ks.card = min kids.card 3 := hkscard
  have hjd : 3 - ks.card ≤ dirs.card := by
    have h1 : ks.card ≤ kids.card := Finset.card_le_card hkssub
    rw [hkscard']; omega
  obtain ⟨ds, hdsub, hdscard⟩ := Finset.exists_subset_card_eq (s := dirs) hjd
  -- 像集
  set S := (ks.image (kidVOf F huniv)) ∪ (ds.image (Sum.inr : α → LaminarVertex F)) with hS
  have hks_inj : Set.InjOn (kidVOf F huniv) ↑ks :=
    hkidinj.mono (fun x hx => hkssub hx)
  have hds_inj : Set.InjOn (Sum.inr : α → LaminarVertex F) ↑ds :=
    fun a _ b _ h => Sum.inr_injective h
  have hdisj : Disjoint (ks.image (kidVOf F huniv)) (ds.image (Sum.inr : α → LaminarVertex F)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨B, hBks, hBu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, -, hyu⟩ := Finset.mem_image.mp hu'
    have hEq : kidVOf F huniv B = Sum.inr y := by rw [hBu, ← hyu]
    rw [kidVOf, dif_pos (hne_kids B (hkssub hBks))] at hEq
    exact Sum.inl_ne_inr hEq
  have hScard : S.card = 3 := by
    rw [hS, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn hks_inj, Finset.card_image_of_injOn hds_inj,
      hkscard', hdscard]
    omega
  have hSsub : S ⊆ (treeGraph F).neighborFinset (Sum.inl R) := by
    intro u hu
    rw [hS] at hu
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hu
      exact hchild B (hkssub hB)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
      exact hdir y (hdsub hy)
  calc 3 = S.card := hScard.symm
    _ ≤ ((treeGraph F).neighborFinset (Sum.inl R)).card := Finset.card_le_card hSsub
    _ = (treeGraph F).degree (Sum.inl R) := SimpleGraph.card_neighborFinset_eq_degree _ _

/-- ★★ **`treeGraph` 无度 2 顶点**（`Cladogram.no_degree_two` 字段）。

假设：
* 族元素 `card ≥ 2` 或为 `univ`（即 `F` 已正规化：无单元素簇）；
* `|univ 的孩子| + |univ 的直接元素| ≥ 3`（**唯一真正的退化情形，见 `MEMORY.md`**）。

三种顶点分别：元素度 1 · 非 `univ` 簇度 ≥ 3 · `univ` 度 ≥ 3。 -/
theorem no_degree_two_treeGraph {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card)
    (hroot : 3 ≤ (F.filter fun B => IsChildOf F Finset.univ B).card
        + (directElems F Finset.univ).card) :
    ∀ v : LaminarVertex F, (treeGraph F).degree v ≠ 2 := by
  intro v
  rcases v with A | x
  · by_cases hAu : A.1 = Finset.univ
    · have hAeq : A = (⟨Finset.univ, huniv⟩ : ↥F) := Subtype.ext hAu
      rw [hAeq]
      have h3 := three_le_degree_rootV hl hne huniv hroot
      omega
    · have hAc : 2 ≤ A.1.card := by
        rcases hcard A.1 A.2 with h | h
        · exact absurd h hAu
        · exact h
      have h3 := three_le_degree_treeGraph hl hne huniv hAu hAc
      omega
  · have h1 := degree_inr_eq_one hl huniv x
    omega

/-! ## ★★★ 终点：由镶嵌族构造 `Cladogram`（「相容 ⟹ 存在树」）

组装所有字段：`V := LaminarVertex F` · `graph := treeGraph F` · `leaf := Sum.inr`
· `isTree`（`isTree_treeGraph`）· `no_degree_two`（`no_degree_two_treeGraph`）
· `leaf_iff_degree_one`（元素度 1 ／ 簇度 ≥ 3）。 -/

set_option maxHeartbeats 800000 in
/-- **由镶嵌族构造 cladogram**。

假设：
* `F` 镶嵌、`univ ∈ F`、族元素非空；
* `F` 已正规化（无单元素簇）：`∀ B ∈ F, B = univ ∨ 2 ≤ B.card`；
* 根非退化：`|univ 的孩子| + |univ 的直接元素| ≥ 3`。 -/
noncomputable def toCladogram {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card)
    (hroot : 3 ≤ (F.filter fun B => IsChildOf F Finset.univ B).card
        + (directElems F Finset.univ).card) :
    Cladogram α where
  V := LaminarVertex F
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := treeGraph F
  decAdj := Classical.decRel _
  isTree := isTree_treeGraph hl hne huniv
  leaf := ⟨Sum.inr, Sum.inr_injective⟩
  leaf_iff_degree_one := by
    intro v
    constructor
    · rintro ⟨x, rfl⟩
      exact degree_inr_eq_one hl huniv x
    · intro hv
      rcases v with A | x
      · by_cases hAu : A.1 = Finset.univ
        · have hAeq : A = (⟨Finset.univ, huniv⟩ : ↥F) := Subtype.ext hAu
          rw [hAeq] at hv
          have h3 := three_le_degree_rootV hl hne huniv hroot
          omega
        · have hAc : 2 ≤ A.1.card := by
            rcases hcard A.1 A.2 with h | h
            · exact absurd h hAu
            · exact h
          have h3 := three_le_degree_treeGraph hl hne huniv hAu hAc
          omega
      · exact ⟨x, rfl⟩
  no_degree_two := no_degree_two_treeGraph hl hne huniv hcard hroot

/-! ## 退化情形（`|孩子| + |直接元素| ≤ 2`）

**方案：删掉一个极大簇 `A`**（等价于「把 `univ` 与 `A` 合并」）——
删掉 `A` 后，`A` 的孩子直接挂 `univ`、`A` 的直接元素成为 `univ` 的直接元素，
于是 `univ` 的度数增加。下面先证两条「删除后结构」引理。 -/

/-- **删掉极大簇后，它的孩子成为 `univ` 的孩子**。 -/
theorem isChildOf_erase_of_isChildOf (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty)
    {A : Finset α} (hA : IsChildOf F Finset.univ A) {C : Finset α}
    (hC : IsChildOf F A C) : IsChildOf (F.erase A) Finset.univ C := by
  obtain ⟨hCF, hCA, hCmax⟩ := hC
  obtain ⟨hAF, hAlt, hAmax⟩ := hA
  have hAne : A ≠ Finset.univ := fun h => hAlt.2 (by rw [h])
  have hCneA : C ≠ A := fun h => hCA.2 (by rw [h])
  refine ⟨Finset.mem_erase.mpr ⟨hCneA, hCF⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨hCA.1.trans hAlt.1, fun h => ?_⟩, ?_⟩
  · rw [h] at hCA
    exact hCA.2 (Finset.subset_univ A)
  · intro B hB hCB
    rw [Finset.mem_erase] at hB
    obtain ⟨hBneA, hBF⟩ := hB
    intro hBlt
    rcases hl A hAF B hBF with hAB | hBA | hd
    · exact (hAmax B hBF (Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hBneA.symm⟩)) hBlt
    · exact hCmax B hBF hCB (Finset.ssubset_iff_subset_ne.mpr ⟨hBA, hBneA⟩)
    · exfalso
      obtain ⟨c, hc⟩ := hne C hCF
      have hmem : c ∈ A ∩ B := Finset.mem_inter.mpr ⟨hCA.1 hc, hCB.1 hc⟩
      rw [Finset.disjoint_iff_inter_eq_empty] at hd
      rw [hd] at hmem
      exact Finset.notMem_empty c hmem

/-- **删掉极大簇后，它的直接元素成为 `univ` 的直接元素**（因 `univ` 包含一切）。 -/
theorem isMinClusterOf_erase_of_directElems (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset α) ∈ F) {A : Finset α}
    (hA : IsChildOf F Finset.univ A) {x : α} (hx : x ∈ directElems F A) :
    IsMinClusterOf (F.erase A) x Finset.univ := by
  obtain ⟨hxA, hxmin⟩ := mem_directElems.mp hx
  have hAne : A ≠ Finset.univ := fun h => hA.2.1.2 (by rw [h])
  refine ⟨Finset.mem_erase.mpr ⟨fun h => hAne h.symm, huniv⟩, Finset.mem_univ x, ?_⟩
  intro C hC hxC
  rw [Finset.mem_erase] at hC
  obtain ⟨hCneA, hCF⟩ := hC
  have hAC : A ⊆ C := hxmin C hCF hxC
  have hCuniv : C = Finset.univ := by
    by_contra h
    exact (hA.2.2 C hCF
      (Finset.ssubset_iff_subset_ne.mpr ⟨hAC, fun h' => hCneA h'.symm⟩))
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ C, h⟩)
  rw [hCuniv]

/-- ★★ **除根外所有顶点度 ≠ 2**（`no_degree_two` 的「弱化版」）。

**这就是退化情形的完整结论**：若 `|univ 的孩子| + |univ 的直接元素| = 2`，则 `deg(univ) = 2`
（根是**唯一**的度 2 顶点）。此时树仍是合法的**实现树**（`IsTree` + 叶嵌入 + 叶度为 1），
只是不满足 `Cladogram` 的 `no_degree_two` 正规化条件。

**消除这个唯一障碍需要改图**：把 `univ` 从顶点集中去掉、让它两个「孩子」（极大簇/未覆盖元素）
直接相连 —— 见 `MEMORY.md`（这与 `isChildOf_erase_of_isChildOf` 的思路一致）。
使 `univ` 的度 ≥ 3（即 `hroot`）是**充分**的替代条件。 -/
theorem no_degree_two_except_root {F : Finset (Finset α)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset α) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card) :
    ∀ v : LaminarVertex F, v ≠ Sum.inl (⟨Finset.univ, huniv⟩ : ↥F) →
      (treeGraph F).degree v ≠ 2 := by
  intro v hv
  rcases v with A | x
  · by_cases hAu : A.1 = Finset.univ
    · exact absurd (congrArg Sum.inl (Subtype.ext hAu)) hv
    · have hAc : 2 ≤ A.1.card := by
        rcases hcard A.1 A.2 with h | h
        · exact absurd h hAu
        · exact h
      have h3 := three_le_degree_treeGraph hl hne huniv hAu hAc
      omega
  · have h1 := degree_inr_eq_one hl huniv x
    omega

/-! ## ② 簇 ↔ split 的字典：`B` 的子树叶集恰为 `B`

「规范 cluster 集 `F` 的每个非 `univ` 成员 `B` 对应一条边，其两侧为 `B` 与 `X ∖ B`」。

第一步（本段）：**`B` 的子树叶集 = `B`**。用「最小簇含于 `B`」刻画子树叶集 ——
由镶嵌性 + 最小簇性，`x ∈ B` ⟺ `x` 的最小簇 `⊆ B`。 -/

/-- `B` 的**子树叶集**：最小簇含于 `B` 的叶。 -/
noncomputable def leavesOf (F : Finset (Finset α)) (B : Finset α) : Finset α :=
  Finset.univ.filter fun x => ∃ A ∈ F, IsMinClusterOf F x A ∧ A ⊆ B

theorem mem_leavesOf {F : Finset (Finset α)} {B : Finset α} {x : α} :
    x ∈ leavesOf F B ↔ ∃ A ∈ F, IsMinClusterOf F x A ∧ A ⊆ B := by
  classical
  simp [leavesOf]

/-- ★★ **`B` 的子树叶集恰为 `B`**（`B ∈ F`）。

* `⊆`：最小簇 `A ⊆ B` ⟹ `x ∈ A ⊆ B`；
* `⊇`：`x ∈ B` ⟹ 取 `x` 的最小簇 `A`；由镶嵌性 `A ⊆ B`，或 `B ⊆ A`（此时 `A ⊆ B` 由最小簇性）。 -/
theorem leavesOf_eq {F : Finset (Finset α)} (hl : LaminarFamily F)
    {B : Finset α} (hB : B ∈ F) : leavesOf F B = B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A, -, hmin, hAB⟩ := mem_leavesOf.mp hx
    exact hAB hmin.2.1
  · intro hx
    refine mem_leavesOf.mpr ?_
    obtain ⟨A, hmin⟩ := exists_isMinClusterOf (F := F) hl ⟨B, hB, hx⟩
    exact ⟨A, hmin.1, hmin, isMinClusterOf_subset hmin hB hx⟩

end Phylo
