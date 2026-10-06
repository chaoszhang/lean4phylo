/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Phylo.Split

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

镶嵌性 ⟹ 严格包含者两两嵌套 ⟹ 取交集即得最小者（`Finset.inf'`）。
无严格包含者时返回 `univ`（视为根，调用处再作区分）。 -/
noncomputable def parentOf (F : Finset (Finset α)) (A : Finset α) : Finset α :=
  if h : (strictSups F A).Nonempty then
    (strictSups F A).inf' h id
  else Finset.univ

variable {F : Finset (Finset α)}

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

/-! ### 父关系（「最小严格包含者」的特征性质）

用**特征性质**而非选函数定义父关系 —— 免去 `Finset.inf'` 的选择与引理麻烦，
且「最小性」（`∀ C ∈ F, A ⊊ C → B ⊆ C`）正是建图所需的。 -/

/-- **`B` 是 `A`（在族 `F` 中）的父**：`B ∈ F`，`A ⊊ B`，且 `B` 含于任一严格包含 `A` 的族成员。 -/
def IsParentOf (F : Finset (Finset α)) (A B : Finset α) : Prop :=
  B ∈ F ∧ A ⊂ B ∧ ∀ C ∈ F, A ⊂ C → B ⊆ C

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

end Phylo
