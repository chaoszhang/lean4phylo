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

end Phylo
