/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Aho

/-!
# `Phylo.RootedTriplet` —— 有根三元组与 **Aho 的有根一致性定理**（NEXT.md P0-D **F7**）

**文献**

* Aho, Sagiv, Szymanski & Ullman, *Inferring a tree from lowest common ancestors with an
  application to the optimization of relational expressions*, SIAM J. Comput. **10**(3)
  (1981) 405–421 —— `references/md/AhoSagivSzymanskiUllman1981_InferringTreeLCA.md`
  （BUILD 算法：**393–398 行**；**Theorem 1**（可靠性）：**400–402 行**；
  完备性证明：**783–798 行**；划分 `π_C` 的三条规则：**375–380 行**）。
* Bryant & Steel, *Extension operations on sets of leaf-labelled trees*, Adv. Appl. Math.
  **16** (1995) 415–430 —— `references/md/BryantSteel1995_ExtensionOperationsLeafLabelledTrees.md`
  （有根三元组 `ab|c` 的定义：**227–229 行**；`ONETREE`：**365–388 行**；
  **Theorem 2**（相容 ⟺ 每个至少 3 叶的子集上图不连通）：**766–769 行**）。
  ⚠️ 任务书称该文「未到手 / 需重下」——**实际在手**（md 全文 + `references/ocr/` 30 页 OCR）。

## 有根三元组 `ab|c`

`ab|c` 表示「叶 `a` 与 `b` 彼此比它们各自与 `c` 更近」，等价于
`lca(a,b)` 是 `lca(a,c)` 的**真后代**（Bryant–Steel 1995, 340–342 行）。

本文件取**等价的团（clade）刻画**（自证，见 `displaysTriplet_iff_isRootedClade`）：

> `T` 展示 `ab|c` **⟺** 存在 `T` 的一条边 `e`，其**远离根**的一侧叶集 `C` 满足
> `a, b ∈ C` 且 `c ∉ C`。

⚠️ 「远离根」这一限定是**实质性的**：若只要求「某条边的某一侧含 `a,b` 而不含 `c`」，
则在 `((a,c),b)` 上 `ab|c` 会被误判为成立（取叶边 `(·,c)` 的**近根**一侧 `{a,b}`）。

## Aho 的递归判据（BUILD）

`AhoOK R`（§3）是 BUILD 的递归判据；`tripletBlocks S R` 就是 Bryant–Steel 的图
`[R,S]`（**744–747 行**）的连通分支分解，即 Aho 的划分 `π_C`（**375–380 行**）：

* `|S| ≤ 1`：成功；
* 否则：块数必须 `≥ 2`，且每个块递归成功。

★★★ `exists_rootedTree_of_ahoOK`：`AhoOK R ⟹ ∃` 有根树 `T` 展示 `R` 的每个三元组。

## 与 `Phylo/Aho.lean` 的关系（**库内已有覆盖的说明**）

`Aho.lean` 的 ★★★ `compatible_exists_rootedTree` 与 `Laminar.lean` 的
`toRootedTreeOfCard` / `leafSide_parentEdge_of_card` 已覆盖**无根 split 系统**的
「两两相容 ⟹ 存在展示它的树」。本文件：

* **复用** `toRootedTreeOfCard` 与 `leafSide_parentEdge_of_card` 作为**建树引擎**
  （`exists_rootedTree_of_laminar`）；
* **不重复**无根结论；新增的实质内容是**有根三元组语言层 + BUILD 递归**。
* 之所以不能把 `compatible_exists_rootedTree` 直接用在三元组上：**有根三元组的相容性
  不能两两判定** —— 例如 `{ab|c, ac|d, ad|b}`（四个叶 `a,b,c,d`）两两相容而整体不相容
  （Bryant–Steel 1995 Theorem 2 中 `[R,L]` 连通即反例）。
  **W11a/F7 已把该反例形式化**：见 **§5**（有根团的**镶嵌性** `isRootedClade_laminar`）
  与 **§6**（`fourLeafCounterexample` · `pairwiseCompatible_not_sufficient` ·
  `not_displayedByTree_fourLeafCounterexample`）；并给出**显式缺口**
  `rootedTriplet_aho_disconnect_gap` / `rootedTriplet_aho_converse_gap`。
-/

open Phylo

namespace Phylo

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 有根三元组 `ab|c`

用 `Finset X × X` 上的**子类型**表示：第一个分量是近对 `{a,b}`（2 元），第二个分量是外侧叶 `c`。
子类型自动继承 `DecidableEq` / `Fintype`。 -/

/-- **有根三元组** `ab|c`：`(pair, out)`，其中 `pair` 是近对（恰 2 元），`out` 是外侧叶。 -/
abbrev RootedTriplet (X : Type u) := {p : Finset X × X // p.1.card = 2 ∧ p.2 ∉ p.1}

namespace RootedTriplet

/-- 近对 `{a,b}`。 -/
def pair (t : RootedTriplet X) : Finset X := t.1.1

/-- 外侧叶 `c`。 -/
def out (t : RootedTriplet X) : X := t.1.2

/-- `ab|c`（要求 `a,b,c` 两两不同）。 -/
def mk' (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : RootedTriplet X :=
  ⟨(({a, b} : Finset X), c), Finset.card_pair_eq_two_iff.mpr hab, by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac.symm, hbc.symm⟩⟩

variable (t : RootedTriplet X)

omit [Fintype X] [DecidableEq X] in
/-- 近对恰有 2 元。 -/
theorem card_pair (t : RootedTriplet X) : t.pair.card = 2 := t.2.1

omit [Fintype X] [DecidableEq X] in
/-- 外侧叶不属于近对。 -/
theorem out_notMem (t : RootedTriplet X) : t.out ∉ t.pair := t.2.2

/-- 支撑集（三个叶）。 -/
def leaves (t : RootedTriplet X) : Finset X := t.pair ∪ {t.out}

omit [Fintype X] in
/-- 支撑集恰有 3 元。 -/
theorem card_leaves (t : RootedTriplet X) : t.leaves.card = 3 := by
  rw [leaves, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr t.out_notMem),
    t.card_pair, Finset.card_singleton]

omit [Fintype X] in
/-- 外侧叶属于支撑集。 -/
theorem out_mem_leaves (t : RootedTriplet X) : t.out ∈ t.leaves := by
  rw [leaves]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

omit [Fintype X] in
/-- 近对含于支撑集。 -/
theorem pair_subset_leaves (t : RootedTriplet X) : t.pair ⊆ t.leaves :=
  fun _ hx => Finset.mem_union_left _ hx

omit [Fintype X] [DecidableEq X] in
/-- 近对非空。 -/
theorem pair_nonempty (t : RootedTriplet X) : t.pair.Nonempty :=
  Finset.card_pos.mp (by rw [t.card_pair]; norm_num)

omit [Fintype X] in
/-- 近对可写成 `{a,b}`（`a ≠ b`）。 -/
theorem exists_pair_eq (t : RootedTriplet X) : ∃ a b : X, a ≠ b ∧ t.pair = {a, b} :=
  Finset.card_eq_two.mp t.card_pair

omit [Fintype X] [DecidableEq X] in
/-- **外延性**：`pair` 与 `out` 决定三元组。 -/
@[ext] theorem ext {t t' : RootedTriplet X} (h1 : t.pair = t'.pair) (h2 : t.out = t'.out) :
    t = t' :=
  Subtype.ext (Prod.ext h1 h2)

omit [Fintype X] in
/-- `mk'` 的近对就是 `{a,b}`。 -/
@[simp] theorem pair_mk' (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (mk' a b c hab hac hbc).pair = {a, b} := rfl

omit [Fintype X] in
/-- `mk'` 的外侧叶就是 `c`。 -/
@[simp] theorem out_mk' (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (mk' a b c hab hac hbc).out = c := rfl

end RootedTriplet

/-! ## 2. 树展示三元组；三元组 ⟺ 团（clade） -/

namespace RootedTree

variable (T : RootedTree X)

/-- `T` **展示** `ab|c`：存在一条边，其**远离根**的一侧叶集含 `a,b` 而不含 `c`。

（`¬ DeleteEdges.Reachable T.root p` 正是「`p` 在 `e` 的远根一侧」——
`T - e` 把 `T` 分成两个分量，根在其中一个里，故恰好一个端点满足此式。） -/
def DisplaysTriplet (t : RootedTriplet X) : Prop :=
  ∃ (p q : T.V) (_ : T.graph.Adj p q),
    ¬ (T.graph.deleteEdges {s(p, q)}).Reachable T.root p ∧
      t.pair ⊆ T.sideLeaves s(p, q) p ∧ t.out ∉ T.sideLeaves s(p, q) p

/-- `C` 是 `T` 的**有根团**（clade）：恰为某条边**远离根**一侧的叶集。 -/
def IsRootedClade (C : Finset X) : Prop :=
  ∃ (p q : T.V) (_ : T.graph.Adj p q),
    ¬ (T.graph.deleteEdges {s(p, q)}).Reachable T.root p ∧ C = T.sideLeaves s(p, q) p

omit [DecidableEq X] in
/-- ★ **三元组 ⟺ 团**（三元组语言的「成员关系」表述）。 -/
theorem displaysTriplet_iff_isRootedClade (t : RootedTriplet X) :
    T.DisplaysTriplet t ↔ ∃ C : Finset X, T.IsRootedClade C ∧ t.pair ⊆ C ∧ t.out ∉ C := by
  constructor
  · rintro ⟨p, q, hpq, hroot, hsub, hout⟩
    exact ⟨_, ⟨p, q, hpq, hroot, rfl⟩, hsub, hout⟩
  · rintro ⟨C, ⟨p, q, hpq, hroot, rfl⟩, hsub, hout⟩
    exact ⟨p, q, hpq, hroot, hsub, hout⟩

omit [DecidableEq X] in
/-- **团 ⟹ 三元组**（直接由刻画式得到）。 -/
theorem displaysTriplet_of_isRootedClade {t : RootedTriplet X} {C : Finset X}
    (hC : T.IsRootedClade C) (hsub : t.pair ⊆ C) (hout : t.out ∉ C) : T.DisplaysTriplet t :=
  (T.displaysTriplet_iff_isRootedClade t).mpr ⟨C, hC, hsub, hout⟩

/-- ★ **团 ⟹ split**：有根团 `C`（补集非空）给出 `T` 展示的一条 split `C | Cᶜ`。

这是「三元组语言」与 `Phylo.Split` 的接口；⚠️ **反向不成立**：
`IsSplitOf s` 只要求 `s.sideA` 是边的**某一侧**（可以靠根），
而展示 `ab|c` 要求那一侧**远离根**。见文件头注。 -/
theorem isSplitOf_of_isRootedClade {C : Finset X} (hC : T.IsRootedClade C)
    (hne : C.Nonempty) (hcn : Cᶜ.Nonempty) : T.IsSplitOf (splitOf C hne hcn) := by
  obtain ⟨p, q, hpq, hroot, rfl⟩ := hC
  exact ⟨p, q, hpq, p, by rw [splitOf_sideA]⟩

/-- 团给出的 split 在**无根意义**下也被 `T` 展示。 -/
theorem displaysSplit_of_isRootedClade {C : Finset X} (hC : T.IsRootedClade C)
    (hne : C.Nonempty) (hcn : Cᶜ.Nonempty) : T.DisplaysSplit (splitOf C hne hcn) :=
  Or.inl (T.isSplitOf_of_isRootedClade hC hne hcn)

end RootedTree

/-! ## 3. Aho/BUILD：三元组图、块分解与递归判据 -/

/-- `[R,S]`——Bryant–Steel 1995（**744–747 行**）的**边标号图**的底图。

顶点 `S`；`ab|c ∈ R` 且 `a,b,c ∈ S` 时连边 `{a,b}`。
（标号 `c ↦ {x : ab|x ∈ R, x ∈ S}` 在连通性判定中不需要，故略去。） -/
def tripletGraph (S : Finset X) (R : Finset (RootedTriplet X)) : SimpleGraph ↥S where
  Adj a b := a ≠ b ∧ ∃ t ∈ R, t.leaves ⊆ S ∧ a.1 ∈ t.pair ∧ b.1 ∈ t.pair
  symm := ⟨fun a b h => ⟨h.1.symm, by
    obtain ⟨t, ht, hS, ha, hb⟩ := h.2
    exact ⟨t, ht, hS, hb, ha⟩⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

omit [Fintype X] in
/-- `tripletGraph` 的邻接展开。 -/
@[simp] theorem tripletGraph_adj {S : Finset X} {R : Finset (RootedTriplet X)} {a b : ↥S} :
    (tripletGraph S R).Adj a b ↔
      a ≠ b ∧ ∃ t ∈ R, t.leaves ⊆ S ∧ a.1 ∈ t.pair ∧ b.1 ∈ t.pair := Iff.rfl

/-- `a` 在 `S` 中的**连通分支**（叶集视角）。 -/
noncomputable def compSet (S : Finset X) (R : Finset (RootedTriplet X)) (a : ↥S) : Finset X := by
  classical
  exact (S.attach.filter fun b => (tripletGraph S R).Reachable a b).image Subtype.val

omit [Fintype X] in
/-- `compSet` 的成员判定。 -/
theorem mem_compSet {S : Finset X} {R : Finset (RootedTriplet X)} {a : ↥S} {b : X} :
    b ∈ compSet S R a ↔ ∃ hb : b ∈ S, (tripletGraph S R).Reachable a ⟨b, hb⟩ := by
  classical
  rw [compSet, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hcb⟩
    rw [Finset.mem_filter] at hc
    have : b = c.1 := hcb.symm
    subst this
    exact ⟨c.2, hc.2⟩
  · rintro ⟨hb, hr⟩
    exact ⟨⟨b, hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach S ⟨b, hb⟩, hr⟩, rfl⟩

omit [Fintype X] in
/-- 连通分支含于 `S`。 -/
theorem compSet_subset (S : Finset X) (R : Finset (RootedTriplet X)) (a : ↥S) :
    compSet S R a ⊆ S := fun _ hb => (mem_compSet.mp hb).1

omit [Fintype X] in
/-- 连通分支非空。 -/
theorem compSet_nonempty (S : Finset X) (R : Finset (RootedTriplet X)) (a : ↥S) :
    (compSet S R a).Nonempty :=
  ⟨a.1, mem_compSet.mpr ⟨a.2, SimpleGraph.Reachable.refl a⟩⟩

omit [Fintype X] in
/-- `a` 属于自己的连通分支。 -/
theorem self_mem_compSet (S : Finset X) (R : Finset (RootedTriplet X)) (a : ↥S) :
    a.1 ∈ compSet S R a :=
  mem_compSet.mpr ⟨a.2, SimpleGraph.Reachable.refl a⟩

omit [Fintype X] in
/-- **连通分支由可达性决定**。 -/
theorem compSet_eq_of_reachable {S : Finset X} {R : Finset (RootedTriplet X)} {a b : ↥S}
    (h : (tripletGraph S R).Reachable a b) : compSet S R a = compSet S R b := by
  classical
  ext x
  rw [mem_compSet, mem_compSet]
  constructor
  · rintro ⟨hx, hr⟩; exact ⟨hx, h.symm.trans hr⟩
  · rintro ⟨hx, hr⟩; exact ⟨hx, h.trans hr⟩

/-- `S` 关于 `R` 的**块分解** = Aho 的划分 `π_C` = Bryant–Steel 图 `[R,S]` 的连通分支集。 -/
noncomputable def tripletBlocks (S : Finset X) (R : Finset (RootedTriplet X)) :
    Finset (Finset X) :=
  (Finset.univ : Finset ↥S).image (compSet S R)

omit [Fintype X] in
/-- 块分解的成员判定。 -/
theorem mem_tripletBlocks {S : Finset X} {R : Finset (RootedTriplet X)} {B : Finset X} :
    B ∈ tripletBlocks S R ↔ ∃ a : ↥S, compSet S R a = B := by
  classical
  rw [tripletBlocks, Finset.mem_image]
  exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Finset.mem_univ _, h⟩⟩

omit [Fintype X] in
/-- 每个块含于 `S`。 -/
theorem tripletBlocks_subset (S : Finset X) (R : Finset (RootedTriplet X)) {B : Finset X}
    (hB : B ∈ tripletBlocks S R) : B ⊆ S := by
  obtain ⟨a, rfl⟩ := mem_tripletBlocks.mp hB
  exact compSet_subset S R a

omit [Fintype X] in
/-- 每个块非空。 -/
theorem tripletBlocks_nonempty (S : Finset X) (R : Finset (RootedTriplet X)) {B : Finset X}
    (hB : B ∈ tripletBlocks S R) : B.Nonempty := by
  obtain ⟨a, rfl⟩ := mem_tripletBlocks.mp hB
  exact compSet_nonempty S R a

omit [Fintype X] in
/-- **块覆盖 `S`**。 -/
theorem exists_mem_tripletBlocks (S : Finset X) (R : Finset (RootedTriplet X)) {x : X}
    (hx : x ∈ S) : ∃ B ∈ tripletBlocks S R, x ∈ B := by
  classical
  exact ⟨compSet S R ⟨x, hx⟩, mem_tripletBlocks.mpr ⟨⟨x, hx⟩, rfl⟩,
    self_mem_compSet S R ⟨x, hx⟩⟩

omit [Fintype X] in
/-- **不同块互不相交**。 -/
theorem tripletBlocks_disjoint {S : Finset X} {R : Finset (RootedTriplet X)} {B B' : Finset X}
    (hB : B ∈ tripletBlocks S R) (hB' : B' ∈ tripletBlocks S R) (hne : B ≠ B') :
    Disjoint B B' := by
  classical
  obtain ⟨a, rfl⟩ := mem_tripletBlocks.mp hB
  obtain ⟨a', rfl⟩ := mem_tripletBlocks.mp hB'
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨hxS, hr⟩ := mem_compSet.mp hx
  obtain ⟨hxS', hr'⟩ := mem_compSet.mp hx'
  have hxx : (tripletGraph S R).Reachable (⟨x, hxS⟩ : ↥S) ⟨x, hxS'⟩ := by
    have hEq : (⟨x, hxS⟩ : ↥S) = ⟨x, hxS'⟩ := Subtype.ext rfl
    rw [hEq]
  exact hne (compSet_eq_of_reachable (hr.trans (hxx.trans hr'.symm)))

omit [Fintype X] in
/-- **块数 `≥ 2` ⟹ 每个块是 `S` 的真子集**。 -/
theorem tripletBlocks_ssubset_of_two_le_card {S : Finset X} {R : Finset (RootedTriplet X)}
    (h : 2 ≤ (tripletBlocks S R).card) {B : Finset X} (hB : B ∈ tripletBlocks S R) :
    B ⊂ S := by
  classical
  have hBsub : B ⊆ S := tripletBlocks_subset S R hB
  have hne : B ≠ S := by
    intro hBS
    obtain ⟨B₁, hB₁, B₂, hB₂, h12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (tripletBlocks S R).card)
    rcases eq_or_ne B₁ B with h1 | h1
    · have hne₂ : B ≠ B₂ := fun hh => h12 (by rw [h1, hh])
      have hdisj := tripletBlocks_disjoint hB hB₂ hne₂
      obtain ⟨y, hy⟩ := tripletBlocks_nonempty S R hB₂
      have hyS : y ∈ S := tripletBlocks_subset S R hB₂ hy
      have hyB : y ∈ B := by rw [hBS]; exact hyS
      exact (Finset.disjoint_left.mp hdisj) hyB hy
    · have hne₁ : B ≠ B₁ := fun hh => h1 hh.symm
      have hdisj := tripletBlocks_disjoint hB hB₁ hne₁
      obtain ⟨y, hy⟩ := tripletBlocks_nonempty S R hB₁
      have hyS : y ∈ S := tripletBlocks_subset S R hB₁ hy
      have hyB : y ∈ B := by rw [hBS]; exact hyS
      exact (Finset.disjoint_left.mp hdisj) hyB hy
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, hne⟩

omit [Fintype X] in
/-- **近对落在某个块里**（`t` 的全部叶都在 `S` 中时）。 -/
theorem exists_block_of_pair {S : Finset X} {R : Finset (RootedTriplet X)}
    {t : RootedTriplet X} (ht : t ∈ R) (hS : t.leaves ⊆ S) :
    ∃ B ∈ tripletBlocks S R, t.pair ⊆ B := by
  classical
  obtain ⟨a, b, hab, hp⟩ := t.exists_pair_eq
  have hleaves : t.leaves = {a, b} ∪ {t.out} := by rw [RootedTriplet.leaves, hp]
  have haS : a ∈ S := by
    refine hS ?_
    rw [hleaves]
    exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hbS : b ∈ S := by
    refine hS ?_
    rw [hleaves]
    exact Finset.mem_union_left _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨compSet S R ⟨a, haS⟩, mem_tripletBlocks.mpr ⟨⟨a, haS⟩, rfl⟩, ?_⟩
  have haP : a ∈ t.pair := by rw [hp]; exact Finset.mem_insert_self _ _
  have hbP : b ∈ t.pair := by
    rw [hp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  intro x hx
  rw [hp, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxa | hxb
  · rw [hxa]; exact self_mem_compSet S R ⟨a, haS⟩
  · rw [hxb]
    refine mem_compSet.mpr ⟨hbS, ?_⟩
    have hadj : (tripletGraph S R).Adj (⟨a, haS⟩ : ↥S) ⟨b, hbS⟩ := by
      refine ⟨?_, t, ht, hS, haP, hbP⟩
      intro hEq
      exact hab (congrArg Subtype.val hEq)
    exact hadj.reachable

/-- **Aho 的递归相容判据**（BUILD / ONETREE 的成功条件）。

* `small`：`|S| ≤ 1`，成功；
* `step`：`|S| ≥ 2` 时块数 `≥ 2`，且每个块递归成功。

（Aho et al. 1981 的三条规则（**375–380 行**）在**三元组**上退化为「近对图」的连通分支：
规则 (1) 给边 `{a,b}`（来自约束 `(a,b) < (a,c)`）；规则 (2) 的前提是 `a,c` 同块，
而规则 (1) 已令 `a,b` 同块，故规则 (2) 对三元组**恒为冗余**。） -/
inductive AhoOK : Finset X → Finset (RootedTriplet X) → Prop where
  | small {S : Finset X} {R : Finset (RootedTriplet X)} (h : S.card ≤ 1) : AhoOK S R
  | step {S : Finset X} {R : Finset (RootedTriplet X)} (hS : 2 ≤ S.card)
      (hblk : 2 ≤ (tripletBlocks S R).card)
      (hrec : ∀ B ∈ tripletBlocks S R, AhoOK B R) : AhoOK S R

/-- **BUILD 递归构造的簇族**：块 + 块内递归簇。

（分支条件不成立时「就地停止」返回 `{S}`；在 `AhoOK` 成立的前提下分支条件总成立，
见 `ahoFamily_spec`。递归用 `Finset.strongInductionOn`，终止性由 `S.card` 严格下降给出。） -/
noncomputable def ahoFamily (R : Finset (RootedTriplet X)) (S : Finset X) :
    Finset (Finset X) :=
  Finset.strongInductionOn (p := fun _ => Finset (RootedTriplet X) → Finset (Finset X)) S
    (fun S ih => fun R' =>
      if h : 2 ≤ S.card ∧ 2 ≤ (tripletBlocks S R').card then
        insert S ((tripletBlocks S R').attach.biUnion fun B =>
          ih B.1 (tripletBlocks_ssubset_of_two_le_card h.2 B.2) R')
      else {S}) R

omit [Fintype X] in
/-- `ahoFamily` 的**展开方程**。 -/
theorem ahoFamily_eq (R : Finset (RootedTriplet X)) (S : Finset X) :
    ahoFamily R S =
      if _h : 2 ≤ S.card ∧ 2 ≤ (tripletBlocks S R).card then
        insert S ((tripletBlocks S R).attach.biUnion fun B => ahoFamily R B.1)
      else {S} := by
  rw [ahoFamily, Finset.strongInductionOn_eq]
  rfl

/-- `ahoFamily R S` 的**完整规格**。 -/
def AhoSpec (R : Finset (RootedTriplet X)) (S : Finset X) (F : Finset (Finset X)) : Prop :=
  LaminarFamily F ∧ S ∈ F ∧ (∀ C ∈ F, C ⊆ S) ∧ (∀ C ∈ F, C.Nonempty) ∧
    ∀ t ∈ R, t.leaves ⊆ S → ∃ C ∈ F, t.pair ⊆ C ∧ t.out ∉ C

omit [Fintype X] in
/-- ★★★ **`ahoFamily` 的规格**（对 `AhoOK` 的递归结构归纳）。 -/
theorem ahoFamily_spec (R : Finset (RootedTriplet X)) :
    ∀ S : Finset X, S.Nonempty → AhoOK S R → AhoSpec R S (ahoFamily R S) := by
  classical
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hSne hOK
    rw [ahoFamily_eq]
    cases hOK with
    | small hcard =>
      have hnot : ¬ (2 ≤ S.card ∧ 2 ≤ (tripletBlocks S R).card) := fun h => by omega
      rw [dite_eq_right hnot]
      refine ⟨?_, Finset.mem_singleton_self S, ?_, ?_, ?_⟩
      · intro A hA B hB
        rw [Finset.mem_singleton] at hA hB
        rw [hA, hB]
        exact Or.inl (Finset.Subset.refl S)
      · intro C hC
        rw [Finset.mem_singleton] at hC
        rw [hC]
      · intro C hC
        rw [Finset.mem_singleton] at hC
        rw [hC]
        exact hSne
      · intro t ht hsub
        exfalso
        have h3 : t.leaves.card = 3 := t.card_leaves
        have := Finset.card_le_card hsub
        omega
    | step hS hblk hrec =>
      have hcond : 2 ≤ S.card ∧ 2 ≤ (tripletBlocks S R).card := ⟨hS, hblk⟩
      rw [dite_eq_left hcond]
      set K := tripletBlocks S R with hK
      set U := K.attach.biUnion (fun B => ahoFamily R B.1) with hU
      have hmemK : ∀ {B : Finset X}, B ∈ tripletBlocks S R → B ∈ K := fun h => by
        rw [hK]; exact h
      have hmemU : ∀ C : Finset X, C ∈ U ↔ ∃ B : ↥K, C ∈ ahoFamily R B.1 := by
        intro C
        rw [hU, Finset.mem_biUnion]
        exact ⟨fun ⟨B, _, h⟩ => ⟨B, h⟩, fun ⟨B, h⟩ => ⟨B, Finset.mem_attach K B, h⟩⟩
      -- 每个块递归成功
      have hspecB : ∀ B : ↥K, AhoSpec R B.1 (ahoFamily R B.1) := fun B =>
        ih B.1 (tripletBlocks_ssubset_of_two_le_card hblk B.2) (tripletBlocks_nonempty S R B.2)
          (hrec B.1 B.2)
      have hBsub : ∀ B : ↥K, B.1 ⊆ S := fun B => tripletBlocks_subset S R B.2
      have hBdisj : ∀ B B' : ↥K, B ≠ B' → Disjoint B.1 B'.1 := fun B B' h =>
        tripletBlocks_disjoint B.2 B'.2 (fun hh => h (Subtype.ext hh))
      have hBlam : ∀ B : ↥K, LaminarFamily (ahoFamily R B.1) := fun B => (hspecB B).1
      have hBmem : ∀ B : ↥K, B.1 ∈ ahoFamily R B.1 := fun B => (hspecB B).2.1
      have hBsub' : ∀ B : ↥K, ∀ C ∈ ahoFamily R B.1, C ⊆ B.1 := fun B => (hspecB B).2.2.1
      have hBne' : ∀ B : ↥K, ∀ C ∈ ahoFamily R B.1, C.Nonempty := fun B => (hspecB B).2.2.2.1
      have hBdisp : ∀ B : ↥K, ∀ t ∈ R, t.leaves ⊆ B.1 →
          ∃ C ∈ ahoFamily R B.1, t.pair ⊆ C ∧ t.out ∉ C := fun B => (hspecB B).2.2.2.2
      have hUsub : ∀ C ∈ U, C ⊆ S := by
        intro C hC
        obtain ⟨B, hB⟩ := hmemU C |>.mp hC
        exact (hBsub' B C hB).trans (hBsub B)
      have hUne : ∀ C ∈ U, C.Nonempty := by
        intro C hC
        obtain ⟨B, hB⟩ := hmemU C |>.mp hC
        exact hBne' B C hB
      refine ⟨?_, Finset.mem_insert_self S U, ?_, ?_, ?_⟩
      · -- 镶嵌性
        intro A hA B hB
        rw [Finset.mem_insert] at hA hB
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · rw [hA, hB]
          exact Or.inl (Finset.Subset.refl S)
        · rw [hA]
          exact Or.inr (Or.inl (hUsub B hB))
        · rw [hB]
          exact Or.inl (hUsub A hA)
        · obtain ⟨B₁, hB₁⟩ := hmemU A |>.mp hA
          obtain ⟨B₂, hB₂⟩ := hmemU B |>.mp hB
          by_cases hEq : B₁ = B₂
          · rw [← hEq] at hB₂
            exact hBlam B₁ A hB₁ B hB₂
          · exact Or.inr (Or.inr ((hBdisj B₁ B₂ hEq).mono (hBsub' B₁ A hB₁)
              (hBsub' B₂ B hB₂)))
      · intro C hC
        rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · rw [hC]
        · exact hUsub C hC
      · intro C hC
        rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · rw [hC]
          exact hSne
        · exact hUne C hC
      · -- 展示性
        intro t ht htS
        obtain ⟨B, hBK, hpair⟩ := exists_block_of_pair ht htS
        have hBK' : B ∈ K := hmemK hBK
        by_cases hout : t.out ∈ B
        · have hsub : t.leaves ⊆ B := by
            rw [RootedTriplet.leaves]
            exact Finset.union_subset hpair (Finset.singleton_subset_iff.mpr hout)
          obtain ⟨C, hC, hpairC, houtC⟩ := hBdisp ⟨B, hBK'⟩ t ht hsub
          exact ⟨C, Finset.mem_insert_of_mem (hmemU C |>.mpr ⟨⟨B, hBK'⟩, hC⟩), hpairC, houtC⟩
        · refine ⟨B, Finset.mem_insert_of_mem ?_, hpair, hout⟩
          exact hmemU B |>.mpr ⟨⟨B, hBK'⟩, hBmem ⟨B, hBK'⟩⟩

/-! ## 4. ★★★ 主定理：Aho 相容 ⟹ 存在展示它的有根树 -/

/-- **远离根的一侧 = 团**：`toRootedTreeOfCard` 中，非 `univ` 簇 `B` 在 `T - e_B` 中
与根不可达（即 `B` 是**远离根**的一侧）。

由闭包不变式 `walk_mem_subtreeVerts` 得到：若根与 `inl B` 可达，
则根落在闭包 `{A : A ⊆ B} ∪ B` 里，即 `univ ⊆ B`，与 `B ≠ univ` 矛盾。 -/
theorem not_reachable_root_parentEdge {F : Finset (Finset X)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset X) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card)
    (h2 : 2 ≤ Fintype.card X)
    {B : Finset X} (hB : B ∈ F) (hBuniv : B ≠ Finset.univ) :
    ¬ ((toRootedTreeOfCard hl huniv hcard h2).graph.deleteEdges
        {parentEdge hl (nonempty_of_mem_of_hcard hcard h2) huniv B hB hBuniv}).Reachable
      (toRootedTreeOfCard hl huniv hcard h2).root (Sum.inl (⟨B, hB⟩ : ↥F)) := by
  classical
  intro hr
  have hwalk := walk_mem_subtreeVerts hl (nonempty_of_mem_of_hcard hcard h2) huniv hB hBuniv
    (u := (Sum.inl (⟨B, hB⟩ : ↥F))) (v := (Sum.inl (⟨Finset.univ, huniv⟩ : ↥F)))
    (SimpleGraph.Walk.reverse hr.some) (mem_subtreeVerts_inl.mpr (Finset.Subset.refl B))
  have hsub : Finset.univ ⊆ B := mem_subtreeVerts_inl.mp hwalk
  exact hBuniv (Finset.Subset.antisymm (Finset.subset_univ B) hsub)

/-- ★★★ **非 `univ` 簇是 `toRootedTreeOfCard` 的有根团**（且叶集恰为该簇）。

由 `leafSide_parentEdge_of_card`（边侧 = 簇）与 `not_reachable_root_parentEdge`
（该侧**远离根**）合成。 -/
theorem isRootedClade_toRootedTreeOfCard {F : Finset (Finset X)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset X) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card) (h2 : 2 ≤ Fintype.card X)
    {B : Finset X} (hB : B ∈ F) (hBuniv : B ≠ Finset.univ) :
    (toRootedTreeOfCard hl huniv hcard h2).IsRootedClade B := by
  classical
  have hne := nonempty_of_mem_of_hcard hcard h2
  refine ⟨Sum.inl (⟨B, hB⟩ : ↥F), Sum.inl (parentV hl hne huniv (⟨B, hB⟩ : ↥F) hBuniv),
    ?_, ?_, ?_⟩
  · exact (treeGraph_adj_inl_inl F (⟨B, hB⟩ : ↥F)
      (parentV hl hne huniv (⟨B, hB⟩ : ↥F) hBuniv)).mpr
      (Or.inl (isParentOf_parentOf (A := B) hl hne huniv hB hBuniv))
  · exact not_reachable_root_parentEdge hl huniv hcard h2 hB hBuniv
  · exact ((toRootedTreeOfCard_sideLeaves (F := F) hl huniv hcard h2
      (s(Sum.inl (⟨B, hB⟩ : ↥F), Sum.inl (parentV hl hne huniv (⟨B, hB⟩ : ↥F) hBuniv)))
      (Sum.inl (⟨B, hB⟩ : ↥F))).trans
      (leafSide_parentEdge_of_card hl huniv hcard h2 hB hBuniv)).symm

/-- ★★★ **镶嵌簇族 + 展示条件 ⟹ 有根树展示全部三元组**。

这是主定理的引擎：`toRootedTreeOfCard` 建树，`isRootedClade_toRootedTreeOfCard`
说明族成员是**远离根**的团，再用 `displaysTriplet_of_isRootedClade` 收尾。 -/
theorem exists_rootedTree_of_laminar (h2 : 2 ≤ Fintype.card X) {F : Finset (Finset X)}
    (hl : LaminarFamily F) (huniv : (Finset.univ : Finset X) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card) (R : Finset (RootedTriplet X))
    (hdisp : ∀ t ∈ R, ∃ C ∈ F, t.pair ⊆ C ∧ t.out ∉ C) :
    ∃ T : RootedTree.{u, u} X, ∀ t ∈ R, T.DisplaysTriplet t := by
  classical
  refine ⟨toRootedTreeOfCard hl huniv hcard h2, fun t ht => ?_⟩
  obtain ⟨C, hC, hpair, hout⟩ := hdisp t ht
  have hCuniv : C ≠ Finset.univ := fun hh => hout (hh ▸ Finset.mem_univ t.out)
  exact RootedTree.displaysTriplet_of_isRootedClade
    (T := toRootedTreeOfCard hl huniv hcard h2)
    (isRootedClade_toRootedTreeOfCard hl huniv hcard h2 hC hCuniv) hpair hout

/-- ★★★ **Aho 的有根一致性定理**（BUILD）：相容的有根三元组集必被某棵有根树展示。

* `h2 : 2 ≤ |X|`；
* `h : AhoOK X R` 是 Aho et al. 1981 BUILD 的递归判据（本文件 §3）。

⇒ 存在有根树 `T`（叶集 `X`），使 `R` 的每个三元组都被 `T` 展示。 -/
theorem exists_rootedTree_of_ahoOK (h2 : 2 ≤ Fintype.card X)
    (R : Finset (RootedTriplet X)) (h : AhoOK (Finset.univ : Finset X) R) :
    ∃ T : RootedTree.{u, u} X, ∀ t ∈ R, T.DisplaysTriplet t := by
  classical
  have hune : (Finset.univ : Finset X).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  obtain ⟨hl, -, -, -, hdisp⟩ := ahoFamily_spec R Finset.univ hune h
  refine exists_rootedTree_of_laminar h2 (laminarFamily_normFinset hl) univ_mem_normFinset
    (fun B hB => (mem_normFinset.mp hB).imp id (fun hh => hh.2)) R (fun t ht => ?_)
  obtain ⟨C, hC, hpair, hout⟩ := hdisp t ht (Finset.subset_univ _)
  have hCcard : 2 ≤ C.card := by
    have := Finset.card_le_card hpair
    rw [t.card_pair] at this
    exact this
  exact ⟨C, mem_normFinset.mpr (Or.inr ⟨hC, hCcard⟩), hpair, hout⟩

/-! ## 5. 有根团的**镶嵌性**（laminarity）—— ★B 反例的地基

**文献**

* Bryant & Steel 1995（`references/md/BryantSteel1995_ExtensionOperationsLeafLabelledTrees.md`）：
  * 有根三元组 `ab|c` 的定义：**227–229 行**（“The rooted triple with a pair of leaves
    `{a, b}` connected to the third leaf `c` via the root is denoted `ablc`”）；
  * 边标号图 `[R,S]`：**743–747 行**；
  * **Theorem 2**：`R` 相容 **⟺** 每个 `|S| ≥ 3` 的 `S` 上 `[R,S]` **不连通**（**766–769 行**）；
    其 (⟹) 的证明（**777–785 行**）用「`T|s` 的最大元素 `M` 的直接后代**划分** `S`，
    跨块之间没有 `[R,S]` 的边」—— 这正是本节的**镶嵌性**（`[R,S]` 的块 = 远离根的团）；
  * ONETREE（本库 `AhoOK` 的原型）：**365–388 行**；
    “The algorithm returns a tree if and only if the input set of rooted triples is
    consistent”：**759–760 行**。
* Aho, Sagiv, Szymanski & Ullman 1981：划分 `π_C` 的三条规则：**375–380 行**；
  **Theorem 1**（BUILD 返回非空 ⟹ 满足全部约束）：**400–402 行**。

**为什么需要本节**：`Phylo/Split.lean` 的 `sidesCompatible_sideLeaves` 只给出 split 层的
相容性 `SidesCompatible A B = A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ`，
**第四个析取项 `A ∪ B = univ` 是真的会发生**（例：根的两个孩子各带两支的 `A = {a,b}`、
`B = {c,d}`），因此 split 层的相容性**推不出**镶嵌性。
加上「**远离根**」（`¬ inSide e u root`）这一条件后才有镶嵌性 —— 本节证明之。 -/

open SimpleGraph

namespace RootedTree

omit [Fintype X] [DecidableEq X] in
/-- `v` 与 `u` 在删去边 `e` 后**同侧**（`Phylo.Split` 的 `Cladogram.inSide` 的 `RootedTree` 版）。 -/
def inSide (T : RootedTree X) (e : Sym2 T.V) (u v : T.V) : Prop :=
  (T.graph.deleteEdges {e}).Reachable u v

omit [DecidableEq X] in
/-- 边 `e` 的 `u` **侧顶点集**：`T - e` 中含 `u` 的连通分量（`Cladogram.sideVertices` 的对应物）。 -/
noncomputable def cladeVertices (T : RootedTree X) (e : Sym2 T.V) (u : T.V) : Finset T.V := by
  classical
  exact Finset.univ.filter fun w => T.inSide e u w

omit [Fintype X] [DecidableEq X] in
theorem mem_cladeVertices (T : RootedTree X) {e : Sym2 T.V} {u w : T.V} :
    w ∈ T.cladeVertices e u ↔ T.inSide e u w := by
  classical
  simp [cladeVertices]

omit [Fintype X] [DecidableEq X] in
theorem self_mem_cladeVertices (T : RootedTree X) (e : Sym2 T.V) (u : T.V) :
    u ∈ T.cladeVertices e u := by
  classical
  rw [mem_cladeVertices]
  exact Reachable.refl u

omit [DecidableEq X] in
/-- `sideLeaves` 与 `inSide` 的一致性（`Cladogram.mem_sideLeaves_iff_inSide` 的对应物）。 -/
theorem mem_sideLeaves_iff_inSide (T : RootedTree X) {e : Sym2 T.V} {u : T.V} {x : X} :
    x ∈ T.sideLeaves e u ↔ T.inSide e u (T.leaf x) := by
  classical
  rw [RootedTree.sideLeaves]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inSide]
  exact reachable_comm

omit [Fintype X] [DecidableEq X] in
theorem inSide_self (T : RootedTree X) (e : Sym2 T.V) (u : T.V) : T.inSide e u u :=
  Reachable.refl u

omit [Fintype X] [DecidableEq X] in
theorem inSide_comm (T : RootedTree X) (e : Sym2 T.V) (u v : T.V) :
    T.inSide e u v ↔ T.inSide e v u := reachable_comm

omit [Fintype X] [DecidableEq X] in
theorem inSide_trans (T : RootedTree X) (e : Sym2 T.V) {u v w : T.V}
    (huv : T.inSide e u v) (hvw : T.inSide e v w) : T.inSide e u w := huv.trans hvw

omit [Fintype X] [DecidableEq X] in
/-- **树中每条边都是桥**（`Cladogram.not_reachable_deleteEdges_of_adj` 的对应物）。 -/
theorem not_reachable_deleteEdges_of_adj (T : RootedTree X) {u v : T.V}
    (h : T.graph.Adj u v) : ¬ (T.graph.deleteEdges {s(u, v)}).Reachable u v :=
  isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) h)

omit [Fintype X] [DecidableEq X] in
/-- **跨越一个侧分量的边只有它本身**。 -/
theorem eq_edge_of_adj_of_mem_cladeVertices_of_notMem (T : RootedTree X) {e : Sym2 T.V}
    {u w z : T.V} (hadj : T.graph.Adj w z) (hw : w ∈ T.cladeVertices e u)
    (hz : z ∉ T.cladeVertices e u) : s(w, z) = e := by
  classical
  by_contra hne
  refine hz ?_
  rw [mem_cladeVertices] at hw ⊢
  have hadj' : (T.graph.deleteEdges {e}).Adj w z := deleteEdges_adj.mpr ⟨hadj, hne⟩
  exact hw.trans hadj'.reachable

omit [Fintype X] [DecidableEq X] in
/-- **相邻两点在删边后同侧**（除非该边就是被删的边）。 -/
theorem inSide_congr_of_adj (T : RootedTree X) {e₁ : Sym2 T.V} {u₁ c d : T.V}
    (hcd : T.graph.Adj c d) (hne : s(c, d) ≠ e₁) :
    T.inSide e₁ u₁ c ↔ T.inSide e₁ u₁ d := by
  constructor
  · intro hc
    by_contra hd
    exact hne (T.eq_edge_of_adj_of_mem_cladeVertices_of_notMem hcd
      ((mem_cladeVertices (T := T)).mpr hc) (fun h => hd ((mem_cladeVertices (T := T)).mp h)))
  · intro hd
    by_contra hc
    have h := T.eq_edge_of_adj_of_mem_cladeVertices_of_notMem hcd.symm
      ((mem_cladeVertices (T := T)).mpr hd) (fun h => hc ((mem_cladeVertices (T := T)).mp h))
    rw [Sym2.eq_swap] at h
    exact hne h

omit [Fintype X] [DecidableEq X] in
/-- **旁侧连通性**：若 `p,q` 在 `e₁` 同侧，且该侧不含 `e₂ = ⟦c,d⟧` 的端点，
则在 `T - e₂` 中 `p,q` 仍可达（`Cladogram.inSide_deleteEdges_of_inSide` 的对应物）。 -/
theorem inSide_deleteEdges_of_inSide (T : RootedTree X)
    {e₁ e₂ : Sym2 T.V} {c d p q : T.V} (he₂ : e₂ = s(c, d))
    (hside : T.inSide e₁ p q) (hc : ¬ T.inSide e₁ p c) (hd : ¬ T.inSide e₁ p d) :
    T.inSide e₂ p q := by
  obtain ⟨p'⟩ := hside
  refine reachable_deleteEdges_of_support_notMem (p'.mapLe (deleteEdges_le {e₁})) ?_
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro w hw
  have hwX : T.inSide e₁ p w := reachable_of_mem_support p' hw
  rw [he₂, Sym2.mem_iff]
  rintro (rfl | rfl)
  · exact hc hwX
  · exact hd hwX

omit [Fintype X] [DecidableEq X] in
/-- **删边后每点与端点之一同侧**（`Cladogram.inSide_or_inSide` 的对应物）。 -/
theorem inSide_or_inSide (T : RootedTree X) {a b x : T.V} (hab : T.graph.Adj a b) :
    T.inSide s(a, b) x a ∨ T.inSide s(a, b) x b := by
  obtain ⟨p⟩ := T.isTree.connected x a
  refine SimpleGraph.Walk.recOn (motive := fun u v _ =>
    v = a → T.inSide s(a, b) u a ∨ T.inSide s(a, b) u b) p ?_ ?_ rfl
  · intro u hu
    subst hu
    exact Or.inl (Reachable.refl _)
  · intro u v w hadj q ih hw
    by_cases h : s(u, v) = s(a, b)
    · rcases Sym2.eq_iff.mp h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj' : (T.graph.deleteEdges {s(a, b)}).Adj u v :=
        deleteEdges_adj.mpr ⟨hadj, by simpa using h⟩
      rcases ih hw with ih | ih
      · exact Or.inl (hadj'.reachable.trans ih)
      · exact Or.inr (hadj'.reachable.trans ih)

omit [Fintype X] [DecidableEq X] in
/-- **`e` 的两端点分居两侧**。 -/
theorem not_inSide_both (T : RootedTree X) {a b y : T.V} (hab : T.graph.Adj a b) :
    ¬ (T.inSide s(a, b) a y ∧ T.inSide s(a, b) b y) := by
  rintro ⟨h1, h2⟩
  exact T.not_reachable_deleteEdges_of_adj hab (h1.trans h2.symm)

omit [DecidableEq X] in
/-- **同侧基准可换**。 -/
theorem sideLeaves_eq_of_inSide (T : RootedTree X) {e : Sym2 T.V} {u a : T.V}
    (h : T.inSide e u a) : T.sideLeaves e u = T.sideLeaves e a := by
  classical
  ext x
  rw [mem_sideLeaves_iff_inSide, mem_sideLeaves_iff_inSide]
  exact ⟨fun hu => h.symm.trans hu, fun ha => h.trans ha⟩

/-- **情形 1**：若 `e₂` 的端点 `c,d` 都在 `e₁` 的 `u₁` 侧**之外**，且两侧有公共叶，
则 `u₁` 侧叶集整个含于 `u₂` 侧叶集。

（这是 `Cladogram.sidesCompatible_sideLeaves_of_not_inSide` 对应证明的「存在公共点」分支，
在那里被 split 层的四析取形式掩盖；这里提炼成**子集**结论。） -/
theorem sideLeaves_subset_of_not_inSide (T : RootedTree X) {e₁ e₂ : Sym2 T.V}
    {u₁ u₂ c d : T.V} (he₂ : e₂ = s(c, d)) (hc : ¬ T.inSide e₁ u₁ c)
    (hd : ¬ T.inSide e₁ u₁ d)
    (hne : (T.sideLeaves e₁ u₁ ∩ T.sideLeaves e₂ u₂).Nonempty) :
    T.sideLeaves e₁ u₁ ⊆ T.sideLeaves e₂ u₂ := by
  classical
  obtain ⟨y, hy⟩ := hne
  rw [Finset.mem_inter, mem_sideLeaves_iff_inSide, mem_sideLeaves_iff_inSide] at hy
  intro x hx
  rw [mem_sideLeaves_iff_inSide] at hx ⊢
  have hc' : ¬ T.inSide e₁ (T.leaf x) c := fun h => hc (hx.trans h)
  have hd' : ¬ T.inSide e₁ (T.leaf x) d := fun h => hd (hx.trans h)
  have hside : T.inSide e₁ (T.leaf x) (T.leaf y) := hx.symm.trans hy.1
  exact hy.2.trans ((T.inSide_deleteEdges_of_inSide he₂ hside hc' hd').symm)

/-- ★★ **有根团的镶嵌性**（`RootedTree` 版）：设 `⟦a,b⟧`、`⟦c,d⟧` 是树的两条边，
`u₁`（resp. `u₂`）位于 `⟦a,b⟧`（resp. `⟦c,d⟧`）**远离根**的一侧，则两侧叶集要么**嵌套**、
要么**相离**；若两侧有公共叶，则必为**嵌套**。

⚠️ 「远离根」是**实质条件**：没有它，`A = {a,b}` 与 `B = {c,d}`（根的两个孩子的两支）
给出 `A ∪ B = univ` 且 `A ∩ B = ∅`，`A = {a,b}` 与 `B = {b,c}` 给出既非嵌套又非相离。 -/
theorem sideLeaves_nested_of_adj (T : RootedTree X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {u₁ u₂ : T.V}
    (h₁ : ¬ T.inSide s(a, b) u₁ T.root) (h₂ : ¬ T.inSide s(c, d) u₂ T.root)
    (hne : (T.sideLeaves s(a, b) u₁ ∩ T.sideLeaves s(c, d) u₂).Nonempty) :
    T.sideLeaves s(a, b) u₁ ⊆ T.sideLeaves s(c, d) u₂ ∨
      T.sideLeaves s(c, d) u₂ ⊆ T.sideLeaves s(a, b) u₁ := by
  classical
  by_cases heq : s(c, d) = s(a, b)
  · -- 同一条边：`u₁`、`u₂` 都在远离根的那一侧，故同侧
    rw [heq] at h₂
    have h12 : T.inSide s(a, b) u₁ u₂ := by
      rcases T.inSide_or_inSide hab (x := u₁) with h1 | h1 <;>
        rcases T.inSide_or_inSide hab (x := u₂) with h2 | h2
      · exact h1.trans h2.symm
      · rcases T.inSide_or_inSide hab (x := T.root) with hr | hr
        · exact absurd (h1.trans hr.symm) h₁
        · exact absurd (h2.trans hr.symm) h₂
      · rcases T.inSide_or_inSide hab (x := T.root) with hr | hr
        · exact absurd (h2.trans hr.symm) h₂
        · exact absurd (h1.trans hr.symm) h₁
      · exact h1.trans h2.symm
    exact Or.inl (by rw [heq, T.sideLeaves_eq_of_inSide h12])
  · by_cases hc : T.inSide s(a, b) u₁ c
    · -- `c,d` 都在 `u₁` 侧 ⟹ `u₂` 侧含于 `u₁` 侧
      have hd : T.inSide s(a, b) u₁ d := (T.inSide_congr_of_adj hcd heq).mp hc
      have hcR : ¬ T.inSide s(a, b) T.root c := fun h => h₁ (hc.trans h.symm)
      have hdR : ¬ T.inSide s(a, b) T.root d := fun h => h₁ (hd.trans h.symm)
      have hdisj : ∀ w, T.inSide s(a, b) T.root w → ¬ T.inSide s(c, d) u₂ w := by
        intro w hw hwB
        have hgo : T.inSide s(c, d) T.root w :=
          T.inSide_deleteEdges_of_inSide (e₁ := s(a, b)) (e₂ := s(c, d))
            (c := c) (d := d) rfl hw hcR hdR
        exact h₂ (hwB.trans hgo.symm)
      refine Or.inr fun y hy => ?_
      rw [mem_sideLeaves_iff_inSide] at hy ⊢
      rcases T.inSide_or_inSide hab (x := u₁) with h1 | h1 <;>
        rcases T.inSide_or_inSide hab (x := T.leaf y) with h2 | h2
      · exact h1.trans h2.symm
      · rcases T.inSide_or_inSide hab (x := T.root) with hr | hr
        · exact absurd (h1.trans hr.symm) h₁
        · exact absurd hy (hdisj (T.leaf y) (hr.trans h2.symm))
      · rcases T.inSide_or_inSide hab (x := T.root) with hr | hr
        · exact absurd hy (hdisj (T.leaf y) (hr.trans h2.symm))
        · exact absurd (h1.trans hr.symm) h₁
      · exact h1.trans h2.symm
    · -- `c,d` 都在 `u₁` 侧之外：情形 1
      exact Or.inl (T.sideLeaves_subset_of_not_inSide (e₁ := s(a, b)) (e₂ := s(c, d))
        (u₁ := u₁) (u₂ := u₂) rfl hc ((T.inSide_congr_of_adj hcd heq).not.mp hc) hne)

/-- ★★ **有根团镶嵌**（`IsRootedClade` 版）：同一棵有根树的两个**有根团**若相交则必嵌套。
（这是 `Cladogram` 层没有的一般事实 —— 有根树的团族是**镶嵌族** `LaminarFamily`。） -/
theorem isRootedClade_laminar (T : RootedTree X) {C D : Finset X}
    (hC : T.IsRootedClade C) (hD : T.IsRootedClade D) (hne : (C ∩ D).Nonempty) :
    C ⊆ D ∨ D ⊆ C := by
  obtain ⟨p₁, q₁, hpq₁, hr₁, rfl⟩ := hC
  obtain ⟨p₂, q₂, hpq₂, hr₂, rfl⟩ := hD
  exact T.sideLeaves_nested_of_adj hpq₁ hpq₂
    (fun h => hr₁ ((T.inSide_comm (s(p₁, q₁)) p₁ T.root).mp h))
    (fun h => hr₂ ((T.inSide_comm (s(p₂, q₂)) p₂ T.root).mp h)) hne

end RootedTree

/-! ## 6. 相容性（语义）· ★B 反例 · 有根 Aho 的正确判据

**任务书原文要求的「两两相容 ⟺ 存在树」在有根三元组上是`假`的** —— 本节给出**具体反例**。

* **★B 反例检查（先造反例）**：`{ab|c, ac|b, bc|a}` 呢？ —— `ab|c` 与 `ac|b` **不相容**
  （`not_compatible_mk'_conflict`），故它**不是**两两相容。这确认 `Compatible` 的定义
  **不过弱**：若这里能证出「相容」，定义就是错的。
* **真反例（4 叶）**：`{ab|c, ac|d, ad|b}` —— 三个近对 `{a,b},{a,c},{a,d}` **两两只交于 `a`**，
  故两两相容（`compatible_mk'_chain` + `((a,b),c)d` 形的显式树）；但**没有**任何有根树同时
  展示三者（`not_displayedByTree_fourLeafCounterexample`）——
  三个展示团都含 `a`，由 `isRootedClade_laminar` 两两嵌套，取最大者即矛盾。
  这也正是 Bryant–Steel 1995 **Theorem 2**（766–769 行）在 `S = {a,b,c,d}` 上的
  `[R,S]` **连通**反例（边 `{a,b}, {a,c}, {a,d}` 构成星形）。
* **正确的判据**是 Aho 的**递归** `AhoOK`（§3）：`exists_rootedTree_of_ahoOK`（§4）已证
  「`AhoOK` ⟹ 存在展示树」；反方向仍是显式缺口（见本节末）。 -/

namespace RootedTriplet

omit [Fintype X] in
/-- **两个有根三元组相容**（语义定义）：存在一棵有根树同时展示两者。 -/
def Compatible (t t' : RootedTriplet X) : Prop :=
  ∃ T : RootedTree.{u, u} X, T.DisplaysTriplet t ∧ T.DisplaysTriplet t'

omit [Fintype X] in
/-- 三元组族**两两相容**。 -/
def PairwiseCompatible (R : Finset (RootedTriplet X)) : Prop :=
  ∀ t ∈ R, ∀ t' ∈ R, Compatible t t'

omit [Fintype X] in
/-- 三元组族**被某一棵有根树展示**（「整体相容」的语义版）。 -/
def DisplayedByTree (R : Finset (RootedTriplet X)) : Prop :=
  ∃ T : RootedTree.{u, u} X, ∀ t ∈ R, T.DisplaysTriplet t

omit [DecidableEq X] in
theorem compatible_comm {t t' : RootedTriplet X} (h : Compatible t t') : Compatible t' t := by
  obtain ⟨T, h1, h2⟩ := h
  exact ⟨T, h2, h1⟩

omit [DecidableEq X] in
/-- ★ **「展示 ⟹ 两两相容」**（Aho 有根版的两个方向里容易的那个；**不是**重言式：
它断言同一个 `T` 同时见证 `R` 的任意两元，而 `DisplayedByTree` 的存在量词在合取之前）。 -/
theorem pairwiseCompatible_of_displaysByTree {R : Finset (RootedTriplet X)}
    (h : DisplayedByTree R) : PairwiseCompatible R := by
  intro t ht t' ht'
  obtain ⟨T, hT⟩ := h
  exact ⟨T, hT t ht, hT t' ht'⟩

/-- **存在性引擎的具体形态**：任意单个三元组都被某棵有根树展示（`|X| ≥ 2`）。
（用镶嵌族 `{univ, t.pair}` 走 `exists_rootedTree_of_laminar`。） -/
theorem exists_rootedTree_displays_of_singleton (h2 : 2 ≤ Fintype.card X)
    (t : RootedTriplet X) : ∃ T : RootedTree.{u, u} X, T.DisplaysTriplet t := by
  classical
  set F : Finset (Finset X) := ({Finset.univ, t.pair} : Finset (Finset X)) with hF
  have huniv : (Finset.univ : Finset X) ∈ F := by
    rw [hF]; exact Finset.mem_insert_self _ _
  have hl : LaminarFamily F := by
    intro A hA B hB
    rw [hF] at hA hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact Or.inl (Finset.Subset.refl _)
    · exact Or.inr (Or.inl (Finset.subset_univ _))
    · exact Or.inl (Finset.subset_univ _)
    · exact Or.inl (Finset.Subset.refl _)
  have hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rw [hF] at hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [RootedTriplet.card_pair])
  have hdisp : ∀ t' ∈ ({t} : Finset (RootedTriplet X)),
      ∃ C ∈ F, t'.pair ⊆ C ∧ t'.out ∉ C := by
    intro t' ht'
    rw [Finset.mem_singleton] at ht'
    exact ⟨t'.pair, by rw [hF, ht']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      Finset.Subset.refl _, t'.out_notMem⟩
  obtain ⟨T, hT⟩ := exists_rootedTree_of_laminar (h2 := h2) hl huniv hcard
    ({t} : Finset (RootedTriplet X)) hdisp
  exact ⟨T, hT t (Finset.mem_singleton_self t)⟩

theorem compatible_self (h2 : 2 ≤ Fintype.card X) (t : RootedTriplet X) : Compatible t t := by
  obtain ⟨T, hT⟩ := exists_rootedTree_displays_of_singleton h2 t
  exact ⟨T, hT, hT⟩

/-- ★ **相容的充分条件**（构造性）：`xy|z` 与 `xz|w`（`x,y,z,w` 两两不同）被树
`(((x,y),z),w)` 同时展示（团 `{x,y}` 与 `{x,y,z}`）。 -/
theorem compatible_mk'_chain {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w) (h2 : 2 ≤ Fintype.card X) :
    Compatible (mk' x y z hxy hxz hyz) (mk' x z w hxz hxw hzw) := by
  classical
  set F : Finset (Finset X) :=
    ({Finset.univ, ({x, y} : Finset X), ({x, y, z} : Finset X)} : Finset (Finset X)) with hF
  have hcard2 : ({x, y} : Finset X).card = 2 := Finset.card_pair_eq_two_iff.mpr hxy
  have hcard3 : ({x, y, z} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hPQ : ({x, y} : Finset X) ⊆ ({x, y, z} : Finset X) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    tauto
  have hl : LaminarFamily F := by
    intro A hA B hB
    rw [hF] at hA hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl
    · exact Or.inl (Finset.Subset.refl _)
    · exact Or.inr (Or.inl (Finset.subset_univ _))
    · exact Or.inr (Or.inl (Finset.subset_univ _))
    · exact Or.inl (Finset.subset_univ _)
    · exact Or.inl (Finset.Subset.refl _)
    · exact Or.inl hPQ
    · exact Or.inl (Finset.subset_univ _)
    · exact Or.inr (Or.inl hPQ)
    · exact Or.inl (Finset.Subset.refl _)
  have hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rw [hF] at hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [hcard2])
    · exact Or.inr (by rw [hcard3]; omega)
  have hdisp : ∀ t' ∈ ({mk' x y z hxy hxz hyz, mk' x z w hxz hxw hzw}
      : Finset (RootedTriplet X)), ∃ C ∈ F, t'.pair ⊆ C ∧ t'.out ∉ C := by
    intro t' ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl
    · refine ⟨({x, y} : Finset X), ?_, Finset.Subset.refl _, ?_⟩
      · rw [hF]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [RootedTriplet.out_mk']
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hxz h.symm, fun h => hyz h.symm⟩
    · refine ⟨({x, y, z} : Finset X), ?_, ?_, ?_⟩
      · rw [hF]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · intro a ha
        simp only [RootedTriplet.pair_mk', Finset.mem_insert, Finset.mem_singleton] at ha ⊢
        tauto
      · rw [RootedTriplet.out_mk']
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hxw h.symm, fun h => hyw h.symm, fun h => hzw h.symm⟩
  obtain ⟨T, hT⟩ := exists_rootedTree_of_laminar (h2 := h2) hl
    (by rw [hF]; exact Finset.mem_insert_self _ _) hcard
    ({mk' x y z hxy hxz hyz, mk' x z w hxz hxw hzw} : Finset (RootedTriplet X)) hdisp
  exact ⟨T, hT _ (Finset.mem_insert_self _ _),
    hT _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

/-- ★B —— **反例检查 1**：`ab|c` 与 `ac|b`（同一三叶集、不同拓扑）**不相容**。
若这里能证出「相容」，就说明 `Compatible` 的定义被写**弱**了、必须修定义。 -/
theorem not_compatible_mk'_conflict {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Compatible (mk' a b c hab hac hbc) (mk' a c b hac hab (fun h => hbc h.symm)) := by
  rintro ⟨T, h1, h2⟩
  obtain ⟨C₁, hC₁, hp₁, ho₁⟩ := (T.displaysTriplet_iff_isRootedClade _).mp h1
  obtain ⟨C₂, hC₂, hp₂, ho₂⟩ := (T.displaysTriplet_iff_isRootedClade _).mp h2
  have ha₁ : a ∈ C₁ := hp₁ (by simp)
  have ha₂ : a ∈ C₂ := hp₂ (by simp)
  have hb₁ : b ∈ C₁ := hp₁ (by simp)
  have hc₂ : c ∈ C₂ := hp₂ (by simp)
  rcases T.isRootedClade_laminar hC₁ hC₂ ⟨a, Finset.mem_inter.mpr ⟨ha₁, ha₂⟩⟩ with hsub | hsub
  · exact ho₂ (hsub hb₁)
  · exact ho₁ (hsub hc₂)

/-- ★B —— **反例检查 2**（派单原问「`ab|c`, `ac|b`, `bc|a` 两两相容吗？」）：
**不**两两相容 —— `ab|c` 与 `ac|b` 已经冲突。这是「相容定义不过弱」的直接证据。 -/
theorem not_pairwiseCompatible_threeConflicting {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ PairwiseCompatible
      ({mk' a b c hab hac hbc, mk' a c b hac hab (fun h => hbc h.symm),
        mk' b c a hbc (fun h => hab h.symm) (fun h => hac h.symm)}
        : Finset (RootedTriplet X)) := by
  intro h
  exact not_compatible_mk'_conflict hab hac hbc
    (h _ (Finset.mem_insert_self _ _) _
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))

/-! ### 6.1 ★★★ 真反例：`{ab|c, ac|d, ad|b}`（`a=0, b=1, c=2, d=3`） -/

/-- `ab|c`（`a=0, b=1, c=2`）。 -/
abbrev ex_ab_c : RootedTriplet (Fin 4) := mk' 0 1 2 (by decide) (by decide) (by decide)

/-- `ac|d`（`a=0, c=2, d=3`）。 -/
abbrev ex_ac_d : RootedTriplet (Fin 4) := mk' 0 2 3 (by decide) (by decide) (by decide)

/-- `ad|b`（`a=0, d=3, b=1`）。 -/
abbrev ex_ad_b : RootedTriplet (Fin 4) := mk' 0 3 1 (by decide) (by decide) (by decide)

/-- ★★ **反例族** `{ab|c, ac|d, ad|b}`（三个近对两两只交于 `a`）。 -/
def fourLeafCounterexample : Finset (RootedTriplet (Fin 4)) := {ex_ab_c, ex_ac_d, ex_ad_b}

/-- ★★ **反例族两两相容**（每一对都由 `compatible_mk'_chain` 给出的显式树见证）。 -/
theorem pairwiseCompatible_fourLeafCounterexample :
    PairwiseCompatible fourLeafCounterexample := by
  intro t ht t' ht'
  simp only [fourLeafCounterexample, Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl
  · exact compatible_self (by decide) _
  · exact compatible_mk'_chain (x := 0) (y := 1) (z := 2) (w := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact compatible_comm (compatible_mk'_chain (x := 0) (y := 3) (z := 1) (w := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact compatible_comm (compatible_mk'_chain (x := 0) (y := 1) (z := 2) (w := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact compatible_self (by decide) _
  · exact compatible_mk'_chain (x := 0) (y := 2) (z := 3) (w := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact compatible_mk'_chain (x := 0) (y := 3) (z := 1) (w := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact compatible_comm (compatible_mk'_chain (x := 0) (y := 2) (z := 3) (w := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact compatible_self (by decide) _

/-- ★★★ **反例族没有共同展示树**。

证明：三个展示团 `C₁ ∋ 0,1`、`C₂ ∋ 0,2`、`C₃ ∋ 0,3` 都含叶 `0`，由
`isRootedClade_laminar` 两两嵌套；分情形取「最大者」，分别用
`2 ∉ C₁`、`3 ∉ C₂`、`1 ∉ C₃` 导出矛盾。 -/
theorem not_displayedByTree_fourLeafCounterexample :
    ¬ DisplayedByTree fourLeafCounterexample := by
  rintro ⟨T, hT⟩
  have h1 : T.DisplaysTriplet ex_ab_c := hT ex_ab_c (Finset.mem_insert_self _ _)
  have h2 : T.DisplaysTriplet ex_ac_d :=
    hT ex_ac_d (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h3 : T.DisplaysTriplet ex_ad_b :=
    hT ex_ad_b (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)))
  obtain ⟨C₁, hC₁, hp₁, ho₁⟩ := (T.displaysTriplet_iff_isRootedClade _).mp h1
  obtain ⟨C₂, hC₂, hp₂, ho₂⟩ := (T.displaysTriplet_iff_isRootedClade _).mp h2
  obtain ⟨C₃, hC₃, hp₃, ho₃⟩ := (T.displaysTriplet_iff_isRootedClade _).mp h3
  have h0₁ : (0 : Fin 4) ∈ C₁ := hp₁ (by decide)
  have h1₁ : (1 : Fin 4) ∈ C₁ := hp₁ (by decide)
  have hc₁ : (2 : Fin 4) ∉ C₁ := ho₁
  have h0₂ : (0 : Fin 4) ∈ C₂ := hp₂ (by decide)
  have h2₂ : (2 : Fin 4) ∈ C₂ := hp₂ (by decide)
  have hc₂ : (3 : Fin 4) ∉ C₂ := ho₂
  have h0₃ : (0 : Fin 4) ∈ C₃ := hp₃ (by decide)
  have h3₃ : (3 : Fin 4) ∈ C₃ := hp₃ (by decide)
  have hc₃ : (1 : Fin 4) ∉ C₃ := ho₃
  have h12 := T.isRootedClade_laminar hC₁ hC₂ ⟨0, Finset.mem_inter.mpr ⟨h0₁, h0₂⟩⟩
  have h23 := T.isRootedClade_laminar hC₂ hC₃ ⟨0, Finset.mem_inter.mpr ⟨h0₂, h0₃⟩⟩
  by_cases hAB : C₁ ⊆ C₂
  · by_cases hBC : C₂ ⊆ C₃
    · exact hc₃ (hBC (hAB h1₁))
    · exact hc₂ ((h23.resolve_left hBC) h3₃)
  · exact hc₁ ((h12.resolve_left hAB) h2₂)

/-- ★★★ **「两两相容 ⟹ 存在展示树」在有根三元组上为假**（与无根 split 的
`Phylo.Aho.compatible_exists_rootedTree` 形成鲜明对比：无根 split 层成立，有根三元组层不成立）。 -/
theorem pairwiseCompatible_not_sufficient :
    ∃ R : Finset (RootedTriplet (Fin 4)), PairwiseCompatible R ∧ ¬ DisplayedByTree R :=
  ⟨fourLeafCounterexample, pairwiseCompatible_fourLeafCounterexample,
    not_displayedByTree_fourLeafCounterexample⟩

/-- **被证伪的「两两相容版有根 Aho」陈述**（派单建议名 `rootedTriplets_compatible_iff_displayed`
的「⟸」方向在两两相容口径下的形式）；`…_false` 证明它**不成立**。 -/
def rootedTriplets_pairwiseCompatible_implies_displayed : Prop :=
  ∀ R : Finset (RootedTriplet (Fin 4)), PairwiseCompatible R → DisplayedByTree R

theorem rootedTriplets_pairwiseCompatible_implies_displayed_false :
    ¬ rootedTriplets_pairwiseCompatible_implies_displayed := by
  intro h
  obtain ⟨R, hpc, hnd⟩ := pairwiseCompatible_not_sufficient
  exact hnd (h R hpc)

/-! ### 6.2 反空真（`example`） -/

/-- 反空真 A：`Compatible` 有真居民（`Fin 4` 的 `01|2` 与 `02|3`，树 `(((0,1),2),3)`）。 -/
example : Compatible ex_ab_c ex_ac_d :=
  compatible_mk'_chain (x := 0) (y := 1) (z := 2) (w := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 反空真 B：`{ab|c, ac|b, bc|a}`（`Fin 3`）**不**两两相容（★B 检查的具体实例）。 -/
example : ¬ PairwiseCompatible
    ({mk' (0 : Fin 3) 1 2 (by decide) (by decide) (by decide),
      mk' (0 : Fin 3) 2 1 (by decide) (by decide) (by decide),
      mk' (1 : Fin 3) 2 0 (by decide) (by decide) (by decide)}
        : Finset (RootedTriplet (Fin 3))) :=
  not_pairwiseCompatible_threeConflicting (by decide) (by decide) (by decide)

/-- 反空真 C：**建树引擎**在具体非空实例上可居留（`Fin 3`，单个三元组 `01|2`）。 -/
example : ∃ T : RootedTree.{0, 0} (Fin 3),
    T.DisplaysTriplet (mk' (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)) :=
  exists_rootedTree_displays_of_singleton (by decide) _

/-- 反空真 D：反例族**非空**且三个成员互异（故 `pairwiseCompatible_not_sufficient`
不是靠空族取巧）。 -/
example : fourLeafCounterexample.card = 3 := by decide

/-! ### 6.3 仍是**显式缺口**的部分（文献陈述，本节未证） -/

omit [Fintype X] in
/-- 三元组族 `R` 的**叶集**（`R` 中所有支撑集的并）。 -/
def systemLeaves (R : Finset (RootedTriplet X)) : Finset X :=
  R.biUnion fun t => t.leaves

/-- ★ **显式缺口 1 —— Bryant–Steel Theorem 2 的 (⟹)**：若 `T` 展示 `R` 的每个三元组，
则对每个 `S ⊇ leaves(R)`（`|S| ≥ 3`），图 `[R,S]` **不连通**。

文献：Bryant & Steel 1995，定理陈述 **766–769 行**，证明 **777–785 行**。
**缺什么**：证明要用**限制树** `T|S`（“考虑子树 `T|s`，它有最大元素 `M`；`M` 的每个直接后代
给出一个块”）—— 库内 `Phylo/Split.lean` 的 `Split.restrict` 只覆盖 **split 层**，
`RootedTree` 层的 `T|S`（抑制非 `S` 叶、抑制度 2 顶点）尚未建立。
**为什么不硬编**：不用额外假设「假装」证出来；此处只把文献陈述落成 `Prop`。 -/
def rootedTriplet_aho_disconnect_gap : Prop :=
  ∀ (R : Finset (RootedTriplet X)) (T : RootedTree.{u, u} X),
    (∀ t ∈ R, T.DisplaysTriplet t) →
    ∀ S : Finset X, (∀ t ∈ R, t.leaves ⊆ S) → 3 ≤ S.card →
      ¬ (tripletGraph S R).Preconnected

omit [Fintype X] in
/-- ★ **显式缺口 2 —— Aho/ONETREE 的完备性（BUILD 反方向）**：若某棵有根树展示 `R` 的全部
三元组，则递归判据 `AhoOK`（在叶集 `systemLeaves R` 上）**成功**。

这是本文件 ★★★ `exists_rootedTree_of_ahoOK` 的**逆**，二者合起来才是完整的有根版 Aho 定理。
文献：Bryant & Steel 1995 **759–760 行**（“The algorithm returns a tree if and only if the input
set of rooted triples is consistent”）；Aho et al. 1981 Theorem 1 的反方向。
**缺什么**：同缺口 1（需要限制树 /「块 = 远离根的团」的对应）。
**注**：`S = univ` 的版本**不可直接**陈述 —— `R = ∅` 时 `AhoOK univ ∅` 为真但
`∃ T` 的存在性对**非空** `R` 才实质；故这里取 `S = systemLeaves R`（Aho 算法真正的工作集）。 -/
def rootedTriplet_aho_converse_gap : Prop :=
  ∀ R : Finset (RootedTriplet X), DisplayedByTree R → AhoOK (systemLeaves R) R

end RootedTriplet

end Phylo
