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
  （Bryant–Steel 1995 Theorem 2 中 `[R,L]` 连通即反例；本文件未形式化该反例）。
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

end Phylo
