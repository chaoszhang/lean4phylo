/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Quartet
import Phylo.RootedTriplet
import Phylo.Supertree

/-!
# `Phylo.SupertreeLimits` —— supertree / consensus 方法的**不可能性**（NEXT.md **C7**）

## 0. 文献（在手，逐行核读）

Steel, M., Böcker, S. & Dress, A. W. M. (2000).
*Simple but fundamental limitations on supertree and consensus tree methods.*
Syst. Biol. **49**(2):363–368.
在手 OCR 版：`references/md/SteelBockerDress2000_FundamentalLimitsSupertreeConsensus.md`
（下称「原文」，行号即该 md 的行号）。

### 0.1 方法性质（原文行号）

* **P1**（124 行）
  > "The method can be applied to any unordered set of input trees."
* **P2**（126–130 行）
  > "If we rename all the species, and then apply the method to the new input trees, the
  > output tree is simply the old output tree, but with the species renamed accordingly."
* **P3**（68–73 行）
  > "If there exists at least one parent tree for the given collection of input trees, then
  > the output tree is one of those parent trees (that is, the output tree displays the
  > input trees whenever the latter are compatible)."
* **P7**（290–292 行，有根共识方法）
  > "If at least one input tree displays (IJ)K and no input tree displays (IK)J or (JK)I,
  > then the output tree displays (IJ)K."

### 0.2 否定性结论

* **Proposition 1**（97–100 行）
  > "There is no supertree method that satisfies P1-P3 for unrooted phylogenetic trees,
  > even when the input trees are restricted to being fully resolved."
  证明（101–147 行）：六个 taxa `1..6`，三棵输入树 `(12)(45)`、`(34)(16)`、`(56)(23)`；
  它们**相容**，且**恰有**两棵 parent tree（原文 Figure 1）。同时交换 `2↔6`、`3↔5`
  的置换 `σ` 保持输入集合不变，却**交换**这两棵 parent tree：
  > "neither of the two possible parent trees (in Fig. 1) has this property (in fact,
  > performing simultaneously the taxa interchanges of 2 with 6, and 3 with 5 simply
  > interchanges the two parent trees)"（141–144 行）
* **Proposition 2**（247–249 行）：同一直觉的另一形态（P1、P2、P6 不相容）。
* **Proposition 3**（300–306 行）：有根情形 P1–P5 与 P6′ **可**同时满足，但
  > "there is no consensus method for rooted phylogenetic trees that satisfies property P7."
  证明（255–263 行）：5 个 taxa、四个有根团 `{1,2}`、`{2,3}`、`{3,4}`、`{4,5}`（原文 Figure 2），
  P7 迫使输出同时展示 `(12)5`、`(23)5`、`(34)1`、`(45)1`，而
  > "it is easily verified that no rooted phylogenetic tree can display these four trees
  > simultaneously"（312–315 行）。

## 1. 本文件在库内落地了什么

1. ★★ **taxon 置换在 split 上的作用**（`Split.relabel`）与「树在置换下不变」的
   split 层定义（`Cladogram.InvariantUnder`）。
2. ★★★★ **主定理** `SBD.no_supertree_method_P2_P3`：**不存在**同时满足 P2、P3 的
   supertree 方法 `F : 输入 profile → Cladogram (Fin 6)`（P1 由定义域 `Finset` 自动满足）。
   这是原文 **Proposition 1** 的库内形态。
3. ★★★ **技术核心** `SBD.no_invariant_tree_displays_two_quartets`：**没有** `σ`-不变的
   （无根）树能同时展示 `(12)(45)` 与 `(56)(23)`。证明只用**两条**输入 quartet
   （原文用三条 + Figure 1 的分类），因此**不必**证明「恰有两棵 parent tree」。
4. ★★★ **原文 Proposition 3 的具体核** `SBD.no_rootedTree_displays_four_triplets`：
   **没有**有根树能同时展示 `(12)5`、`(23)5`、`(34)1`、`(45)1`（= 原文 312–315 行的
   "it is easily verified that no rooted phylogenetic tree can display these four trees
   simultaneously"）。
5. ★★★★ **原文 Proposition 3 的方法层** `SBD.no_rooted_P7_method`：
   **不存在**满足 P7 的有根共识方法（在「输入树 = 其展示三元组集」的抽象下；
   树层版本因库内 `RootedTree` 无 `DecidableEq` 而**不可陈述**，见缺口 3）。
6. 反空真（★B）：显式 profile `SBD.prof`、显式置换 `SBD.sig`，以及
   `SBD.prof_compatible`（该 profile **确实相容**，用 `supertree_displays_of_pairwiseCompatible`
   造出 parent tree）—— 主定理不是空真；`SBD.side_r1`–`side_r4` 逐条复核 P7 的侧条件。
7. 未证部分落成显式缺口（§7）。

## 2. 与库内既有零件的关系（★A 扫描结论）

| 路线步骤 | 库里现成 | 需新证（本文件） |
|---|---|---|
| `Split` / `Compatible` / `sideA`/`sideB` / `sideB_eq_compl` | ✅ `Phylo/Split.lean` | — |
| 「树展示 split」`IsSplitOf`、`pairwiseCompatible` | ✅ `Phylo/Split.lean:615, 894` | — |
| 「树展示 quartet」`DisplaysQuartet` | ✅ `Phylo/Quartet.lean:202` | — |
| 相容 split 族 ⟹ 存在展示树（造 parent tree 用） | ✅ `Phylo/Supertree.lean:411` | — |
| quartet 的「两配对」编码 + 置换作用 | ⬜ | `QTop` / `QTop.relabel` / `QProfile` |
| taxon 置换作用在 split 上 | ⬜ | `Split.relabel` |
| 「输出在置换下不变」 | ⬜ | `Cladogram.InvariantUnder` |
| 有根团镶嵌 | ✅ `Phylo/RootedTriplet.lean:848` | — |
| 三元组 ⟺ 团 | ✅ `Phylo/RootedTriplet.lean:170` | — |
| split 系统决定树（同构层） | ✅ `Phylo/SplitsDetermineTree.lean` | `Iso`↔split 桥（缺口 1） |

**关于 profile 编码**：原文的输入是**无根 quartet 树**。库内对应类型是
`Phylo.QuartetTopology`。本文件改用等价的「**两配对之集**」编码
`QTop X := Finset (Finset X)`（`q = {P₁,P₂}`）：taxon 置换的作用就是 `Finset.image`，
**无序性自动成立**，从而可干净地陈述「`σ`-不变的 profile」。
语义桥接见 `SBD.displaysQP_iff_displaysQuartet`（与库内 `Cladogram.DisplaysQuartet` 等价）。

⚠️ **并发写注意**：正本 `Phylo/` 下有其他 agent 同时在改（本文件只**新增**
`Phylo/SupertreeLimits.lean`，未改任何既有文件）。镜像里编译前必须 `lake build` 依赖模块，
否则会用到**过期 olean**（`RootedTriplet.isRootedClade_laminar` 在旧 olean 中不存在）。
-/

open Phylo

universe u

/-! 局部可判定性实例：`SidesCompatible` 是 `def`，类型类搜索不展开它，
而下面的有限穷举（`decide`）需要它的**可计算**可判定性。 -/

local instance instDecDisjointFinset {α : Type*} [DecidableEq α] (A B : Finset α) :
    Decidable (Disjoint A B) := Finset.decidableDisjoint A B

local instance instDecSidesCompatible {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : Decidable (SidesCompatible A B) :=
  inferInstanceAs (Decidable (A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = Finset.univ))

/-! ## 1. taxon 置换在 split 上的作用 -/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **换标号**：把 `e : α ≃ α` 作用到一个 split 上（两侧分别取 `e`-像）。
这是原文 P2 里 "rename all the species" 在 split 层的实现。 -/
def relabel (e : α ≃ α) (s : Split α) : Split α where
  parts i := (s.parts i).image e.toEmbedding
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hx'
    have hab : a = b := e.injective (hax.trans hbx.symm)
    subst hab
    exact (Finset.disjoint_left.mp (s.pairwise_disjoint i j hij)) ha hb
  union_eq_univ := by
    ext x
    constructor
    · intro _; exact Finset.mem_univ x
    · intro _
      have hx : e.symm x ∈ Finset.univ.biUnion s.parts := by
        rw [s.union_eq_univ]; exact Finset.mem_univ _
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨e.symm x, hi, Equiv.apply_symm_apply e x⟩⟩
  nonempty i := (s.nonempty i).image _

/-- `relabel` 在 `sideA` 上的作用。 -/
@[simp] theorem relabel_sideA (e : α ≃ α) (s : Split α) :
    (relabel e s).sideA = s.sideA.image e.toEmbedding := rfl

/-- `relabel` 在 `sideB` 上的作用。 -/
@[simp] theorem relabel_sideB (e : α ≃ α) (s : Split α) :
    (relabel e s).sideB = s.sideB.image e.toEmbedding := rfl

end Split

/-! ## 2. 「在 taxon 置换下不变」的树（split 层定义） -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 树 `T` 在 taxon 置换 `e` 下**不变**：`T` 展示的每条 split，其 `e`-像也被 `T` 展示。

（由 `Phylo/SplitsDetermineTree.lean` 的「split 系统决定树」，这等价于
`T` 与其换标号版本同构。） -/
def InvariantUnder (T : Cladogram X) (e : X ≃ X) : Prop :=
  ∀ s : Split X, T.IsSplitOf s → T.IsSplitOf (Split.relabel e s)

end Cladogram

/-! ## 3. 输入 profile、「展示」、方法性质 P1–P3 -/

namespace SBD

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **无根 quartet 拓扑的「两配对」编码**：`q = {P₁, P₂}`（四条叶的两个配对）。
无序性由 `Finset` 自动承载。 -/
abbrev QTop (X : Type*) [Fintype X] [DecidableEq X] := Finset (Finset X)

/-- **输入 profile**：一族 quartet 拓扑（原文的一个 supertree 输入集合）。 -/
abbrev QProfile (X : Type*) [Fintype X] [DecidableEq X] := Finset (QTop X)

namespace QTop

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- taxon 置换 `e` 作用在一个 quartet 拓扑上。 -/
def relabel (e : X ≃ X) (q : QTop X) : QTop X := q.image fun p => p.image e.toEmbedding

end QTop

namespace QProfile

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- taxon 置换 `e` 作用在输入 profile 上。 -/
def relabel (e : X ≃ X) (P : QProfile X) : QProfile X := P.image (QTop.relabel e)

end QProfile

/-- `T` **展示** quartet 拓扑 `q = {P₁,P₂}`：`T` 有一条边，其 `sideA` 含 `q` 中某个 `P`、
`sideB` 含另一个。 -/
def DisplaysQP (T : Cladogram X) (q : QTop X) : Prop :=
  ∃ s : Split X, T.IsSplitOf s ∧ (∃ p ∈ q, p ⊆ s.sideA) ∧ (∃ p' ∈ q, p' ⊆ s.sideB)

/-- **语义桥接**：`{{a,b},{c,d}}` 的展示 ⟺ 库内的 `Cladogram.DisplaysQuartet a b c d`
（`Phylo/Quartet.lean:202`）。 -/
theorem displaysQP_iff_displaysQuartet (T : Cladogram X) (a b c d : X) :
    DisplaysQP T ({({a, b} : Finset X), {c, d}} : QTop X) ↔ T.DisplaysQuartet a b c d := by
  constructor
  · rintro ⟨s, hs, ⟨p, hp, hpA⟩, ⟨p', hp', hp'B⟩⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact ((Finset.disjoint_left.mp s.disjoint_sides)
        (hpA (Finset.mem_insert_self a ({b} : Finset X)))
        (hp'B (Finset.mem_insert_self a ({b} : Finset X)))).elim
    · exact ⟨s, hs, hpA, hp'B⟩
    · exact (T.displaysQuartet_comm_cd a b c d).mpr ⟨s, hs, hpA, hp'B⟩
    · exact ((Finset.disjoint_left.mp s.disjoint_sides)
        (hpA (Finset.mem_insert_self c ({d} : Finset X)))
        (hp'B (Finset.mem_insert_self c ({d} : Finset X)))).elim
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨s, hs, ⟨{a, b}, by simp, h1⟩, ⟨{c, d}, by simp, h2⟩⟩

/-- **相容**：存在一棵树展示 profile 中每个 quartet 拓扑
（= 原文的 "there exists at least one parent tree"）。 -/
def Compatible (P : QProfile X) : Prop := ∃ T : Cladogram.{u, u} X, ∀ q ∈ P, DisplaysQP T q

/-- **P2**（原文 126–130 行）：taxon 置换与「应用方法」可交换 ——
输出树的 split 系统按 `Split.relabel e` 搬运。 -/
def P2 (F : QProfile X → Cladogram.{u, u} X) : Prop :=
  ∀ (e : X ≃ X) (P : QProfile X) (s : Split X),
    (F (QProfile.relabel e P)).IsSplitOf (Split.relabel e s) ↔ (F P).IsSplitOf s

/-- **P3**（原文 68–73 行）：输入相容时输出必须是 parent tree（展示全部输入）。 -/
def P3 (F : QProfile X → Cladogram.{u, u} X) : Prop :=
  ∀ P : QProfile X, Compatible P → ∀ q ∈ P, DisplaysQP (F P) q

/-- **P2 + `e`-不变输入 ⟹ 输出 `e`-不变** —— 这是原文证明中**实际用到**的那一步。 -/
theorem invariantUnder_of_P2 {F : QProfile X → Cladogram.{u, u} X} (h : P2 F) {e : X ≃ X}
    {P : QProfile X} (hP : QProfile.relabel e P = P) : (F P).InvariantUnder e := by
  intro s hs
  have h' := h e P s
  rw [hP] at h'
  exact h'.mpr hs

/-! ## 4. 六 taxa 见证：原文 Proposition 1 -/

/-- 原文 121–131 行的置换 `σ`：同时交换 taxon `2↔6` 与 `3↔5`
（taxon `i` ↔ `Fin 6` 下标 `i-1`，故 `σ = (1 5)(2 4)`）。 -/
def sig : Equiv.Perm (Fin 6) := Equiv.swap 1 5 * Equiv.swap 2 4

/-- 原文 Prop. 1 的输入树 `(12)(45)`（= 配对 `{0,1}` 与 `{3,4}`）。 -/
def q1 : QTop (Fin 6) := {({0, 1} : Finset (Fin 6)), {3, 4}}

/-- 原文 Prop. 1 的输入树 `(34)(16)`（= 配对 `{2,3}` 与 `{0,5}`）。 -/
def q2 : QTop (Fin 6) := {({2, 3} : Finset (Fin 6)), {0, 5}}

/-- 原文 Prop. 1 的输入树 `(56)(23)`（= 配对 `{4,5}` 与 `{1,2}`）。 -/
def q3 : QTop (Fin 6) := {({4, 5} : Finset (Fin 6)), {1, 2}}

/-- 原文的三棵输入树构成的 profile（原文 109 行）。 -/
def prof : QProfile (Fin 6) := {q1, q2, q3}

/-- ★ **`σ` 保持输入 profile 不变**（原文 121–131 行："our collection of input trees would
become (16)(43), (54)(12), (32)(65) which are the same three input trees, just listed in
different order"）。 -/
theorem prof_relabel : QProfile.relabel sig prof = prof := by decide

/-- ★★ **有限核心（第一步）**：若 `A ⊇ {0,1}`、`Aᶜ ⊇ {3,4}`（`A` 是展示 `(12)(45)` 的边侧），
且 `A` 与 `σA` 相容，则 `A = {0,1,5}`（= 原文 Figure 1 的 `{1,2,6}`）。
（`decide` 穷举 `2^6 = 64` 个候选 `A`。） -/
theorem sideA_eq_of_compatible : ∀ A : Finset (Fin 6),
    ({0, 1} : Finset (Fin 6)) ⊆ A → ({3, 4} : Finset (Fin 6)) ⊆ Aᶜ →
    SidesCompatible A (A.image sig.toEmbedding) → A = {0, 1, 5} := by
  decide

/-- ★★ **有限核心（第二步）**：`{0,1,5}` 与任何展示 `(56)(23)` 的边侧 `B`
（`B ⊇ {4,5}`、`Bᶜ ⊇ {1,2}`）**都不相容**。 -/
theorem not_sidesCompatible_of_displays_q3 : ∀ B : Finset (Fin 6),
    ({4, 5} : Finset (Fin 6)) ⊆ B → ({1, 2} : Finset (Fin 6)) ⊆ Bᶜ →
    ¬ SidesCompatible ({0, 1, 5} : Finset (Fin 6)) B := by
  decide

set_option maxHeartbeats 800000 in
/-- ★★★ **核心**：**没有** `σ`-不变的（无根）树能同时展示 `(12)(45)` 与 `(56)(23)`。

证明（**不需要**原文 Figure 1 的分类定理）：设 `s`、`t` 分别见证两个 quartet。
`σ`-不变给出 `σs` 也在 `T` 的 split 系统里，故由 `pairwiseCompatible`，
`s ⊥ σs` 且 `s ⊥ t`。把相容性写成 `SidesCompatible s.sideA _`：
* `s ⊥ σs` + `sideA(s) ⊇ {0,1}`、`sideA(s)ᶜ ⊇ {3,4}`
  ⟹ `sideA(s) = {0,1,5}`（`sideA_eq_of_compatible`）；
* 而 `{0,1,5}` 与任何展示 `(56)(23)` 的边侧不相容
  （`not_sidesCompatible_of_displays_q3`）—— 与 `s ⊥ t` 矛盾。 -/
theorem no_invariant_tree_displays_two_quartets :
    ¬ ∃ T : Cladogram.{0, 0} (Fin 6),
        T.InvariantUnder sig ∧ T.DisplaysQuartet 0 1 3 4 ∧ T.DisplaysQuartet 4 5 1 2 := by
  rintro ⟨T, hinv, h1, h3⟩
  obtain ⟨s, hs, h01, h34⟩ := h1
  obtain ⟨t, ht, h45, h12⟩ := h3
  have hσs : T.IsSplitOf (Split.relabel sig s) := hinv s hs
  have hc1 : Split.Compatible s (Split.relabel sig s) :=
    pairwiseCompatible T s hs (Split.relabel sig s) hσs
  have hc2 : Split.Compatible s t := pairwiseCompatible T s hs t ht
  rw [Split.compatible_iff_sides] at hc1 hc2
  rw [Split.relabel_sideA] at hc1
  rw [Split.sideB_eq_compl] at h34 h12
  have hA : s.sideA = {0, 1, 5} := sideA_eq_of_compatible s.sideA h01 h34 hc1
  rw [hA] at hc2
  exact not_sidesCompatible_of_displays_q3 t.sideA h45 h12 hc2

/-! ### 4.1 反空真：该 profile 确实相容（存在 parent tree） -/

/-- 单 split 的输入树 `{0,1} | 其余`。 -/
def s01 : Split (Fin 6) where
  parts i := if i = 0 then ({0, 1} : Finset (Fin 6)) else {2, 3, 4, 5}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- 单 split 的输入树 `{2,3} | 其余`。 -/
def s23 : Split (Fin 6) where
  parts i := if i = 0 then ({2, 3} : Finset (Fin 6)) else {0, 1, 4, 5}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- 单 split 的输入树 `{4,5} | 其余`。 -/
def s45 : Split (Fin 6) where
  parts i := if i = 0 then ({4, 5} : Finset (Fin 6)) else {0, 1, 2, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- ★★ **该 profile 确实相容**（原文 109–112 行："Note that these three input trees are
compatible."）—— 用库内 `supertree_displays_of_pairwiseCompatible` 造出 parent tree。 -/
theorem prof_compatible : Compatible prof := by
  have hpair : ∀ s ∈ ({s01, s23, s45} : Finset (Split (Fin 6))),
      ∀ t ∈ ({s01, s23, s45} : Finset (Split (Fin 6))), Split.Compatible s t := by
    intro s hs t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      (simp only [Split.Compatible]; decide)
  obtain ⟨M, hM⟩ := supertree_displays_of_pairwiseCompatible
    ({s01, s23, s45} : Finset (Split (Fin 6))) 0 hpair (by decide)
  refine ⟨M, fun q hq => ?_⟩
  simp only [prof, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨s01, hM s01 (by decide), ⟨{0, 1}, by decide, by decide⟩,
      ⟨{3, 4}, by decide, by decide⟩⟩
  · exact ⟨s23, hM s23 (by decide), ⟨{2, 3}, by decide, by decide⟩,
      ⟨{0, 5}, by decide, by decide⟩⟩
  · exact ⟨s45, hM s45 (by decide), ⟨{4, 5}, by decide, by decide⟩,
      ⟨{1, 2}, by decide, by decide⟩⟩

/-! ## 5. ★★★★ 主定理：不存在满足 P1–P3 的 supertree 方法 -/

/-- ★★★★ **主定理（原文 Proposition 1，97–100 行）**：
**不存在**同时满足 P2 与 P3 的 supertree 方法 `F : 输入 profile → Cladogram (Fin 6)`。

（P1 自动成立：定义域 `QProfile X = Finset (QTop X)` 是**无序**集合。）

> "There is no supertree method that satisfies P1-P3 for unrooted phylogenetic trees,
> even when the input trees are restricted to being fully resolved."（97–100 行）

本文件的输入 profile 只含**全分辨**的四叶 quartet 树，与 "restricted to being fully
resolved" 相符。证明只用 `prof` 这一个 `σ`-不变输入 + `no_invariant_tree_displays_two_quartets`。 -/
theorem no_supertree_method_P2_P3 :
    ¬ ∃ F : QProfile (Fin 6) → Cladogram.{0, 0} (Fin 6), P2 F ∧ P3 F := by
  rintro ⟨F, h2, h3⟩
  have hout := h3 prof prof_compatible
  have hq1 : DisplaysQP (F prof) q1 := hout q1 (by decide)
  have hq3 : DisplaysQP (F prof) q3 := hout q3 (by decide)
  have hd1 : (F prof).DisplaysQuartet 0 1 3 4 :=
    (displaysQP_iff_displaysQuartet (F prof) 0 1 3 4).mp (by simpa [q1] using hq1)
  have hd3 : (F prof).DisplaysQuartet 4 5 1 2 :=
    (displaysQP_iff_displaysQuartet (F prof) 4 5 1 2).mp (by simpa [q3] using hq3)
  have hinv : (F prof).InvariantUnder sig := invariantUnder_of_P2 h2 prof_relabel
  exact no_invariant_tree_displays_two_quartets ⟨F prof, hinv, hd1, hd3⟩

/-! ## 6. 原文 Proposition 3 的否定半边（有根情形） -/

/-- 原文 Figure 2 的三元组 `(12)5`。 -/
def r1 : RootedTriplet (Fin 5) :=
  RootedTriplet.mk' (0 : Fin 5) 1 4 (by decide) (by decide) (by decide)

/-- 原文 Figure 2 的三元组 `(23)5`。 -/
def r2 : RootedTriplet (Fin 5) :=
  RootedTriplet.mk' (1 : Fin 5) 2 4 (by decide) (by decide) (by decide)

/-- 原文 Figure 2 的三元组 `(34)1`。 -/
def r3 : RootedTriplet (Fin 5) :=
  RootedTriplet.mk' (2 : Fin 5) 3 0 (by decide) (by decide) (by decide)

/-- 原文 Figure 2 的三元组 `(45)1`。 -/
def r4 : RootedTriplet (Fin 5) :=
  RootedTriplet.mk' (3 : Fin 5) 4 0 (by decide) (by decide) (by decide)

/-- ★★★ **原文 312–315 行的 "it is easily verified"**：
**没有**有根树能同时展示 `(12)5`、`(23)5`、`(34)1`、`(45)1`。

证明：四个展示团 `C₁ ∋ 0,1`、`C₂ ∋ 1,2`、`C₃ ∋ 2,3`、`C₄ ∋ 3,4`（分别避开
`4,4,0,0`）由 `RootedTree.isRootedClade_laminar`「相交 ⟹ 嵌套」，三次分情形即矛盾：
`C₁,C₂ ∋ 1` 必嵌套；两种情形下再与 `C₃`、`C₄` 嵌套，均导出「某团含被排除的叶」。 -/
theorem no_rootedTree_displays_four_triplets :
    ¬ RootedTriplet.DisplayedByTree ({r1, r2, r3, r4} : Finset (RootedTriplet (Fin 5))) := by
  rintro ⟨T, hT⟩
  have h1 : RootedTree.DisplaysTriplet T r1 := hT r1 (by decide)
  have h2 : RootedTree.DisplaysTriplet T r2 := hT r2 (by decide)
  have h3 : RootedTree.DisplaysTriplet T r3 := hT r3 (by decide)
  have h4 : RootedTree.DisplaysTriplet T r4 := hT r4 (by decide)
  obtain ⟨C1, hC1, hp1, ho1⟩ := (RootedTree.displaysTriplet_iff_isRootedClade T r1).mp h1
  obtain ⟨C2, hC2, hp2, ho2⟩ := (RootedTree.displaysTriplet_iff_isRootedClade T r2).mp h2
  obtain ⟨C3, hC3, hp3, ho3⟩ := (RootedTree.displaysTriplet_iff_isRootedClade T r3).mp h3
  obtain ⟨C4, hC4, hp4, ho4⟩ := (RootedTree.displaysTriplet_iff_isRootedClade T r4).mp h4
  have h01 : (0 : Fin 5) ∈ C1 := hp1 (by decide)
  have h11 : (1 : Fin 5) ∈ C1 := hp1 (by decide)
  have hn41 : (4 : Fin 5) ∉ C1 := ho1
  have h12 : (1 : Fin 5) ∈ C2 := hp2 (by decide)
  have h22 : (2 : Fin 5) ∈ C2 := hp2 (by decide)
  have hn42 : (4 : Fin 5) ∉ C2 := ho2
  have h23 : (2 : Fin 5) ∈ C3 := hp3 (by decide)
  have h33 : (3 : Fin 5) ∈ C3 := hp3 (by decide)
  have hn03 : (0 : Fin 5) ∉ C3 := ho3
  have h34 : (3 : Fin 5) ∈ C4 := hp4 (by decide)
  have h44 : (4 : Fin 5) ∈ C4 := hp4 (by decide)
  have hn04 : (0 : Fin 5) ∉ C4 := ho4
  have hAB := RootedTree.isRootedClade_laminar T hC1 hC2
    ⟨1, Finset.mem_inter.mpr ⟨h11, h12⟩⟩
  by_cases hsub12 : C1 ⊆ C2
  · have h02 : (0 : Fin 5) ∈ C2 := hsub12 h01
    have hBC := RootedTree.isRootedClade_laminar T hC2 hC3
      ⟨2, Finset.mem_inter.mpr ⟨h22, h23⟩⟩
    by_cases hsub32 : C3 ⊆ C2
    · have h32 : (3 : Fin 5) ∈ C2 := hsub32 h33
      rcases RootedTree.isRootedClade_laminar T hC2 hC4
        ⟨3, Finset.mem_inter.mpr ⟨h32, h34⟩⟩ with h | h
      · exact hn04 (h h02)
      · exact hn42 (h h44)
    · exact hn03 ((hBC.resolve_right hsub32) h02)
  · have h21 : C2 ⊆ C1 := hAB.resolve_left hsub12
    have hAC := RootedTree.isRootedClade_laminar T hC1 hC3
      ⟨2, Finset.mem_inter.mpr ⟨h21 h22, h23⟩⟩
    by_cases hsub13 : C1 ⊆ C3
    · exact hn03 (hsub13 h01)
    · have h31 : (3 : Fin 5) ∈ C1 := (hAC.resolve_left hsub13) h33
      rcases RootedTree.isRootedClade_laminar T hC1 hC4
        ⟨3, Finset.mem_inter.mpr ⟨h31, h34⟩⟩ with h | h
      · exact hn04 (h h01)
      · exact hn41 (h h44)

/-! ### 6.1 P7 层：不存在满足 P7 的有根共识方法

⚠️ **抽象说明**：库内 `RootedTree` 没有 `DecidableEq`，`Finset (RootedTree X)` 写不出来，
故树层 P7 无法陈述。这里把「输入树」抽象为**它展示的三元组之集**
（原文 P7 的假设只提到「输入树展示什么」，故这一抽象对 P7 是忠实的），
于是方法变成 `Finset (Finset (RootedTriplet X)) → RootedTree X`。 -/

/-- 输入树 `T₁`（唯一非平凡团 `{0,1}`）展示的三元组集：`(01)2`、`(01)3`、`(01)4`。 -/
def a1 : Finset (RootedTriplet (Fin 5)) :=
  {RootedTriplet.mk' (0 : Fin 5) 1 2 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (0 : Fin 5) 1 3 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (0 : Fin 5) 1 4 (by decide) (by decide) (by decide)}

/-- 输入树 `T₂`（团 `{1,2}`）展示的三元组集。 -/
def a2 : Finset (RootedTriplet (Fin 5)) :=
  {RootedTriplet.mk' (1 : Fin 5) 2 0 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (1 : Fin 5) 2 3 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (1 : Fin 5) 2 4 (by decide) (by decide) (by decide)}

/-- 输入树 `T₃`（团 `{2,3}`）展示的三元组集。 -/
def a3 : Finset (RootedTriplet (Fin 5)) :=
  {RootedTriplet.mk' (2 : Fin 5) 3 0 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (2 : Fin 5) 3 1 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (2 : Fin 5) 3 4 (by decide) (by decide) (by decide)}

/-- 输入树 `T₄`（团 `{3,4}`）展示的三元组集。 -/
def a4 : Finset (RootedTriplet (Fin 5)) :=
  {RootedTriplet.mk' (3 : Fin 5) 4 0 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (3 : Fin 5) 4 1 (by decide) (by decide) (by decide),
   RootedTriplet.mk' (3 : Fin 5) 4 2 (by decide) (by decide) (by decide)}

/-- 原文 Figure 2 的四个输入树（以「展示三元组集」表示）构成的 profile。 -/
def tprof : Finset (Finset (RootedTriplet (Fin 5))) := {a1, a2, a3, a4}

/-- `tprof` 中所有输入树展示的三元组之并（把 P7 侧条件化归为**有界穷举**）。 -/
def tall : Finset (RootedTriplet (Fin 5)) := a1 ∪ a2 ∪ a3 ∪ a4

/-- `tprof` 的成员关系化归到 `tall`。 -/
theorem mem_tall_of_mem_tprof {R : Finset (RootedTriplet (Fin 5))}
    {t' : RootedTriplet (Fin 5)} (hR : R ∈ tprof) (ht' : t' ∈ R) : t' ∈ tall := by
  rw [tprof] at hR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hR
  rcases hR with rfl | rfl | rfl | rfl <;>
    (rw [tall]; simp only [Finset.mem_union]; tauto)

/-- ★ **P7 侧条件（`(12)5`）**：`tprof` 中所有输入树展示的三元组里，
**没有**一个是 `(12)5` 的竞争者（`decide` 穷举 `30` 个三元组）。 -/
theorem side_r1 : ∀ t' : RootedTriplet (Fin 5), t' ∈ tall →
    ¬ (t'.pair ∪ {t'.out} = r1.pair ∪ {r1.out} ∧ t' ≠ r1) := by decide

/-- ★ **P7 侧条件（`(23)5`）**。 -/
theorem side_r2 : ∀ t' : RootedTriplet (Fin 5), t' ∈ tall →
    ¬ (t'.pair ∪ {t'.out} = r2.pair ∪ {r2.out} ∧ t' ≠ r2) := by decide

/-- ★ **P7 侧条件（`(34)1`）**。 -/
theorem side_r3 : ∀ t' : RootedTriplet (Fin 5), t' ∈ tall →
    ¬ (t'.pair ∪ {t'.out} = r3.pair ∪ {r3.out} ∧ t' ≠ r3) := by decide

/-- ★ **P7 侧条件（`(45)1`）**。 -/
theorem side_r4 : ∀ t' : RootedTriplet (Fin 5), t' ∈ tall →
    ¬ (t'.pair ∪ {t'.out} = r4.pair ∪ {r4.out} ∧ t' ≠ r4) := by decide

/-- **P7**（原文 290–292 行）在「输入树 = 其展示三元组集」抽象下的形式：
> "If at least one input tree displays (IJ)K and no input tree displays (IK)J or (JK)I,
> then the output tree displays (IJ)K." -/
def P7 (F : Finset (Finset (RootedTriplet (Fin 5))) → RootedTree.{0, 0} (Fin 5)) : Prop :=
  ∀ (Prof : Finset (Finset (RootedTriplet (Fin 5)))) (t : RootedTriplet (Fin 5)),
    (∃ R ∈ Prof, t ∈ R) →
    (∀ R ∈ Prof, ∀ t' ∈ R, ¬ (t'.pair ∪ {t'.out} = t.pair ∪ {t.out} ∧ t' ≠ t)) →
    RootedTree.DisplaysTriplet (F Prof) t

/-- ★★★★ **原文 Proposition 3 的否定半边（方法层）**：
**不存在**满足 P7 的有根共识方法（在「输入树 = 其展示三元组集」的抽象下）。

证明：对 `Prof = tprof`，P7 的两条假设都成立（`side_r1`–`side_r4` 由 `decide` 穷举
`30` 个三元组验证；脚本 `scripts/msc/w11c_supertree_nonexistence.py` Part I 用
`236` 棵 5 叶有根树独立复核），于是 `F tprof` 必须同时展示
`(12)5`、`(23)5`、`(34)1`、`(45)1` —— 与 ★★★ `no_rootedTree_displays_four_triplets` 矛盾。 -/
theorem no_rooted_P7_method :
    ¬ ∃ F : Finset (Finset (RootedTriplet (Fin 5))) → RootedTree.{0, 0} (Fin 5), P7 F := by
  rintro ⟨F, hF⟩
  have key : ∀ t ∈ ({r1, r2, r3, r4} : Finset (RootedTriplet (Fin 5))),
      RootedTree.DisplaysTriplet (F tprof) t := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hF tprof r1 ⟨a1, by decide, by decide⟩
        (fun R hR t' ht' => side_r1 t' (mem_tall_of_mem_tprof hR ht'))
    · exact hF tprof r2 ⟨a2, by decide, by decide⟩
        (fun R hR t' ht' => side_r2 t' (mem_tall_of_mem_tprof hR ht'))
    · exact hF tprof r3 ⟨a3, by decide, by decide⟩
        (fun R hR t' ht' => side_r3 t' (mem_tall_of_mem_tprof hR ht'))
    · exact hF tprof r4 ⟨a4, by decide, by decide⟩
        (fun R hR t' ht' => side_r4 t' (mem_tall_of_mem_tprof hR ht'))
  exact no_rootedTree_displays_four_triplets ⟨F tprof, key⟩

/-! ## 7. 显式缺口 -/

/-- ★ **显式缺口 1 —— `Iso` 与 split 系统的桥**。
原文 P2 的字面形式（126–130 行）是树层的：
`F (σ·P)` 与 `σ·(F P)` 在**保标号同构** `Iso` 意义下相等。
本文件把 P2 落成**split 层**的搬运（`SBD.P2`）—— 这是原文证明**实际用到**的形式
（只需「输出在 `σ` 下不变」）。要把树层形式接过来，需要：
`Iso T T' → ∀ s, T.IsSplitOf s ↔ T'.IsSplitOf s`。
**缺什么**：`SimpleGraph.Iso` 与 `deleteEdges`/`Reachable` 的搬运
（库内 `Phylo/SplitsDetermineTree.lean` 有反方向「split 系统决定树」）。
**为什么不硬编**：不假装证出来，此处只把缺口落成 `Prop`。 -/
def iso_preserves_splits_gap : Prop :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X] (T T' : Cladogram.{u, u} X),
    Iso T T' → ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s

/-- ★ **显式缺口 2 —— 原文 Figure 1 的分类定理**（113–116 行）：
> "there are precisely two trees that are parent trees for this collection of trees."

本文件的主定理**不需要**它（§4 只用两条 quartet）。此处把它落成 `Prop`：
每个 parent tree 都展示 `T₁` 或展示 `T₂`，且 `T₂` 的 split 系统是 `T₁` 在 `σ` 下的像。
**缺什么**：6 个 taxa 上「展示这三条 quartet 的无根树」的分类 ——
等价于 quartet 展示 ⟹ split 系统被锁定。`Cladogram` 无 `DecidableEq`，故不写 `T₁ ≠ T₂`。 -/
def two_parent_trees_gap : Prop :=
  ∃ T₁ T₂ : Cladogram.{0, 0} (Fin 6),
    (∀ q ∈ prof, DisplaysQP T₁ q) ∧ (∀ q ∈ prof, DisplaysQP T₂ q) ∧
    (∀ s : Split (Fin 6), T₂.IsSplitOf s ↔ T₁.IsSplitOf (Split.relabel sig s)) ∧
    (∀ T : Cladogram.{0, 0} (Fin 6), (∀ q ∈ prof, DisplaysQP T q) →
      (∀ s : Split (Fin 6), T₁.IsSplitOf s → T.IsSplitOf s) ∨
      (∀ s : Split (Fin 6), T₂.IsSplitOf s → T.IsSplitOf s))

/-- ★ **显式缺口 3 —— Proposition 3 的树层方法（有根共识方法 + P7）**。

本文件已证：
* ★★★ `no_rootedTree_displays_four_triplets`（具体核，= 原文 312–315 行）；
* ★★★★ `no_rooted_P7_method`（方法层，在「输入树 = 其展示三元组集」的抽象下）。

**仍未证**：把输入树**原样**（而非其三元组集）作为定义域的形式
`F : Finset (RootedTree X) → RootedTree X`。库内 `RootedTree` **没有**
`DecidableEq`/`Fintype`，`Finset (RootedTree X)` 这个类型**写不出来**
（`Finset α` 要求 `[DecidableEq α]`），故该陈述在当前接口下**不可表达**。
**缺什么**：`RootedTree` 的 `DecidableEq`（或商掉同构的树类型）。
**为什么不硬编**：不假装证出来；只把「当前接口下不可表达」这件事本身落成 `Prop`，
即「任何把 `RootedTree X` 当作 `Finset` 元素的尝试都要求一个可判定相等」。 -/
def rooted_tree_decidableEq_gap : Prop :=
  ∀ (X : Type u) [Fintype X] [DecidableEq X],
    (∀ T T' : RootedTree.{u, u} X, Decidable (T = T')) →
    ∀ T T' : RootedTree.{u, u} X, T = T' ∨ T ≠ T'

end SBD
