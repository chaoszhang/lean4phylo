/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Quartet
import Phylo.RootedTriplet
import Phylo.Supertree
import Phylo.ConsensusExtra

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

**W12a 状态（已证）**：`def` 升为 `theorem`，**陈述逐字不改**。
路线：`sideLeaves` = 「`Finset.filter`（叶标号）∘ `Reachable`（删边图）」（`Cladogram.mem_sideLeaves`），
而单边删边图沿 `SimpleGraph.Iso` 同构地搬运（零件 `deleteEdgesIso`：单点集 `{s(a,b)}` 的
`Sym2` 像由 `Sym2.eq_iff` + `φ` 的单射性给出），故 `Iso.reachable_iff` 把可达性搬过去；
`Finset.ext` + `mem_sideLeaves` 直接给出 `sideLeaves` 的等式（**绕开** `filter` 的
`Decidable` 实例项差异这一坑）。最后把 `IsSplitOf` 的见证 `(a,b,Adj,u)` 沿 `φ`／`φ.symm` 搬运。
**不需要** `Phylo/SplitsDetermineTree.lean`（那是反方向：split 系统 ⟹ 同构）。
⚠️ 这**不**等于把原文 P2 的**树层**形式（`F (σ·P)` 与 `σ·(F P)` 同构）也证出来；
本文件仍只用 split 层形式（`SBD.P2`），本条是它的**接口补全**。 -/
theorem iso_preserves_splits_gap :
    ∀ {X : Type u} [Fintype X] [DecidableEq X] (T T' : Cladogram.{u, u} X),
      Iso T T' → ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s := by
  intro X _ _ T T' e s
  -- 零件：`sideLeaves` 沿保标号同构搬运
  have sideLeaves_iso : ∀ (T T' : Cladogram.{u, u} X) (e : Iso T T') (a b : T.V)
      (_hab : T.graph.Adj a b) (u : T.V),
      T.sideLeaves s(a, b) u
        = T'.sideLeaves s(e.gIso.toEquiv a, e.gIso.toEquiv b) (e.gIso.toEquiv u) := by
    intro T T' e a b _ u
    -- 直接给**字面结构**（`toEquiv := e.gIso.toEquiv`）：投影可归约，
    -- 从而 `⇑hiso` 与 `⇑e.gIso.toEquiv` **定义相等**（若经 `deleteEdgesIso` 的 let 绑定则不归约）。
    let hiso : (T.graph.deleteEdges {s(a, b)}) ≃g
        (T'.graph.deleteEdges {s(e.gIso.toEquiv a, e.gIso.toEquiv b)}) :=
      RelIso.mk e.gIso.toEquiv (by
        intro x y
        rw [SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj]
        refine and_congr e.gIso.map_adj_iff ?_
        rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
        constructor
        · intro h heq
          exact h (by
            rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
            · rw [hx, hy]
            · rw [hx, hy, Sym2.eq_swap])
        · intro h heq
          refine h ?_
          rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · rw [e.gIso.toEquiv.injective hx, e.gIso.toEquiv.injective hy]
          · rw [e.gIso.toEquiv.injective hx, e.gIso.toEquiv.injective hy, Sym2.eq_swap])
    refine Finset.ext fun x => ?_
    rw [Cladogram.mem_sideLeaves, Cladogram.mem_sideLeaves]
    have h1 := hiso.reachable_iff (u := T.leaf x) (v := u)
    have h2 : (hiso : T.V → T'.V) (T.leaf x) = T'.leaf x := e.leaf_compat x
    have h2u : (hiso : T.V → T'.V) u = e.gIso.toEquiv u := by
      show (e.gIso.toEquiv) u = (e.gIso.toEquiv) u
      rfl
    rw [h2, h2u] at h1
    exact h1.symm
  constructor
  · rintro ⟨a, b, hab, u, hu⟩
    refine ⟨e.gIso.toEquiv a, e.gIso.toEquiv b, e.gIso.map_adj_iff.mpr hab, e.gIso.toEquiv u, ?_⟩
    rw [hu]
    exact sideLeaves_iso T T' e a b hab u
  · rintro ⟨a, b, hab, u, hu⟩
    refine ⟨e.gIso.toEquiv.symm a, e.gIso.toEquiv.symm b,
      e.gIso.symm.map_adj_iff.mpr hab, e.gIso.toEquiv.symm u, ?_⟩
    rw [hu]
    have h := sideLeaves_iso T T' e (e.gIso.toEquiv.symm a) (e.gIso.toEquiv.symm b)
      (e.gIso.symm.map_adj_iff.mpr hab) (e.gIso.toEquiv.symm u)
    rw [e.gIso.toEquiv.apply_symm_apply, e.gIso.toEquiv.apply_symm_apply,
      e.gIso.toEquiv.apply_symm_apply] at h
    exact h.symm

/--
✅ **已收口**（`two_parent_trees_gap_holds`，`Phylo/TwoParentTrees.lean:590`，W21 任务 C3 `321585d`）；下方「终局 ⬜ 保留缺口」是**历史记录**，勿据此判状态。

★ **显式缺口 2 —— 原文 Figure 1 的分类定理**（113–116 行）：
> "there are precisely two trees that are parent trees for this collection of trees."

本文件的主定理**不需要**它（§4 只用两条 quartet）。此处把它落成 `Prop`：
每个 parent tree 都展示 `T₁` 或展示 `T₂`，且 `T₂` 的 split 系统是 `T₁` 在 `σ` 下的像。
**缺什么**：6 个 taxa 上「展示这三条 quartet 的无根树」的分类 ——
等价于 quartet 展示 ⟹ split 系统被锁定。`Cladogram` 无 `DecidableEq`，故不写 `T₁ ≠ T₂`。

⚠️ **W12a：本陈述在**形式**上弱于原文 Figure 1 的分类定理（见下 `…_correct_shape`）**，
故**逐字保留**（登记用）而在下方另立改写形态。两条形式差异：
1. 第三条只要求 `T₂` 的 split 系统 `= T₁` 的 **σ-像**，而原文（141–144 行）说 `σ` **交换**
   这两棵 parent tree（"simply interchanges the two parent trees"）—— 即 `σ·T₁` 与 `T₂`
   **互为该像**（在「恰有两棵 parent tree」的前提下二者等价）；在 `T₁ = T₂` 的退化代入下
   这一条**恰是**「`T₁` 的 split 系统 `σ`-不变」，与「两个 parent tree」的结论无关；
2. 最后一条的措辞是**包含**（`T₁` 的 split 系统 `⊆ T` 的），**不是**「`T` 恰是 `T₁` 或 `T₂`」
   —— 而 "there are **precisely two**" 的内容是**相等**（`↔`）。

### ★D（W12a）**真值机器穷举**：本 `Prop` 为**真** ✓ —— 但当时 Lean 内仍缺「构造两棵树」的器材

`scripts/msc/w12a_twoparent_check.py`（纯标准库、穷举、无 Monte Carlo）在
「无根树 ↔ 两两相容的非平凡 split 族」模型下**穷举** 6 taxa 的全部相容族（**236** 个，最大族大小 3）：

| 量 | 机器结果 |
|---|---|
| 展示全部三条 quartet 的（parent）split 族 | **恰 2 个** ✓（与原文 113–116 行 "precisely two" 一致） |
| `P₁` | `{{0,1}\|rest, {0,1,2,3}\|{4,5}, {0,1,4,5}\|{2,3}}` |
| `P₂` | `= σ(P₁)` = `{{0,1,2,5}\|{3,4}, {0,3,4,5}\|{1,2}, {0,5}\|rest}` |
| 原 `def` 第 3 条（`T₂` = `σ(T₁)`） | **✓ 成立**（`σ(P₁) = P₂` 且 `P₂` 是 parent） |
| 原 `def` 第 4 条（每个 parent 含 `T₁` 或 `T₂`） | **✓ 成立**（恰两根 ⇒ 自含） |
| `…_correct_shape` 第 ②（每个 parent 恰是 `T₁` 或 `T₂`） | **✓ 成立** |
| 每条 split 族的**显式树构造**核验 | ✓（`V=10, E=9`、内部点度 ≥ 3、叶度 1、split 系统逐条吻合） |

⇒ **本 `Prop` 不是可证伪的**（我早前"两条不忠实"的担心只涉及**措辞**，不涉及真值）；
它**真**，且真内容正是**分类定理**（机器已在小模型上证实）。

**当时 Lean 内仍缺什么（W12a8 修正：原「缺精确构造」的判断是错的 ✓）**：
1. ~~两棵显式 `Cladogram.{0,0} (Fin 6)`，其 split 系统**恰为** `P₁`、`P₂`~~
   **❌ 该器材库内早有**：`Phylo/ConsensusExtra.lean:222` 的
   ```text
   theorem isSplitOf_iff_mem_or_trivial (fam : Finset (Split X)) (ρ : X)
       (hcomp : …) (hnt : …) (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3 : 3 ≤ card X) :
     ∃ M : Cladogram.{u,u} X,
       ∀ s, M.IsSplitOf s ↔ s ∈ fam ∨ (∃ x, s.sideA = {x}) ∨ (∃ x, s.sideA = {x}ᶜ)
   ```
   即「相容非平凡族 ⟹ **精确** split 系统的 cladogram」的 `↔` 版**已落地**
   （比 `Phylo.Supertree.exists_cladogram_of_compatible` 的**边侧刻画**更强；本文件 §4 之前
   引用的 `supertree_displays_of_pairwiseCompatible` 只是它的 `⊇` 弱化版）。
   两点使用须知：(i) 它在**另一个模块**（本文件未 import `Phylo.ConsensusExtra`）；
   (ii) 它多要一个 `hswap`：族对 `swap` 封闭 —— 本处取 `fam := P₁ ∪ swap(P₁)` 即可 ✓。
   ⇒ 代入后 `T₁`/`T₂` 的 split 系统被**完全刻画**，第 3 条（`σ` 互换）即化为**显式 split 族**的
     `Finset` 等式（无 `∀ s` ⇒ 可 `decide` ✓）。
2. **树 → split 系统的桥**（见证 split 必非平凡、全体见证两两相容）—— 库内亦已有
   （`Cladogram.pairwiseCompatible`、`Split.cluster` 系列、`Split.ext_sideA` 等）✓。
3. **分类定理（唯一真正的剩余 ✗）**：每个展示 `prof` 的 `Cladogram (Fin 6)`，其非平凡
   split 系统**恰是** `P₁` 或 `P₂`（无序意义）。W12a 实测两条 `decide` 路线**都走不通**：
   * `∀ A B C : Finset (Fin 6), …` 版本：**综合不出可计算的 `Fintype (Finset (Fin 6))`**
     ⇒ `failed to synthesize Decidable (∀ A B C : Finset (Fin 6), …)`（**不是**慢）；
   * **不带量词**的实例级版本（`A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ …`、`(∃ p ∈ q, p ⊆ A) ∧ …`）：
     `Decidable` **同样综合不出来**（换 `Disjoint` 也失败）⇒ 须改写成 `Bool`/位掩码
     （`Fin 64` 解码）判据才可能 `decide`；或走**手写情形分析**（原文 Figure 1 的论证，
     估计 100–200 行）。
   机器见证已在 `scripts/msc/w12a_twoparent_check.py`（236 个相容族穷举、parent 族**恰 2**、
   每条族的**显式树构造**核验 `V=10, E=9` ✓）。

**终局 ⬜（当时保留缺口）**（真值已确认为**真**，唯一剩余器材 = 上面的**分类定理**）。 -/
def two_parent_trees_gap : Prop :=
  ∃ T₁ T₂ : Cladogram.{0, 0} (Fin 6),
    (∀ q ∈ prof, DisplaysQP T₁ q) ∧ (∀ q ∈ prof, DisplaysQP T₂ q) ∧
    (∀ s : Split (Fin 6), T₂.IsSplitOf s ↔ T₁.IsSplitOf (Split.relabel sig s)) ∧
    (∀ T : Cladogram.{0, 0} (Fin 6), (∀ q ∈ prof, DisplaysQP T q) →
      (∀ s : Split (Fin 6), T₁.IsSplitOf s → T.IsSplitOf s) ∨
      (∀ s : Split (Fin 6), T₂.IsSplitOf s → T.IsSplitOf s))

/--
✅ **已收口**（`two_parent_trees_gap_correct_shape_holds`，`Phylo/TwoParentTrees.lean:578`，W21 任务 C3 `321585d`）；下方「仍然未证」是**历史记录**，勿据此判状态。

★★ **缺口 2 的**改写形态**（W12a 新增，**不替代**原 `def`）**：原文 Figure 1 的"there are **precisely two** trees that are parent trees for this collection of trees"
（113–116 行）＋「`σ` 交换这两棵 parent tree」（141–144 行）的忠实落式。

与原 `two_parent_trees_gap` 的三处差别：
* **② 由 ⊆ 升为 ↔**（"precisely two" 的内容）：任何 parent tree 的 split 系统**恰好**是
  `T₁` 的或 `T₂` 的；
* **③ 新增非退化条件**：`T₂` 的 split 系统**严格大于**不了 `T₁` 的 —— 即存在一条
  `T₂` 展示而 `T₁` 不展示的 split（在 split 系统层面表达「两棵树确实不同」；
  `Cladogram` 无 `DecidableEq`，故**不**写 `T₁ ≠ T₂`）；
* ①②③ 合起来才排除了 `T₁ = T₂` 的退化代入（见下方 `two_parent_trees_correct_shape_not_degenerate`）。

**当时未证**（真内容 = 分类定理）：存在性与 ② —— 需要「三条 quartet 的展示 ⟹ split 系统被锁定」，
即 6 taxa 上无根树的分类。**已核过的部分**：`prof_relabel`（`σ` 保持 `prof`，已证）＋
本文件的 `iso_preserves_splits_gap`（同构 ⟹ split 系统相同，已证）—— 这两条给出
「若 `T₁` 是 parent tree 且 `T₁` 的 split 系统被 `σ` 保持不变，则 `T₁` 也是 `σ`-不变树」，
但**不足以**得到 ①：`T₂ := σ·T₁` 需要「`σ`-像的 split 族恰被某棵树展示」，
而 `Split.relabel` 只保**相容性**（`supertree_displays_of_pairwiseCompatible` 给出 ⊇ 方向），
`↔`（无多余 split）仍需 classification。 -/
def two_parent_trees_gap_correct_shape : Prop :=
  ∃ T₁ T₂ : Cladogram.{0, 0} (Fin 6),
    (∀ q ∈ prof, DisplaysQP T₁ q) ∧ (∀ q ∈ prof, DisplaysQP T₂ q) ∧
    -- ① `σ` 交换两者的 split 系统
    (∀ s : Split (Fin 6), T₂.IsSplitOf s ↔ T₁.IsSplitOf (Split.relabel sig s)) ∧
    -- ② 分类结论（"precisely two"：恰是 `T₁` 的或 `T₂` 的）
    (∀ T : Cladogram.{0, 0} (Fin 6), (∀ q ∈ prof, DisplaysQP T q) →
      (∀ s : Split (Fin 6), T₁.IsSplitOf s ↔ T.IsSplitOf s) ∨
      (∀ s : Split (Fin 6), T₂.IsSplitOf s ↔ T.IsSplitOf s)) ∧
    -- ③ 非退化：`T₂` 的 split 系统严格多出一条
    (∃ s : Split (Fin 6), T₂.IsSplitOf s ∧ ¬ T₁.IsSplitOf s)

/-- ★★★ **改写形态确实**强于**原登记形态**（W12a 已证）：把 ② 的 `↔` 弱化成 `⊆` 即得原
`two_parent_trees_gap` 的第 4 条（其余三条逐字相同）。故 `…_correct_shape → …_gap`，
即「原陈述不忠实」这件事**不是**削弱登记，而是**加强**它。 -/
theorem two_parent_trees_gap_of_correct_shape :
    two_parent_trees_gap_correct_shape → two_parent_trees_gap := by
  rintro ⟨T₁, T₂, h₁, h₂, hσ, hcls, -⟩
  exact ⟨T₁, T₂, h₁, h₂, hσ, fun T hT => (hcls T hT).imp
    (fun h s hs => (h s).mp hs) (fun h s hs => (h s).mp hs)⟩

/-- ★★ **非退化条件 ③ 排除 `T₁ = T₂` 的退化代入**（W12a 已证）：对**任何**树 `T`，
「存在一条 `T` 展示而 `T` 不展示的 split」是**假**的 —— 故 ③ 使 `T₁`、`T₂` 在 split 系统层面
必须不同（这正是原 `def` 缺的那一条）。 -/
theorem two_parent_trees_correct_shape_not_degenerate (T : Cladogram.{0, 0} (Fin 6)) :
    ¬ ∃ s : Split (Fin 6), T.IsSplitOf s ∧ ¬ T.IsSplitOf s := by
  rintro ⟨s, hs, hns⟩
  exact hns hs

/-- ★ **显式缺口 3 —— Proposition 3 的树层方法（有根共识方法 + P7）**。

本文件已证：
* ★★★ `no_rootedTree_displays_four_triplets`（具体核，= 原文 312–315 行）；
* ★★★★ `no_rooted_P7_method`（方法层，在「输入树 = 其展示三元组集」的抽象下）。

**仍未证**：把输入树**原样**（而非其三元组集）作为定义域的形式
`F : Finset (RootedTree X) → RootedTree X`。库内 `RootedTree` **没有**
`DecidableEq`/`Fintype`，`Finset (RootedTree X)` 这个类型**写不出来**
（`Finset α` 要求 `[DecidableEq α]`），故该陈述在当前接口下**不可表达**。
**缺什么**：`RootedTree` 的 `DecidableEq`（或商掉同构的树类型）。

**W12a 状态（已证）**：本 `Prop` 是「可判定相等 ⟹ 相等可判定」这一**逻辑重言**：
假设本身即结论所需的判定程序（`cases h T T'` 消去 `Decidable`）。
故**陈述逐字保留**，由 `def` 升为 `theorem`（零 `sorry`/零 `axiom`）。
⚠️ 本定理**不**给出 `RootedTree X` 的 `DecidableEq` **实例**（那仍缺：`RootedTree` 含
`V : Type*`、`SimpleGraph V` 等**数据场**，`V` 是结构里的类型场，无法对两个**不同** `V` 的
结构判等）—— 它只闭合「这条登记命题本身」。 -/
theorem rooted_tree_decidableEq_gap :
    ∀ (X : Type u) [Fintype X] [DecidableEq X],
      (∀ T T' : RootedTree.{u, u} X, Decidable (T = T')) →
      ∀ T T' : RootedTree.{u, u} X, T = T' ∨ T ≠ T' := by
  intro X _ _ h T T'
  cases h T T' with
  | isTrue hh => exact Or.inl hh
  | isFalse hh => exact Or.inr hh

/-! ## 8. ★ (W12a9) 原文 Figure 1 两棵 parent tree 的**精确** split 系统 —— 库内零件实例化

原文 113–116 行的 "precisely two trees" 需要「**精确** split 系统」的 cladogram。
库内 `Phylo/ConsensusExtra.lean` 的 `isSplitOf_iff_mem_or_trivial` 恰好给出
（W12a8 发现的 **`↔` 全刻画**，本文件因此**新增 1 行 import `Phylo.ConsensusExtra`**）：

```text
theorem isSplitOf_iff_mem_or_trivial (fam) (ρ) (hcomp) (hnt)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3) :
  ∃ M, ∀ s, M.IsSplitOf s ↔ s ∈ fam ∨ (∃ x, s.sideA = {x}) ∨ (∃ x, s.sideA = {x}ᶜ)
```

本节把 `w12a_twoparent_check.py` 机器穷举出的两个 parent 族 `P₁`、`P₂`（split 用
「不含 `0` 的一侧」编码，与该脚本的输出**逐字对应**）代入，得到两棵精确树的存在性 ✓。
「分类定理」（每个 parent tree 的 split 系统都在 `P₁ ∪ P₂` 内）仍是唯一剩余，见下方
`two_parent_trees_classification` ✓。 -/

/-- 相容性的**集合形式**：`splitOf` 的相容 ⟺ 两侧集合的 4 个 `∩ = ∅` 之一（可 `decide`）。 -/
theorem splitOf_compatible_iff {A B : Finset (Fin 6)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hB : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    (Phylo.splitOf A hA hAc).Compatible (Phylo.splitOf B hB hBc) ↔
      (A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ Aᶜ ∩ B = ∅ ∨ Aᶜ ∩ Bᶜ = ∅) := by
  rw [Split.Compatible]
  simp only [Phylo.splitOf_sideA, Phylo.splitOf_sideB, Finset.disjoint_iff_inter_eq_empty]

/-- `splitOf` 两侧的基数（集合形式）。 -/
theorem splitOf_card {A : Finset (Fin 6)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (Phylo.splitOf A hA hAc).sideA.card = A.card
      ∧ (Phylo.splitOf A hA hAc).sideB.card = Aᶜ.card := by
  rw [Phylo.splitOf_sideA, Phylo.splitOf_sideB]
  exact ⟨rfl, rfl⟩

/-- `swap` 不改相容性（右侧）。 -/
theorem compatible_swap_iff {s t : Split (Fin 6)} : s.Compatible t ↔ s.Compatible t.swap := by
  rw [Split.Compatible, Split.Compatible]
  simp only [Finset.disjoint_iff_inter_eq_empty, Split.swap_sideA, Split.swap_sideB]
  tauto

/-- `swap` 不改相容性（左侧）。 -/
theorem compatible_swap_left_iff {s t : Split (Fin 6)} :
    s.Compatible t ↔ s.swap.Compatible t := by
  rw [Split.Compatible, Split.Compatible]
  simp only [Finset.disjoint_iff_inter_eq_empty, Split.swap_sideA, Split.swap_sideB]
  tauto

/-! ### 8.1 `P₁`（机器穷举的 `P1`：`{0,1}|rest`、`{0,1,2,3}|{4,5}`、`{0,1,4,5}|{2,3}`） -/

noncomputable abbrev sP1a : Split (Fin 6) :=
  Phylo.splitOf ({2, 3, 4, 5} : Finset (Fin 6)) (by decide) (by decide)
noncomputable abbrev sP1b : Split (Fin 6) :=
  Phylo.splitOf ({4, 5} : Finset (Fin 6)) (by decide) (by decide)
noncomputable abbrev sP1c : Split (Fin 6) :=
  Phylo.splitOf ({2, 3} : Finset (Fin 6)) (by decide) (by decide)

noncomputable abbrev baseP1 : Finset (Split (Fin 6)) := {sP1a, sP1b, sP1c}

/-- `P₁` 补上换向（`hswap` 前提）。 -/
noncomputable abbrev famP1 : Finset (Split (Fin 6)) := baseP1 ∪ baseP1.image (fun s => s.swap)

theorem baseP1_compatible : ∀ s ∈ baseP1, ∀ t ∈ baseP1, s.Compatible t := by
  intro s hs t ht
  simp only [baseP1, Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    (rw [splitOf_compatible_iff]; decide)

theorem baseP1_nontrivial : ∀ s ∈ baseP1, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  simp only [baseP1, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;>
    (simp only [Phylo.splitOf_sideA, Phylo.splitOf_sideB]; decide)

theorem famP1_swap_closed : ∀ s ∈ famP1, s.swap ∈ famP1 := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨s, h, rfl⟩))
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    rw [Split.swap_swap]
    exact Finset.mem_union.mpr (Or.inl ht)

theorem famP1_compatible : ∀ s ∈ famP1, ∀ t ∈ famP1, s.Compatible t := by
  intro s hs t ht
  rcases Finset.mem_union.mp hs with h1 | h1 <;> rcases Finset.mem_union.mp ht with h2 | h2
  · exact baseP1_compatible s h1 t h2
  · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact compatible_swap_iff.mpr (baseP1_compatible s h1 t' ht')
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    exact compatible_swap_left_iff.mpr (baseP1_compatible s' hs' t h2)
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact compatible_swap_iff.mpr
      (compatible_swap_left_iff.mpr (baseP1_compatible s' hs' t' ht'))

theorem famP1_nontrivial : ∀ s ∈ famP1, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact baseP1_nontrivial s h
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := baseP1_nontrivial t ht
    rw [Split.swap_sideA, Split.swap_sideB]
    exact ⟨h2, h1⟩

/-- ★★★ **`P₁` 的精确树**：其 split 系统恰为 `famP1`（＋平凡 split）。 -/
theorem exists_exact_tree_P1 :
    ∃ M : Cladogram.{0, 0} (Fin 6), ∀ s : Split (Fin 6),
      M.IsSplitOf s ↔
        s ∈ famP1 ∨ (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ) :=
  isSplitOf_iff_mem_or_trivial famP1 0 famP1_compatible famP1_nontrivial famP1_swap_closed
    (by decide)

/-! ### 8.2 `P₂`（机器穷举的 `P2` = `σ(P₁)`：`{0,1,2,5}|{3,4}`、`{0,3,4,5}|{1,2}`、`{0,5}|rest`） -/

noncomputable abbrev sP2a : Split (Fin 6) :=
  Phylo.splitOf ({3, 4} : Finset (Fin 6)) (by decide) (by decide)
noncomputable abbrev sP2b : Split (Fin 6) :=
  Phylo.splitOf ({1, 2} : Finset (Fin 6)) (by decide) (by decide)
noncomputable abbrev sP2c : Split (Fin 6) :=
  Phylo.splitOf ({1, 2, 3, 4} : Finset (Fin 6)) (by decide) (by decide)

noncomputable abbrev baseP2 : Finset (Split (Fin 6)) := {sP2a, sP2b, sP2c}

/-- `P₂` 补上换向（`hswap` 前提）。 -/
noncomputable abbrev famP2 : Finset (Split (Fin 6)) := baseP2 ∪ baseP2.image (fun s => s.swap)

theorem baseP2_compatible : ∀ s ∈ baseP2, ∀ t ∈ baseP2, s.Compatible t := by
  intro s hs t ht
  simp only [baseP2, Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    (rw [splitOf_compatible_iff]; decide)

theorem baseP2_nontrivial : ∀ s ∈ baseP2, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  simp only [baseP2, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;>
    (simp only [Phylo.splitOf_sideA, Phylo.splitOf_sideB]; decide)

theorem famP2_swap_closed : ∀ s ∈ famP2, s.swap ∈ famP2 := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨s, h, rfl⟩))
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    rw [Split.swap_swap]
    exact Finset.mem_union.mpr (Or.inl ht)

theorem famP2_compatible : ∀ s ∈ famP2, ∀ t ∈ famP2, s.Compatible t := by
  intro s hs t ht
  rcases Finset.mem_union.mp hs with h1 | h1 <;> rcases Finset.mem_union.mp ht with h2 | h2
  · exact baseP2_compatible s h1 t h2
  · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact compatible_swap_iff.mpr (baseP2_compatible s h1 t' ht')
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    exact compatible_swap_left_iff.mpr (baseP2_compatible s' hs' t h2)
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact compatible_swap_iff.mpr
      (compatible_swap_left_iff.mpr (baseP2_compatible s' hs' t' ht'))

theorem famP2_nontrivial : ∀ s ∈ famP2, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact baseP2_nontrivial s h
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := baseP2_nontrivial t ht
    rw [Split.swap_sideA, Split.swap_sideB]
    exact ⟨h2, h1⟩

/-- ★★★ **`P₂` 的精确树**：其 split 系统恰为 `famP2`（＋平凡 split）。 -/
theorem exists_exact_tree_P2 :
    ∃ M : Cladogram.{0, 0} (Fin 6), ∀ s : Split (Fin 6),
      M.IsSplitOf s ↔
        s ∈ famP2 ∨ (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ) :=
  isSplitOf_iff_mem_or_trivial famP2 0 famP2_compatible famP2_nontrivial famP2_swap_closed
    (by decide)

/-- ⬜ **余下的唯一缺口（显式登记为 `Prop`）—— 分类定理**：
每个展示三条输入 quartet 的 `Cladogram (Fin 6)`，其每条 split 要么平凡，要么落在
`P₁`/`P₂` 的 split 系统内（无序意义；`famP1`/`famP2` 已含两个方向）。

机器见证：`scripts/msc/w12a_twoparent_check.py` 穷举 6 taxa 上**全部 236** 个两两相容族，
展示 `prof` 的族**恰有两个** = `P₁`、`P₂` ✓（与原文 "precisely two" 一致），
并对每条族做了**显式树构造**核验（`V=10, E=9`、内部点度 ≥ 3、叶度 1 ✓）。

### ★D（W12a12）**真值：机器判定为真** ✓ —— 但两条 Lean 路线都实测被挡住 ✗

该脚本 **★D-2 段**（W12a12 新增）把本 `Prop` 的「非平凡部分」在**全部 236 个相容族**上重跑：
**含 `P₁∪P₂` 之外 split 的展示族 = 0 个** ✓ ⇒ 分类定理**真** ✓
（附核：两个 parent 族规模均为 `3 = n-3` ✓）。

**Lean 侧实测结论（★D 精神：先做最小实验判定路线）**：
1. **`Finset (Fin 6)` 直写**（前一版已试）—— ❌ 综合不出可计算 `Fintype`/`Decidable`；
2. **`Fin 64` 位掩码 ＋ `decide`（`64³ = 262144` 例）—— ❌ 实测不可行**：
   * 默认 `maxRecDepth` 下报 `maximum recursion depth has been reached` ✗；
   * 提到 `maxRecDepth 200000` 后，在**玩具判据**（`a+b+c < 3 → a+b+c < 300`）上
     即 `(deterministic) timeout at whnf, maximum number of heartbeats (200000)`（约 40 s）✗；
     真实判据还含「相容性 ＋ 三条 quartet 展示」的集合运算，远重于玩具 ⇒ 该路线**实质作废** ✗。
3. **手写原文 Figure 1 情形分析** —— 未做（估计 100–200 行）✗；
4. **尚未尝试（推荐下一轮）**：在 Lean 内写**带相容性剪枝的 `Bool` 枚举**
   （剪枝后只有 **236** 个族 ✓，与 Python 脚本同规模 ⇒ 计算量微不足道 ✓），
   再补一条**反射引理**（「枚举返回 `true`」⟹ 分类定理）—— 反射引理是本路线的主要工作量 ✗。

⇒ 有了本 `Prop` ＋ §8.4 的 `two_parent_trees_conjuncts_1_2_3`（缺口第 1–3 条**已证** ✓），
`two_parent_trees_gap` 的 `…_proof` 只剩**把两者拼起来**（原 `def` 逐字保留 ✓、新名如实 ✓）。 -/
def two_parent_trees_classification : Prop :=
  ∀ T : Cladogram.{0, 0} (Fin 6), (∀ q ∈ prof, DisplaysQP T q) →
    ∀ s : Split (Fin 6), T.IsSplitOf s →
      s ∈ famP1 ∨ s ∈ famP2 ∨
        (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ)

/-! ### 8.3 (W12a10) `σ` 在两个 parent 族上的作用 —— **闭式** `Finset` 等式

缺口第 3 条（`σ` 互换两棵树）在 split 系统层就是 `famP2 = famP1.image (Split.relabel sig)`。
本节把它连同「6 条显式 split 上的**求值**」与「`relabel` 沿**对合**的双向性」一并证掉：
四条都是**闭式**（无自由尾随 `∀ s`）陈述，故 `decide` 直接可判 ✓
（这正是 W12a8 起就点名的捷径）。 -/

/-- `sig = (1 5)(2 4)` 是对合。 -/
theorem sig_involutive : Function.Involutive (⇑sig) := by
  intro x
  fin_cases x <;> decide

/-- `σ` 把 `P₁` 的三条 split 分别送到 `P₂` 的三条上（**求值**）。 -/
theorem relabel_sig_sP1a : Split.relabel sig sP1a = sP2c := by decide

theorem relabel_sig_sP1b : Split.relabel sig sP1b = sP2b := by decide

theorem relabel_sig_sP1c : Split.relabel sig sP1c = sP2a := by decide

/-- ★★★ **闭式族等式（第 3 条的 split 系统层内容）**：`σ(P₁) = P₂`。 -/
theorem famP2_eq_famP1_image_relabel : famP2 = famP1.image (Split.relabel sig) := by decide

/-- `relabel` 沿**对合**的双向性（通用形式，供把 `∈ famP1` 与 `∈ famP2` 来回搬运）。 -/
theorem relabel_relabel {α : Type*} [Fintype α] [DecidableEq α] (e : Equiv.Perm α)
    (he : Function.Involutive (⇑e)) (s : Split α) :
    Split.relabel e (Split.relabel e s) = s := by
  apply Split.ext_sideA
  rw [Split.relabel_sideA, Split.relabel_sideA, Finset.image_image]
  rw [show (⇑(Equiv.toEmbedding e) ∘ ⇑(Equiv.toEmbedding e)) = id by
    rw [Equiv.coe_toEmbedding]
    exact funext fun x => he x]
  simp

/-! ### 8.4 (W12a11) 缺口第 1–3 条**已证** ✓

用 §8.3 的闭式族等式 ＋ §8.2 的 `↔` 刻画，把「`σ` 互换两棵树」与「两棵树都展示三条
输入 quartet」一并证掉。此后 `two_parent_trees_gap` 只剩**第 4 条**
（= 下方 `two_parent_trees_classification`，未证 ⬜）✓。 -/

/-- ① `s ∈ famP2 ↔ relabel sig s ∈ famP1`（族等式 ＋ 对合）。 -/
theorem mem_famP2_iff_relabel_mem_famP1 (s : Split (Fin 6)) :
    s ∈ famP2 ↔ Split.relabel sig s ∈ famP1 := by
  rw [famP2_eq_famP1_image_relabel, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [relabel_relabel sig sig_involutive t]
    exact ht
  · intro h
    exact ⟨Split.relabel sig s, h, relabel_relabel sig sig_involutive s⟩

/-- ②（`sideA`）`relabel` 把单点侧映到单点侧。 -/
theorem relabel_sideA_singleton_iff {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (s : Split α) (x : α) :
    (Split.relabel e s).sideA = {x} ↔ s.sideA = {e.symm x} := by
  rw [Split.relabel_sideA]
  constructor
  · intro h
    have h2 := congrArg (Finset.image (Equiv.toEmbedding e.symm)) h
    rw [Finset.image_image, Finset.image_singleton] at h2
    rw [show (⇑(Equiv.toEmbedding e.symm) ∘ ⇑(Equiv.toEmbedding e)) = id by
      rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding]
      exact funext fun y => e.symm_apply_apply y] at h2
    simpa using h2
  · intro h
    rw [h, Finset.image_singleton]
    simp

/-- ②（`sideB`）。 -/
theorem relabel_sideB_singleton_iff {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (s : Split α) (x : α) :
    (Split.relabel e s).sideB = {x} ↔ s.sideB = {e.symm x} := by
  rw [Split.relabel_sideB]
  constructor
  · intro h
    have h2 := congrArg (Finset.image (Equiv.toEmbedding e.symm)) h
    rw [Finset.image_image, Finset.image_singleton] at h2
    rw [show (⇑(Equiv.toEmbedding e.symm) ∘ ⇑(Equiv.toEmbedding e)) = id by
      rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding]
      exact funext fun y => e.symm_apply_apply y] at h2
    simpa using h2
  · intro h
    rw [h, Finset.image_singleton]
    simp

/-- ②（补侧版，与 `sideAᶜ` 直接对话）。 -/
theorem relabel_compl_singleton_iff {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (s : Split α) (x : α) :
    (Split.relabel e s).sideAᶜ = {x} ↔ s.sideAᶜ = {e.symm x} := by
  rw [← Split.sideB_eq_compl (Split.relabel e s), ← Split.sideB_eq_compl s]
  exact relabel_sideB_singleton_iff e s x

/-- ②′ 「平凡」判定在 `relabel` 下不变（`{x}` 与 `{x}ᶜ` 两形态合并）。 -/
theorem trivial_relabel_iff {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (s : Split α) :
    ((∃ x, s.sideA = {x}) ∨ (∃ x, s.sideA = {x}ᶜ)) ↔
      ((∃ x, (Split.relabel e s).sideA = {x}) ∨
        (∃ x, (Split.relabel e s).sideA = {x}ᶜ)) := by
  have hA := relabel_sideA_singleton_iff e s
  have hB := relabel_compl_singleton_iff e s
  have key : ∀ t : Split α, ((∃ x, t.sideA = {x}) ∨ (∃ x, t.sideA = {x}ᶜ)) ↔
      ((∃ x, t.sideA = {x}) ∨ (∃ x, t.sideAᶜ = {x})) := by
    intro t
    constructor
    · rintro (h | ⟨x, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, by rw [hx, compl_compl]⟩
    · rintro (h | ⟨x, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, by rw [← hx, compl_compl]⟩
  rw [key s, key (Split.relabel e s)]
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨e x, (hA (e x)).mpr (by rw [Equiv.symm_apply_apply]; exact hx)⟩
    · exact Or.inr ⟨e x, (hB (e x)).mpr (by rw [Equiv.symm_apply_apply]; exact hx)⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact Or.inl ⟨e.symm y, (hA y).mp hy⟩
    · exact Or.inr ⟨e.symm y, (hB y).mp hy⟩

/-- ★★★★ **缺口第 1–3 条已证**：存在两棵树 `T₁`、`T₂`，都展示三条输入 quartet，
且 `T₂` 的 split 系统是 `T₁` 的在 `σ` 下的像（逐 split 的 `↔`）。

（第 4 条 —— 「任何 parent tree 的 split 系统都在 `T₁`/`T₂` 的之内」—— 仍未证，
见 `two_parent_trees_classification`。） -/
theorem two_parent_trees_conjuncts_1_2_3 :
    ∃ T₁ T₂ : Cladogram.{0, 0} (Fin 6),
      (∀ q ∈ prof, DisplaysQP T₁ q) ∧ (∀ q ∈ prof, DisplaysQP T₂ q) ∧
      (∀ s : Split (Fin 6), T₂.IsSplitOf s ↔ T₁.IsSplitOf (Split.relabel sig s)) := by
  obtain ⟨T₁, hT₁⟩ := exists_exact_tree_P1
  obtain ⟨T₂, hT₂⟩ := exists_exact_tree_P2
  have h1a : T₁.IsSplitOf sP1a := (hT₁ sP1a).mpr (Or.inl (by simp))
  have h1b : T₁.IsSplitOf sP1b := (hT₁ sP1b).mpr (Or.inl (by simp))
  have h1c : T₁.IsSplitOf sP1c := (hT₁ sP1c).mpr (Or.inl (by simp))
  have h2a : T₂.IsSplitOf sP2a := (hT₂ sP2a).mpr (Or.inl (by simp))
  have h2b : T₂.IsSplitOf sP2b := (hT₂ sP2b).mpr (Or.inl (by simp))
  have h2c : T₂.IsSplitOf sP2c := (hT₂ sP2c).mpr (Or.inl (by simp))
  refine ⟨T₁, T₂, ?_, ?_, fun s => ?_⟩
  · intro q hq
    simp only [prof, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨sP1a, h1a, ⟨{3, 4}, by decide, by decide⟩, ⟨{0, 1}, by decide, by decide⟩⟩
    · exact ⟨sP1c, h1c, ⟨{2, 3}, by decide, by decide⟩, ⟨{0, 5}, by decide, by decide⟩⟩
    · exact ⟨sP1b, h1b, ⟨{4, 5}, by decide, by decide⟩, ⟨{1, 2}, by decide, by decide⟩⟩
  · intro q hq
    simp only [prof, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨sP2a, h2a, ⟨{3, 4}, by decide, by decide⟩, ⟨{0, 1}, by decide, by decide⟩⟩
    · exact ⟨sP2c, h2c, ⟨{2, 3}, by decide, by decide⟩, ⟨{0, 5}, by decide, by decide⟩⟩
    · exact ⟨sP2b, h2b, ⟨{1, 2}, by decide, by decide⟩, ⟨{4, 5}, by decide, by decide⟩⟩
  · rw [hT₂ s, hT₁ (Split.relabel sig s), mem_famP2_iff_relabel_mem_famP1 s]
    exact or_congr Iff.rfl (trivial_relabel_iff sig s)

/-! ### 8.5 (W12a13) 树层分类定理 **归约到有限核心**

把第 4 条（树层分类）归约成一个**纯有限**的 `Prop`（`two_parent_trees_core`）：
树 `T` 的**非平凡** split 族自动是「两两相容 ＋ 非平凡 ＋ 展示 `prof`」的族
（相容性来自库内 `Phylo.pairwiseCompatible` ✓；展示的见证 split 必非平凡 ✓ ——
因为 quartet 的每个配对都是 2 元集 ✓），于是「有限核心」直接给出分类定理 ✓。 -/

/-- ⬜ **有限核心（尚未证）**：6 taxa 上任何**两两相容、非平凡、且展示 `prof`** 的 split 族，
其成员都落在 `P₁ ∪ P₂` 内。这是分类定理的全部有限内容（机器判定为**真** ✓，见 §8.2 末）。 -/
def two_parent_trees_core : Prop :=
  ∀ F : Finset (Split (Fin 6)),
    (∀ s ∈ F, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) →
    (∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t) →
    (∀ q ∈ prof, ∃ s ∈ F, (∃ p ∈ q, p ⊆ s.sideA) ∧ (∃ p' ∈ q, p' ⊆ s.sideB)) →
    ∀ s ∈ F, s ∈ famP1 ∨ s ∈ famP2

/-! **W12a14**：桥已补上 ✓。上一轮卡住的那一行，真因是**库内引理的真实形态**：
读 `Phylo/Split.lean` 的 namespace 块 ＋ `#check` 确认，全名是**根级** `pairwiseCompatible`
（`Cladogram.pairwiseCompatible` 与 `Split.pairwiseCompatible` **都不存在** ✗），
其结论 `T.PairwiseCompatible` 是一个 **`def`**（`= ∀ s ∈ T.splits, ∀ t ∈ T.splits, Split.Compatible s t`）
⇒ **不能直接把它当函数应用** ✗；用**显式类型归属**让 elaborate 在正确类型上展开即可 ✓。 -/

/-- ★★★ **桥：有限核心 ⟹ 分类定理**（缺口第 4 条的树层形态）。

树 `T` 的非平凡 split 族 `F` 自动满足核心的三条前提：非平凡（构造）、两两相容
（`pairwiseCompatible T`）、展示 `prof`（`DisplaysQP` 的见证 split 必非平凡 ——
因为 quartet 的每个配对都是 2 元集）。 -/
theorem two_parent_trees_classification_of_core (h : two_parent_trees_core) :
    two_parent_trees_classification := by
  classical
  intro T hT s hs
  by_cases htriv : (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ)
  · exact Or.inr (Or.inr htriv)
  · have hntA : 2 ≤ s.sideA.card := by
      have h1 : 1 ≤ s.sideA.card := Finset.card_pos.mpr (s.nonempty 0)
      rcases Nat.lt_or_ge s.sideA.card 2 with h2 | h2
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : s.sideA.card = 1)
        exact absurd (Or.inl ⟨x, hx⟩) htriv
      · exact h2
    have hntB : 2 ≤ s.sideB.card := by
      have h1 : 1 ≤ s.sideB.card := Finset.card_pos.mpr (s.nonempty 1)
      rcases Nat.lt_or_ge s.sideB.card 2 with h2 | h2
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : s.sideB.card = 1)
        refine absurd (Or.inr ⟨x, ?_⟩) htriv
        rw [← hx, Split.sideB_eq_compl, compl_compl]
      · exact h2
    set F : Finset (Split (Fin 6)) := Finset.univ.filter (fun t : Split (Fin 6) =>
      T.IsSplitOf t ∧ 2 ≤ t.sideA.card ∧ 2 ≤ t.sideB.card) with hF
    have hsF : s ∈ F := by
      rw [hF, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hs, hntA, hntB⟩
    have hF1 : ∀ a ∈ F, T.IsSplitOf a := by
      intro a ha
      rw [hF] at ha
      exact (Finset.mem_filter.mp ha).right.1
    have hF2 : ∀ a ∈ F, 2 ≤ a.sideA.card ∧ 2 ≤ a.sideB.card := by
      intro a ha
      rw [hF] at ha
      exact (Finset.mem_filter.mp ha).right.2
    have hcomp : ∀ a ∈ F, ∀ b ∈ F, Split.Compatible a b := by
      intro a ha b hb
      have ha' : a ∈ T.splits := by
        change T.IsSplitOf a
        exact hF1 a ha
      have hb' : b ∈ T.splits := by
        change T.IsSplitOf b
        exact hF1 b hb
      exact (pairwiseCompatible T :
        ∀ s ∈ T.splits, ∀ t ∈ T.splits, Split.Compatible s t) a ha' b hb'
    have hcard : ∀ (q : QTop (Fin 6)) (p : Finset (Fin 6)), q ∈ prof → p ∈ q →
        p.card = 2 := by
      intro q p hq hp
      simp only [prof, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;>
        (simp only [q1, q2, q3, Finset.mem_insert, Finset.mem_singleton] at hp
         rcases hp with rfl | rfl <;> decide)
    have hdisp : ∀ q ∈ prof, ∃ a ∈ F,
        (∃ p ∈ q, p ⊆ a.sideA) ∧ (∃ p' ∈ q, p' ⊆ a.sideB) := by
      intro q hq
      obtain ⟨a, ha, hsubA, hsubB⟩ := hT q hq
      refine ⟨a, ?_, hsubA, hsubB⟩
      rw [hF, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ha, ?_, ?_⟩
      · obtain ⟨p, hp, hpsub⟩ := hsubA
        calc 2 = p.card := (hcard q p hq hp).symm
          _ ≤ a.sideA.card := Finset.card_le_card hpsub
      · obtain ⟨p', hp', hpsub⟩ := hsubB
        calc 2 = p'.card := (hcard q p' hq hp').symm
          _ ≤ a.sideB.card := Finset.card_le_card hpsub
    rcases h F hF2 hcomp hdisp s hsF with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

/-! ### 8.6 (W12a15) 核心的前提拆解件：展示 quartet 的 split 必非平凡

`two_parent_trees_core` 的第一条前提（族成员**非平凡**）在树层是**免费**的：
quartet 的每个配对都是 2 元集，故展示它的 split 两侧各 ≥2 叶。
下面把这条从 §8.5 桥的 `hdisp` 里**抽成具名引理**（核心的证明要用它，
且「每条 quartet 的配对都是 2 元集」这一计算也因此只写一次）。 -/

/-- **展示 `prof` 中某条 quartet 的 split 必非平凡**（两侧各 ≥2 叶）。 -/
theorem two_le_card_of_displaysQP {q : QTop (Fin 6)} (hq : q ∈ prof) {s : Split (Fin 6)}
    (h : (∃ p ∈ q, p ⊆ s.sideA) ∧ (∃ p' ∈ q, p' ⊆ s.sideB)) :
    2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  have hcard : ∀ p : Finset (Fin 6), p ∈ q → p.card = 2 := by
    intro p hp
    simp only [prof, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;>
      (simp only [q1, q2, q3, Finset.mem_insert, Finset.mem_singleton] at hp
       rcases hp with rfl | rfl <;> decide)
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hps⟩ := h.1
    calc 2 = p.card := (hcard p hp).symm
      _ ≤ s.sideA.card := Finset.card_le_card hps
  · obtain ⟨p', hp', hps⟩ := h.2
    calc 2 = p'.card := (hcard p' hp').symm
      _ ≤ s.sideB.card := Finset.card_le_card hps

end SBD
