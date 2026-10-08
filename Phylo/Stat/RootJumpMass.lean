/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.Stat.KingmanJumpChain
import Phylo.Stat.KingmanLaw

/-!
# `Phylo.Stat.RootJumpMass` —— 根种群的 `1/3` **就是**跳链在拓扑类上的质量

把两个**已经各自做完**的结果在**具体对象**上接起来：

* **左半边**（MSC 侧）：`Phylo.Stat.MSCProof.rootTopoProb = 1 / 3`（`rootTopoProb_eq_third`）。
  它是**根种群**里「`0,1` 同类」这一拓扑的概率，由 `MSCKingman.root_topology_class_prob`
  在**首次合并对**上求和得到 —— W9 批评点（「`1/3` 是定义还是推导」）的正面回应。
* **右半边**（W10a / 跳链侧）：`Phylo.Stat.KingmanJumpChain.jumpWeight 4 3`
  = K82 (2.2) 给出的 **3 块层**（`PartK 4 3`）上的绝对概率 `partitionProb 4 3`。

**本文件证明两者相等**：根种群的 `1/3` 不是一次算术巧合，而是**同一个跳链律**
在「`{0,1}` 同类（等价地 `{2,3}` 同类）」这个拓扑**类**上的**总质量**。

## 证明路线（四步）

1. `jumpWeight_four_three`：`Fin 4` 的**每一个** 3 块划分权重都是 `1/6`。
   用层间一致性递归 `partitionProb_merge_recursion_div (n := 4) (k := 3)`：
   `pp(4,3,P) = Σ_{Q : |Q| = 4, MergeInto Q P} pp(4,4,Q) / C(4,2)`；
   而 `|Q| = 4 = n` 迫使 `Q = ⊥`（`eq_bot_of_card_parts`），
   故右端 = `#(过滤子) · pp(4,4,⊥) / 6 = #(过滤子) · 1/6`；
   再由 `partitionProb_pos` 知其 `> 0`，得 `#(过滤子) = 1`（`card_mergeFilter_four_three`）。
2. `parts_eq_of_mem_pair`：`Fin 4` 的 3 块划分若含二元块 `{a,b}`
   （且 `{a,b,c,d} = univ`），则其块集合恰为 `{{a,b},{c},{d}}`。
3. `topoClass_eq` / `topoClass_card`：拓扑类恰由**两个**划分组成 ——
   `P01 = {{0,1},{2},{3}}` 与 `P23 = {{2,3},{0},{1}}`。
   （`P01` / `P23` 用 `Finpartition.ofExistsUnique` 显式构造，**不是**假设。）
4. 合并：`Σ_{P ∈ 类} jumpWeight 4 3 P = 2 · (1/6) = 1/3 = rootTopoProb`
   （`jumpMass_class_eq_third` + `rootTopoProb_eq_third`）。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| ★★★ **主目标** `rootTopoProb_eq_jumpMass`（**等式**） | ✅ **已达成**（不是降级版）：两侧都是具体对象；全文零占位证明、零新公理（`#print` 公理检查只报 `propext, Classical.choice, Quot.sound`） |
| ★★★ `jumpMass_class_eq_third`（跳链在拓扑类上的质量 `= 1/3`） | ✅ **已证**（可独立引用） |
| 「每个 3 块划分权重 `= 1/6`」 | ✅ **已证**（`jumpWeight_four_three`；走层间递归，**没有**用枚举） |
| 「拓扑类恰有 2 个元素」 | ✅ **已证**（`topoClass_card`；逐元素刻画，**没有**用 `Finset.univ : Finset (PartK 4 3)` 的枚举 —— 该 `Fintype` 实例在 `decide` 下会触发 `maximum recursion depth`，实测） |
| 「跳链**测度** `jumpMeasure 4 3` 在该类上的质量」 | ✅ **已证**（`jumpMeasure_topoClass`：`jumpMeasure 4 3 ↑topoClass = ofReal (1/3)`，接上了 `KingmanLaw.jumpMeasure`） |
| 整条跳链 `(S_4, S_3, S_2, S_1)` 的轨迹律 | ❌ **未做**（同 `KingmanLaw` 的诚实边界，本文件只碰 `k = 3` 这一层） |
-/

noncomputable section

namespace Phylo.Stat.RootJumpMass

open Phylo.Stat.KingmanJumpChain
open Phylo.Stat.KingmanLaw (jumpMeasure jumpMeasure_apply)
open Phylo.Stat.MSCProof (rootTopoProb rootTopoProb_eq_third)

/-! ## 0. 拓扑类与小算术 -/

/-- ★ 跳链第 `3` 层（`Fin 4` 上的 3 块划分）上「`0,1` 同类」这一**拓扑类**。
（在这个层上「`0,1` 同类」⟺「`2,3` 同类」，因为恰有一个二元块。） -/
abbrev topoClass : Finset (PartK 4 3) :=
  Finset.univ.filter (fun P : PartK 4 3 =>
    ({0, 1} : Finset (Fin 4)) ∈ P.1.parts
      ∨ ({2, 3} : Finset (Fin 4)) ∈ P.1.parts)

/-- `((3 + 1).choose 2 : ℕ) = 6`。（单独提出来，避免在被 `Classical` 实例化的
`Decidable` 环境里使用 `decide`。） -/
theorem choose_three_succ_two : ((3 + 1).choose 2 : ℕ) = 6 := by decide

/-- `({0, 1, 2, 3} : Finset (Fin 4))` 就是全集。 -/
theorem four_univ : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ := by decide

/-! ## 1. 每个 3 块划分的权重都是 `1/6`

`MergeInto` 上没有可计算的 `Decidable` 实例（它是带依赖证明的存在量词），
故 `Finset.univ.filter … ∧ MergeInto …` 的 `DecidablePred` 只能由 `Classical.decPred` 给出
（`Phylo/Stat/KingmanJumpChain.lean` 的 `section Consistency` 也是这么做的）。
本节因此显式 `open Classical`，与那边实例一致；本节内**不使用** `decide`。 -/

open Classical in
/-- 层间递归（`n = 4, k = 3`）的过滤子恰含**一个**元素：`|Q| = 4 = n` 迫使 `Q = ⊥`。 -/
theorem card_mergeFilter_four_three (P : Part 4) (hP : P.parts.card = 3) :
    (Finset.univ.filter (fun Q : Part 4 => Q.parts.card = 3 + 1 ∧ MergeInto Q P)).card = 1 := by
  set s : Finset (Part 4) :=
    Finset.univ.filter (fun Q : Part 4 => Q.parts.card = 3 + 1 ∧ MergeInto Q P) with hs
  have hsub : s ⊆ ({⊥} : Finset (Part 4)) := by
    intro Q hQ
    rw [hs] at hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    rw [Finset.mem_singleton]
    exact eq_bot_of_card_parts (n := 4) Q (by omega)
  have hle : s.card ≤ 1 := by
    calc s.card ≤ ({⊥} : Finset (Part 4)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton ⊥
  have hone : ∀ Q ∈ s, partitionProb 4 4 Q / (((3 + 1).choose 2 : ℕ) : ℝ) = 1 / 6 := by
    intro Q hQ
    rw [hs] at hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    have hQ4 : Q.parts.card = 4 := by omega
    rw [eq_bot_of_card_parts (n := 4) Q hQ4, partitionProb_self_bot, choose_three_succ_two]
    norm_num
  have hrec := partitionProb_merge_recursion_div (n := 4) (k := 3) (by norm_num) (by norm_num) P hP
  have hrec' : partitionProb 4 3 P
      = ∑ Q ∈ s, partitionProb 4 4 Q / (((3 + 1).choose 2 : ℕ) : ℝ) := by
    rw [hrec, ← hs]
  have hpos : 0 < partitionProb 4 3 P := partitionProb_pos 4 3 P
  rw [hrec', Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul] at hpos
  have hne : s.card ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hcard : s.card = 1 := by omega
  exact hcard

open Classical in
/-- ★★★ **3 块层上每个划分的权重都是 `1/6`**：`Fin 4` 的 3 块划分恰有 `6` 个，
且 K82 (2.2) 在这一层是均匀的。（用层间递归 + 归一化，不用枚举。） -/
theorem jumpWeight_four_three (P : PartK 4 3) : jumpWeight 4 3 P = 1 / 6 := by
  have hrec := partitionProb_merge_recursion_div (n := 4) (k := 3) (by norm_num) (by norm_num) P.1 P.2
  have hone : ∀ Q ∈ (Finset.univ.filter (fun Q : Part 4 => Q.parts.card = 3 + 1 ∧ MergeInto Q P.1)),
      partitionProb 4 4 Q / (((3 + 1).choose 2 : ℕ) : ℝ) = 1 / 6 := by
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    have hQ4 : Q.parts.card = 4 := by omega
    rw [eq_bot_of_card_parts (n := 4) Q hQ4, partitionProb_self_bot, choose_three_succ_two]
    norm_num
  have hcard := card_mergeFilter_four_three P.1 P.2
  show partitionProb 4 3 P.1 = 1 / 6
  rw [hrec, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, hcard]
  norm_num

/-! ## 2. `Fin 4` 的 3 块划分的形状 -/

/-- ★★ **形状引理**：`Fin 4` 的 3 块划分若含二元块 `{a,b}`
（且 `{a,b,c,d}` 是全集），则其块集合**恰**为 `{{a,b},{c},{d}}`。

证明：`Σ_B |B| = 4`、`|{a,b}| = 2`，故剩下两块（`erase {a,b}` 后恰剩 `2` 块）之和为 `2`；
两块都非空，故都是单点；它们与 `{a,b}` 不交，故只能是 `{c}`、`{d}`。 -/
theorem parts_eq_of_mem_pair {a b c d : Fin 4}
    (hperm : ({a, b, c, d} : Finset (Fin 4)) = Finset.univ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (P : Part 4) (hcard : P.parts.card = 3) (h : ({a, b} : Finset (Fin 4)) ∈ P.parts) :
    P.parts = ({({a, b} : Finset (Fin 4)), {c}, {d}} : Finset (Finset (Fin 4))) := by
  have hsum : ∑ B ∈ P.parts, B.card = 4 := by simpa using P.sum_card_parts
  have herase_sum : ∑ B ∈ P.parts.erase ({a, b} : Finset (Fin 4)), B.card = 2 := by
    have hsplit := Finset.add_sum_erase (s := P.parts)
      (f := fun B : Finset (Fin 4) => B.card) h
    rw [hsum, Finset.card_pair hab] at hsplit
    omega
  have herase_card : (P.parts.erase ({a, b} : Finset (Fin 4))).card = 2 := by
    have h1 := Finset.card_erase_add_one h
    omega
  have hcard_one : ∀ B ∈ P.parts.erase ({a, b} : Finset (Fin 4)), B.card = 1 := by
    have hle : ∀ B ∈ P.parts.erase ({a, b} : Finset (Fin 4)), (1 : ℕ) ≤ B.card :=
      fun B hB => Finset.card_pos.mpr (P.nonempty_of_mem_parts (Finset.mem_of_mem_erase hB))
    have hsum1 : ∑ B ∈ P.parts.erase ({a, b} : Finset (Fin 4)), (1 : ℕ)
        = ∑ B ∈ P.parts.erase ({a, b} : Finset (Fin 4)), B.card := by
      rw [Finset.sum_const, herase_card, smul_eq_mul, mul_one, herase_sum]
    intro B hB
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum1 B hB).symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro B hB
    by_cases hBeq : B = ({a, b} : Finset (Fin 4))
    · rw [hBeq]
      exact Finset.mem_insert_self _ _
    · have hBe : B ∈ P.parts.erase ({a, b} : Finset (Fin 4)) := Finset.mem_erase.mpr ⟨hBeq, hB⟩
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hcard_one B hBe)
      have hxa : x ≠ a := by
        intro hxa'
        exact hBeq (P.eq_of_mem_parts hB h
          (show x ∈ ({x} : Finset (Fin 4)) by simp)
          (show x ∈ ({a, b} : Finset (Fin 4)) by simp [hxa']))
      have hxb : x ≠ b := by
        intro hxb'
        exact hBeq (P.eq_of_mem_parts hB h
          (show x ∈ ({x} : Finset (Fin 4)) by simp)
          (show x ∈ ({a, b} : Finset (Fin 4)) by simp [hxb']))
      have hx : x ∈ ({a, b, c, d} : Finset (Fin 4)) := by
        rw [hperm]
        exact Finset.mem_univ x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact absurd rfl hxa
      · exact absurd rfl hxb
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · rw [hcard]
    have h2 : (({({a, b} : Finset (Fin 4)), {c}, {d}} : Finset (Finset (Fin 4)))).card
        ≤ (({({c} : Finset (Fin 4)), {d}} : Finset (Finset (Fin 4)))).card + 1 :=
      Finset.card_insert_le _ _
    have h3 : (({({c} : Finset (Fin 4)), {d}} : Finset (Finset (Fin 4)))).card ≤ 2 :=
      Finset.card_le_two
    calc (({({a, b} : Finset (Fin 4)), {c}, {d}} : Finset (Finset (Fin 4)))).card
        ≤ (({({c} : Finset (Fin 4)), {d}} : Finset (Finset (Fin 4)))).card + 1 := h2
      _ ≤ 2 + 1 := Nat.add_le_add_right h3 1
      _ = 3 := by norm_num

/-! ## 3. 拓扑类的两个元素（**显式构造**，不是假设） -/

/-- ★ 划分 `{{0,1},{2},{3}}`（含二元块 `{0,1}`）。 -/
def P01 : PartK 4 3 :=
  ⟨Finpartition.ofExistsUnique ({({0, 1} : Finset (Fin 4)), {2}, {3}} : Finset (Finset (Fin 4)))
      (fun p _ => Finset.subset_univ p)
      (by
        intro a _
        have ha : a ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
          rw [four_univ]
          exact Finset.mem_univ a
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact ⟨{0, 1}, by decide, by decide⟩
        · exact ⟨{0, 1}, by decide, by decide⟩
        · exact ⟨{2}, by decide, by decide⟩
        · exact ⟨{3}, by decide, by decide⟩)
      (by decide),
    by
      rw [Finpartition.ofExistsUnique_parts]
      decide⟩

/-- ★ 划分 `{{2,3},{0},{1}}`（含二元块 `{2,3}`）。 -/
def P23 : PartK 4 3 :=
  ⟨Finpartition.ofExistsUnique ({({2, 3} : Finset (Fin 4)), {0}, {1}} : Finset (Finset (Fin 4)))
      (fun p _ => Finset.subset_univ p)
      (by
        intro a _
        have ha : a ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
          rw [four_univ]
          exact Finset.mem_univ a
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact ⟨{0}, by decide, by decide⟩
        · exact ⟨{1}, by decide, by decide⟩
        · exact ⟨{2, 3}, by decide, by decide⟩
        · exact ⟨{2, 3}, by decide, by decide⟩)
      (by decide),
    by
      rw [Finpartition.ofExistsUnique_parts]
      decide⟩

theorem P01_parts :
    P01.1.parts = ({({0, 1} : Finset (Fin 4)), {2}, {3}} : Finset (Finset (Fin 4))) := by
  simp [P01, Finpartition.ofExistsUnique_parts]

theorem P23_parts :
    P23.1.parts = ({({2, 3} : Finset (Fin 4)), {0}, {1}} : Finset (Finset (Fin 4))) := by
  simp [P23, Finpartition.ofExistsUnique_parts]

/-- ★★★ **拓扑类恰由两个划分构成**：`{{0,1},{2},{3}}` 与 `{{2,3},{0},{1}}`。 -/
theorem topoClass_eq : topoClass = ({P01, P23} : Finset (PartK 4 3)) := by
  ext P
  simp only [topoClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · left
      have hparts := parts_eq_of_mem_pair (a := 0) (b := 1) (c := 2) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        P.1 P.2 h
      apply Subtype.ext
      exact Finpartition.ext (hparts.trans P01_parts.symm)
    · right
      have hparts := parts_eq_of_mem_pair (a := 2) (b := 3) (c := 0) (d := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        P.1 P.2 h
      apply Subtype.ext
      exact Finpartition.ext (hparts.trans P23_parts.symm)
  · rintro (rfl | rfl)
    · left
      rw [P01_parts]
      exact Finset.mem_insert_self _ _
    · right
      rw [P23_parts]
      exact Finset.mem_insert_self _ _

/-- ★★★ **拓扑类恰有 `2` 个元素**。 -/
theorem topoClass_card : topoClass.card = 2 := by
  rw [topoClass_eq]
  refine Finset.card_pair ?_
  intro h
  have hp : P01.1.parts = P23.1.parts := by rw [h]
  rw [P01_parts, P23_parts] at hp
  exact (by decide : ¬ (({({0, 1} : Finset (Fin 4)), {2}, {3}} : Finset (Finset (Fin 4)))
      = ({({2, 3} : Finset (Fin 4)), {0}, {1}} : Finset (Finset (Fin 4))))) hp

/-! ## 4. 收口：跳链在拓扑类上的质量 `= 1/3`，且 `= rootTopoProb` -/

/-- ★★★ **跳链在拓扑类上的总质量 `= 1/3`**（本文件的核心交付之一，可独立引用）。 -/
theorem jumpMass_class_eq_third :
    (∑ P ∈ (Finset.univ.filter (fun P : PartK 4 3 =>
        ({0, 1} : Finset (Fin 4)) ∈ P.1.parts
          ∨ ({2, 3} : Finset (Fin 4)) ∈ P.1.parts)),
      jumpWeight 4 3 P) = 1 / 3 := by
  change (∑ P ∈ topoClass, jumpWeight 4 3 P) = 1 / 3
  have h1 : (∑ P ∈ topoClass, jumpWeight 4 3 P) = ∑ P ∈ topoClass, (1 / 6 : ℝ) :=
    Finset.sum_congr rfl (fun P _ => jumpWeight_four_three P)
  rw [h1, Finset.sum_const, nsmul_eq_mul, topoClass_card]
  norm_num

/-- ★★★ **测度层**：跳链律 `jumpMeasure 4 3`（`KingmanLaw` 里由 (2.2) 的 `jumpWeight`
构造、并已证是概率测度的那个对象）在拓扑类上的**质量**就是 `1/3`。 -/
theorem jumpMeasure_topoClass :
    jumpMeasure 4 3 (↑topoClass : Set (PartK 4 3)) = ENNReal.ofReal (1 / 3) := by
  rw [jumpMeasure_apply]
  have hdirac : ∀ P : PartK 4 3,
      (MeasureTheory.Measure.dirac P : MeasureTheory.Measure (PartK 4 3))
          (↑topoClass : Set (PartK 4 3))
        = if P ∈ (↑topoClass : Set (PartK 4 3)) then 1 else 0 := by
    intro P
    by_cases h : P ∈ (↑topoClass : Set (PartK 4 3))
    · rw [MeasureTheory.Measure.dirac_apply_of_mem h]
      simp only [h, ↓reduceIte]
    · rw [MeasureTheory.Measure.dirac_apply' P
          (MeasurableSpace.measurableSet_top (α := PartK 4 3)
            (s := (↑topoClass : Set (PartK 4 3)))),
        Set.indicator_of_notMem h]
      simp only [h, ↓reduceIte]
  have hpt : ∀ P : PartK 4 3,
      ENNReal.ofReal (jumpWeight 4 3 P)
          * (MeasureTheory.Measure.dirac P : MeasureTheory.Measure (PartK 4 3))
              (↑topoClass : Set (PartK 4 3))
        = if P ∈ (↑topoClass : Set (PartK 4 3)) then ENNReal.ofReal (jumpWeight 4 3 P)
            else 0 := by
    intro P
    rw [hdirac P]
    by_cases h : P ∈ (↑topoClass : Set (PartK 4 3)) <;>
      simp only [h, ↓reduceIte, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun P _ => hpt P), ← Finset.sum_filter]
  have hfil : (Finset.univ.filter
      (fun P : PartK 4 3 => P ∈ (↑topoClass : Set (PartK 4 3)))) = topoClass := by
    ext P
    simp
  rw [hfil, ← ENNReal.ofReal_sum_of_nonneg (fun P _ => jumpWeight_nonneg 4 3 P),
    jumpMass_class_eq_third]

/-- ★★★ **主目标**：根种群的拓扑概率 `1/3` **就是**跳链在 `3` 块层的律落在一个拓扑类上的质量。

左边 `rootTopoProb` 来自 MSC 侧（根种群首次合并对的均匀权重在拓扑类上求和，
`MSCKingman.root_topology_class_prob`），右边来自 W10a 的 (2.2) 绝对概率 `jumpWeight 4 3`；
两者是**同一个跳链律**在**同一个类**上的同一个数。 -/
theorem rootTopoProb_eq_jumpMass :
    rootTopoProb
      = ∑ P ∈ (Finset.univ.filter (fun P : PartK 4 3 =>
            ({0, 1} : Finset (Fin 4)) ∈ P.1.parts
              ∨ ({2, 3} : Finset (Fin 4)) ∈ P.1.parts)),
          jumpWeight 4 3 P := by
  rw [rootTopoProb_eq_third, jumpMass_class_eq_third]

end Phylo.Stat.RootJumpMass
