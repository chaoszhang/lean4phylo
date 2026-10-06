/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Distance
import Phylo.Split

/-!
# `Phylo.Quartet` —— quartet / triplet 与它们的拓扑（M3 地基）

`CONCEPTS.md` §3.5 决策（老师原话：「quartet topology = quartet + split，quartet 就是 set」）：

**把「支撑集（set）」与「拓扑（topology）」彻底分开。**

| 对象 | 支撑集 | 拓扑 = `Split ↥S` | 分裂形状 |
|---|---|---|---|
| **quartet topology** | `S`，`|S| = 4` | `Split ↥S` | 2 \| 2 |
| **triplet topology** | `S`，`|S| = 3` | `Split ↥S` | 2 \| 1 |

两者是**同一个构造**，只是 `|S|` 与分裂形状不同 —— 故只需一个 `Topology S`。

**§3.5 要点**：
* `Split` 的底**必须参数化在任意类型**（本库已如此）—— quartet 的配对是 4 元集**内部**的二分，
  不是整个 `X` 的二分（§3.1「保留改底层空间」的第一次实战检验）；
* quartet topology **无根**，triplet topology **天然有根**（「谁是外群」需要 root）；
* 无序性：`ab|cd = cd|ab`、`ab|c = ba|c` —— 需商掉 `Split.swap`（见 `QuartetTopology.swap`）。
-/

namespace Phylo

open Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **4 元叶集** —— quartet「就是 set」，不带任何配对信息。

用 `abbrev` 而非 `def`：直接展开为子类型，从而**自动获得 `Fintype` / `DecidableEq` 实例**。 -/
abbrev Quartet (X : Type*) [Fintype X] [DecidableEq X] :=
  {S : Finset X // S.card = 4}

/-- **3 元叶集**（triplet 的支撑集）。 -/
abbrev TripletSet (X : Type*) [Fintype X] [DecidableEq X] :=
  {S : Finset X // S.card = 3}

/-- **支撑集 `S` 上的拓扑** = `S` 上的一个 2-划分。

`|S| = 4` 时是 quartet topology（2\|2），`|S| = 3` 时是 triplet topology（2\|1）
—— 同一个构造，正是 §3.5 的统一形式。 -/
abbrev Topology (S : Finset X) := Split ↥S

namespace Topology

variable {S : Finset X}

/-- 拓扑**交换两侧**（`ab|cd ↦ cd|ab`）。（须显式限定 `Split.swap`，否则递归自身。） -/
def swap (t : Topology S) : Topology S := Split.swap t

@[simp] theorem swap_swap (t : Topology S) : swap (swap t) = t := by
  cases t with
  | mk parts hd hu hn =>
    simp only [swap, Split.swap]
    congr 1
    funext i
    fin_cases i <;> rfl

end Topology

/-- **quartet topology**：4 元支撑集 + 其上的配对（2\|2 划分）。 -/
structure QuartetTopology (X : Type*) [Fintype X] [DecidableEq X] where
  /-- 支撑集（4 个叶）。 -/
  supp : Finset X
  /-- 支撑集恰有 4 元。 -/
  card_supp : supp.card = 4
  /-- 配对方式。 -/
  top : Topology supp

/-- **triplet topology**：3 元支撑集 + 其上的划分（2\|1）。 -/
structure TripletTopology (X : Type*) [Fintype X] [DecidableEq X] where
  /-- 支撑集（3 个叶）。 -/
  supp : Finset X
  /-- 支撑集恰有 3 元。 -/
  card_supp : supp.card = 3
  /-- 划分方式。 -/
  top : Topology supp

namespace Quartet

variable {S : Finset X}

/-- quartet 作为集合的成员判定。 -/
theorem mem_iff {Q : Quartet X} {x : X} : x ∈ Q.1 ↔ x ∈ (Q.1 : Finset X) := Iff.rfl

/-- quartet 恰有 4 个元素。 -/
theorem card_eq (Q : Quartet X) : Q.1.card = 4 := Q.2

/-- 非空。 -/
theorem nonempty (Q : Quartet X) : Q.1.Nonempty :=
  Finset.card_pos.mp (by rw [Q.card_eq]; norm_num)

end Quartet

namespace TripletSet

/-- triplet 支撑集恰有 3 个元素。 -/
theorem card_eq (T : TripletSet X) : T.1.card = 3 := T.2

/-- 非空。 -/
theorem nonempty (T : TripletSet X) : T.1.Nonempty :=
  Finset.card_pos.mp (by rw [T.card_eq]; norm_num)

end TripletSet

/-! ### 枚举 -/

/-- **全部 quartet**（`|X| ≥ 4` 时非空）。 -/
def allQuartets (X : Type*) [Fintype X] [DecidableEq X] : Finset (Quartet X) := Finset.univ

/-- **全部 triplet 支撑集**。 -/
def allTripletSets (X : Type*) [Fintype X] [DecidableEq X] : Finset (TripletSet X) := Finset.univ

/-- 4 元支撑集的「一簇子集」视角（`Finset.powersetCard`），用于计数。 -/
theorem univ_filter_card_eq_powersetCard :
    (Finset.univ.filter fun S : Finset X => S.card = 4) =
      (Finset.univ : Finset X).powersetCard 4 := by
  ext S
  simp [Finset.mem_powersetCard]

/-- 3 元支撑集的同款。 -/
theorem univ_filter_card3_eq_powersetCard :
    (Finset.univ.filter fun S : Finset X => S.card = 3) =
      (Finset.univ : Finset X).powersetCard 3 := by
  ext S
  simp [Finset.mem_powersetCard]

/-- **quartet 总数 = `C(|X|, 4)`**。 -/
theorem card_allQuartets : (allQuartets X).card = (Fintype.card X).choose 4 := by
  rw [allQuartets, Finset.card_univ, Fintype.card_subtype,
    univ_filter_card_eq_powersetCard, Finset.card_powersetCard, Finset.card_univ]

/-- **triplet 支撑集总数 = `C(|X|, 3)`**。 -/
theorem card_allTripletSets : (allTripletSets X).card = (Fintype.card X).choose 3 := by
  rw [allTripletSets, Finset.card_univ, Fintype.card_subtype,
    univ_filter_card3_eq_powersetCard, Finset.card_powersetCard, Finset.card_univ]

namespace QuartetTopology

/-- quartet topology 的支撑集是 4 元集（`Quartet` 视角）。 -/
def toQuartet (q : QuartetTopology X) : Quartet X := ⟨q.supp, q.card_supp⟩

/-- **交换配对**（`ab|cd ↦ cd|ab`）—— 无序性所需的商。 -/
def swap (q : QuartetTopology X) : QuartetTopology X where
  supp := q.supp
  card_supp := q.card_supp
  top := q.top.swap

@[simp] theorem swap_swap (q : QuartetTopology X) : q.swap.swap = q := by
  cases q with
  | mk supp card top =>
    simp only [swap]
    congr 1
    exact Topology.swap_swap top

end QuartetTopology

namespace TripletTopology

/-- triplet topology 的支撑集是 3 元集。 -/
def toTripletSet (t : TripletTopology X) : TripletSet X := ⟨t.supp, t.card_supp⟩

/-- 交换两侧。 -/
def swap (t : TripletTopology X) : TripletTopology X where
  supp := t.supp
  card_supp := t.card_supp
  top := t.top.swap

@[simp] theorem swap_swap (t : TripletTopology X) : t.swap.swap = t := by
  cases t with
  | mk supp card top =>
    simp only [swap]
    congr 1
    exact Topology.swap_swap top

end TripletTopology

end Phylo

open Phylo

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## display —— 树展示 quartet / quartet 拓扑

`CONCEPTS.md` §3.5 / §3.11：**「存在 cladogram 显示 Q 中所有 quartet」= Quartet Compatibility**
（一般情形 NP-complete，故**只作存在性命题 / 算法目标，不作判据**）。 -/

namespace Cladogram

variable (T : Cladogram X)

/-- 树 `T` **展示** quartet `ab|cd`：存在一条边（split）把 `{a,b}` 与 `{c,d}` 分到两侧。 -/
def DisplaysQuartet (a b c d : X) : Prop :=
  ∃ s : Split X, T.IsSplitOf s ∧ ({a, b} : Finset X) ⊆ s.sideA ∧ ({c, d} : Finset X) ⊆ s.sideB

/-- 展示性对第一侧内部次序不变（`ab|cd ⟺ ba|cd`）。 -/
theorem displaysQuartet_comm_ab (a b c d : X) :
    T.DisplaysQuartet a b c d ↔ T.DisplaysQuartet b a c d := by
  have h : ({a, b} : Finset X) = {b, a} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold DisplaysQuartet
  rw [h]

/-- 展示性对两侧交换不变（`ab|cd ⟺ cd|ab`）—— 用 `isSplitOf_swap` 换到边另一端。 -/
theorem displaysQuartet_comm_cd (a b c d : X) :
    T.DisplaysQuartet a b c d ↔ T.DisplaysQuartet c d a b := by
  unfold DisplaysQuartet
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨s.swap, T.isSplitOf_swap hs,
      by rw [Split.swap_sideA]; exact h2,
      by rw [Split.swap_sideB]; exact h1⟩
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨s.swap, T.isSplitOf_swap hs,
      by rw [Split.swap_sideA]; exact h2,
      by rw [Split.swap_sideB]; exact h1⟩

/-- **展示 ⟹ 该 split 在 4 元支撑集上恰给出 `{a,b}|{c,d}`**（§3.5 的「quartet + split」桥）。 -/
theorem exists_split_inter_of_displaysQuartet {a b c d : X}
    (h : T.DisplaysQuartet a b c d) :
    ∃ s : Split X, T.IsSplitOf s ∧ s.sideA ∩ ({a, b, c, d} : Finset X) = {a, b} := by
  obtain ⟨s, hs, h1, h2⟩ := h
  refine ⟨s, hs, Finset.Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hxA, hxQ⟩ := hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hxQ
    rcases hxQ with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (h2 (by simp)) fun h' => (Finset.disjoint_left.mp s.disjoint_sides) hxA h'
    · exact absurd (h2 (by simp)) fun h' => (Finset.disjoint_left.mp s.disjoint_sides) hxA h'
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact h1 (by rw [Finset.mem_insert, Finset.mem_singleton]; exact hx)
    · rcases hx with hxa | hxb
      · rw [hxa]; simp
      · rw [hxb]; simp

/-- ★ **Colonius–Schultze 推理规则**：`ab|ce ∧ ab|de ⟹ ab|cd`（`x` 取 `e`）。

（`CONCEPTS.md` §3.11：full 情形下 quartet 系统的完整刻画。证明只需
「两条相容 split 必嵌套」+「共同元素 `e` 排除交叉情形」。） -/
theorem displaysQuartet_of_displaysQuartet_common {a b c d e : X}
    (h1 : T.DisplaysQuartet a b c e) (h2 : T.DisplaysQuartet a b d e) :
    T.DisplaysQuartet a b c d := by
  obtain ⟨s1, hs1, ha1, hc1⟩ := h1
  obtain ⟨s2, hs2, ha2, hd2⟩ := h2
  have hcomp : Split.Compatible s1 s2 := pairwiseCompatible T s1 hs1 s2 hs2
  rcases (Split.compatible_iff_subset.mp hcomp) with h | h | h | h
  · -- `A₁ ⊆ A₂`：`d ∉ A₁`（因 `d ∉ A₂`），故 `d ∈ B₁`；用 `s₁`
    refine ⟨s1, hs1, ha1, fun x hx => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxc | hxd
    · rw [hxc]
      exact hc1 (by simp)
    · rw [hxd]
      exact Split.mem_sideB_of_not_mem_sideA s1 fun hdA =>
        (Split.mem_sideB_iff_not_mem_sideA s2 d).mp (hd2 (by simp)) (h hdA)
  · -- `A₁ ⊆ B₂`：`a ∈ A₁ ⊆ B₂` 与 `a ∈ A₂` 矛盾
    have ha1' : a ∈ ({a, b} : Finset X) := by simp
    exfalso
    exact (Finset.disjoint_left.mp s2.disjoint_sides) (ha2 ha1') (h (ha1 ha1'))
  · -- `B₁ ⊆ A₂`：`e ∈ B₁ ⊆ A₂` 与 `e ∈ B₂` 矛盾
    have hc1' : e ∈ ({c, e} : Finset X) := by simp
    have hd2' : e ∈ ({d, e} : Finset X) := by simp
    exfalso
    exact (Finset.disjoint_left.mp s2.disjoint_sides) (h (hc1 hc1')) (hd2 hd2')
  · -- `B₁ ⊆ B₂`：`c ∈ B₁ ⊆ B₂`；用 `s₂`
    have hc1' : c ∈ ({c, e} : Finset X) := by simp
    have hd2' : d ∈ ({d, e} : Finset X) := by simp
    exact ⟨s2, hs2, ha2, fun x hx => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxc | hxd
      · rw [hxc]; exact h (hc1 hc1')
      · rw [hxd]; exact hd2 hd2'⟩

/-! ### 展示 quartet 拓扑 -/

/-- 树 `T` **展示** quartet 拓扑 `q`：存在 `T` 的边，在 `q.supp` 上诱导出 `q.top` 这一配对。 -/
def DisplaysTopology (q : QuartetTopology X) : Prop :=
  ∃ s : Split X, T.IsSplitOf s ∧
    ∀ (x : X) (hx : x ∈ q.supp), (x ∈ s.sideA ↔ (⟨x, hx⟩ : ↥q.supp) ∈ q.top.sideA)

end Cladogram

universe u v

/-- **Quartet 相容性**（存在性命题）。

`CONCEPTS.md` §3.11：一般情形 **NP-complete**（Steel 1992），故**只能作「存在性命题 / 算法目标」**，
**不能当判据或定义** —— 否则等于把 NP-hard 写进定义。 -/
def QuartetCompatible {X : Type u} [Fintype X] [DecidableEq X]
    (Q : Set (QuartetTopology X)) : Prop :=
  ∃ T : Cladogram.{u, v} X, ∀ q ∈ Q, T.DisplaysTopology q

/-! ## quartet 距离 -/

namespace Cladogram

/-- 树 `T` 展示的 quartet 拓扑集（`Set` 版，因 `IsSplitOf` 不可判定）。 -/
def displaysSet (T : Cladogram X) : Set (QuartetTopology X) := {q | T.DisplaysTopology q}

end Cladogram

/-- **quartet 距离**（§5 M5）：**固定支撑集** `S` 上两个 quartet 拓扑集 `Q`、`Q'` 的对称差大小。

取固定支撑集是因为 `QuartetTopology` 的 `top` 字段类型**依赖** `supp`（§3.5 的「quartet + split」
设计），故全局 `Finset (QuartetTopology X)` 需要依赖型 `DecidableEq`；限定支撑集后
`Split ↥S` 有现成的可判定相等，距离也正对应「同一叶集上的两个 quartet 系统」。

复用 `symmDiffCard` —— 与 RF 距离同一骨架，故度量性质直接继承。 -/
abbrev quartetDistance {S : Finset X} (Q Q' : Finset (Split ↥S)) : ℕ := symmDiffCard Q Q'

theorem quartetDistance_comm {S : Finset X} (Q Q' : Finset (Split ↥S)) :
    quartetDistance Q Q' = quartetDistance Q' Q :=
  symmDiffCard_comm Q Q'

@[simp] theorem quartetDistance_self {S : Finset X} (Q : Finset (Split ↥S)) :
    quartetDistance Q Q = 0 :=
  symmDiffCard_self Q

@[simp] theorem quartetDistance_eq_zero_iff {S : Finset X} {Q Q' : Finset (Split ↥S)} :
    quartetDistance Q Q' = 0 ↔ Q = Q' :=
  symmDiffCard_eq_zero_iff

theorem quartetDistance_triangle {S : Finset X} (Q R Q' : Finset (Split ↥S)) :
    quartetDistance Q Q' ≤ quartetDistance Q R + quartetDistance R Q' :=
  symmDiffCard_triangle Q R Q'
