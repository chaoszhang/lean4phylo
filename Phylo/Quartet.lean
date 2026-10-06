/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
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
