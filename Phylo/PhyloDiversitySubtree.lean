/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PhyloDiversity

/-!
# `Phylo.PhyloDiversitySubtree` —— `T|W` 载体的**第一层**（W12h 第五–六轮）

Steel 2005 式 (1)（PD 的加权交换性质）的选 `x` 论证需要「`W` 的最小子树 `T|W` ＋ 其**外边** ＋
挂在 `T|W` 上的子树族」。本模块给出**第一层**：可复用的定义 ＋ 已证引理，
并**如实标注**尚未完成的部分（见文件末「尚未完成」）。

## 复用的既有件（库内已有，本模块不重复造）

* `Cladogram.inSide`／`inSide_self`／`inSide_comm`／**`inSide_trans`**（`Phylo/Split.lean:633–645`）
  —— 「删去 `e` 后同侧」是**等价关系**；`Cladogram.IsSep` 是它的否定
  （`isSep_iff_not_inSide`，见 `Phylo/PhyloDiversity.lean`）；
* `Cladogram.sideLeaves`／`mem_sideLeaves`／**`sideLeaves_leaf_edge`**（`Phylo/Split.lean:529–581`）
  —— 叶边一侧只有该叶自己；`isIsolated_leaf_deleteEdges`（同处）；
* `Cladogram.spanVerts`／`pathVerts`／`inducedSubgraph`（`Phylo/Core.lean:261–288`）—— 最小子树的顶点集；
* `Cladogram.IsCovered.mono`、`not_isSep_self`、`isSep_comm`（`Phylo/PhyloDiversity.lean`）。

## 本模块内容

* `IsPendantEdgeOf T W w e`：`e` 是 `T|W` 在 `w` 处的**外边**
  （= `cov(W,e) ∧ ¬cov(W∖{w},e)`，即「`w` 的悬挂路径上的边」）；
* `isSep_of_isPendantEdgeOf_of_ne`：**核心引理** —— `e` 是 `w` 的外边、`z ∈ W`、`z ≠ w`
  ⟹ `IsSep e (leaf w) (leaf z)`（用 `inSide_trans` 证）；
* `HangOff T W w`：**外边的「同侧外侧」** —— 正确形式是
  `{z | ∃ e, IsPendantEdgeOf T W w e ∧ ¬ IsSep e (leaf w) (leaf z)}`（= `⋃_e outer(e)`，
  即 `T|W` 在 `w` 处**压缩悬挂边**的外侧）；
* `mem_hangOff_self_of_pendant`：`w ∈ HangOff T W w`（当 `P(w) ≠ ∅`）；
* **两条「错形式」的机器证据**（见下 ★）：
  `forall_form_subset_singleton`（∀-形式塌缩到 `{w}`）、
  `isSep_form_eq_compl_singleton`（**∃-形式取 `IsSep` 则等于 `{w}ᶜ`**）。

## ★ 三次量词/极性更正（W12h 第四–六轮，全部有机器证据）

| 轮的写法 | 机器判定 | 正确形式 |
|---|---|---|
| 第四轮：`Out(w)` =「对**所有**外边都与 `leaf w` **同侧**」（∀-`¬IsSep`） | `⊆ {w}`（`forall_form_subset_singleton`）✗ 太小 | |
| 第五轮：`HangOff` =「**存在**外边把 `leaf z` 与 `leaf w` **分开**」（∃-`IsSep`） | `= {w}ᶜ`（`isSep_form_eq_compl_singleton`）✗ 太大 | |
| **第六轮（本版）**：`HangOff` =「**存在**外边与 `leaf w` **同侧**」（∃-`¬IsSep`） | —— | ✅ `= ⋃_e outer(e) = outer(最内侧外边)` |

★ 教训（第三次同类）：**「∀/∃」与「同侧/分开」两个开关必须同时校正**；
`∀`-形式与 `∃`-形式在 `IsSep`/`¬IsSep` 上互为补集，写错一个就会把**已被证伪**的结论
（「任取 `x` 都行」或「没有 `x` 可行」）假证出来。

用 `HangOff`（第六轮形式）后，**充分条件 (A)** 可以逐边说明：若
`(W'∖W) ∩ HangOff T W w = ∅`，则对每条 `f ∈ P(w)`：`W'∩outer(f) = ∅`（`W'∖W` 由假设，
`W'∩W` 由核心引理）⇒ `¬cov(W',f) ∧ cov(W'∪{w},f)` ⇒ `P(w) ⊆ Gain(w)` ⇒
`PD(W∖{w}) + PD(W'∪{w}) ≥ PD(W) + PD(W')` ✓（**这一步本模块未形式化**）。

## 尚未完成（如实）

1. **(A) 的 PD 求和形式化**（把上面的逐边论证写成 `Finset.sum` 不等式）**未做**；
2. **`HangOff` 在互异 `w ∈ W` 上两两不交**（Steel (B) 的计数核）**未证** —— 需要两件几何：
   (i) `z ∉ W` 到 `spanVerts T W` 的**最近点唯一**（路径论证），
   (ii) 互异 `w` 的悬挂路径**互不相交**；
3. 由此，`pdExchange_gap`（Steel 式 (1)）与 `greedy_gap_correct_shape` **仍是开放目标**；
   本模块**没有**、也不声称证出它们。
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **`e` 是 `T|W` 在 `w` 处的「外边」**（`w` 的悬挂路径上的边）：
`e` 被 `W` 覆盖，但把 `w` 从 `W` 拿掉后就不被覆盖 —— 即 `w` 是 `e` 某一侧**唯一**的 `W`-元素。

（Steel 2005：`T|W` 的 exterior edge；本库用 `IsCovered` 表达 `T|W` 的边集。） -/
def IsPendantEdgeOf (T : Cladogram X) (W : Finset X) (w : X) (e : Sym2 T.V) : Prop :=
  IsCovered T W e ∧ ¬ IsCovered T (W.erase w) e

/-- ★★★ **核心引理**：`e` 是 `w` 的外边、`z ∈ W`、`z ≠ w` ⟹ `e` 分离 `leaf w` 与 `leaf z`。

**证明**：`¬cov(W∖{w},e)` 说明 `W∖{w}` 里没有一对被 `e` 分离；而 `cov(W,e)` 给出一对见证
`p, q`，其中至少一个是 `w`（否则两者都在 `W∖{w}` 内）。若 `z` 与 `leaf w` 同侧，则由
`inSide_trans` 得见证的另一端与 `leaf z` 同侧 —— 而两者都在 `W∖{w}` 内，与 `¬cov(W∖{w},e)` 矛盾。 -/
theorem isSep_of_isPendantEdgeOf_of_ne {T : Cladogram X} {W : Finset X} {w z : X}
    {e : Sym2 T.V} (he : IsPendantEdgeOf T W w e) (hz : z ∈ W) (hzw : z ≠ w) :
    T.IsSep e (T.leaf w) (T.leaf z) := by
  classical
  by_contra hcon
  have hin : T.inSide e (T.leaf w) (T.leaf z) := of_not_not hcon
  obtain ⟨p, hp, q, hq, hsep⟩ := he.1
  have hno : ∀ a ∈ W.erase w, ∀ b ∈ W.erase w, T.inSide e (T.leaf a) (T.leaf b) := by
    intro a ha b hb
    by_contra h
    exact he.2 ⟨a, ha, b, hb, (isSep_iff_not_inSide T e (T.leaf a) (T.leaf b)).mpr h⟩
  have hzw' : z ∈ W.erase w := Finset.mem_erase.mpr ⟨hzw, hz⟩
  rcases eq_or_ne p w with hpw | hpw
  · rw [hpw] at hsep
    rcases eq_or_ne q w with hqw | hqw
    · rw [hqw] at hsep
      exact not_isSep_self T e (T.leaf w) hsep
    · have hq' : q ∈ W.erase w := Finset.mem_erase.mpr ⟨hqw, hq⟩
      rcases eq_or_ne q z with hqz | hqz
      · rw [hqz] at hsep
        exact hsep hin
      · exact hsep (inSide_trans T e hin (hno z hzw' q hq'))
  · rcases eq_or_ne q w with hqw | hqw
    · rw [hqw] at hsep
      have hp' : p ∈ W.erase w := Finset.mem_erase.mpr ⟨hpw, hp⟩
      have hsep' : T.IsSep e (T.leaf w) (T.leaf p) :=
        (isSep_comm T e (T.leaf p) (T.leaf w)).mp hsep
      rcases eq_or_ne p z with hpz | hpz
      · rw [hpz] at hsep'
        exact hsep' hin
      · exact hsep' (inSide_trans T e hin (hno z hzw' p hp'))
    · have hp' : p ∈ W.erase w := Finset.mem_erase.mpr ⟨hpw, hp⟩
      have hq' : q ∈ W.erase w := Finset.mem_erase.mpr ⟨hqw, hq⟩
      exact hsep (hno p hp' q hq')

/-- ★★★ **外边「同侧外侧」的物种集**（W12h **第六轮更正**的形式）。

`z ∈ HangOff T W w` ⟺ 存在 `w` 的一条外边使 `leaf z` 与 `leaf w` **同侧**
⟺ `z ∈ ⋃_{e ∈ P(w)} outer(e) = outer(最内侧外边)`（= `T|W` 在 `w` 处的**压缩悬挂边**外侧）。
即：`z` 挂在 `w` 的悬挂路径上（或在其外侧）✓ —— 这正是 Steel (3) 需要的那一组。 -/
def HangOff (T : Cladogram X) (W : Finset X) (w : X) : Set X :=
  {z | ∃ e : Sym2 T.V, IsPendantEdgeOf T W w e ∧ ¬ T.IsSep e (T.leaf w) (T.leaf z)}

/-- ★★ `w ∈ HangOff T W w`（只要 `w` 有外边；`inSide` 自反）。 -/
theorem mem_hangOff_self_of_pendant {T : Cladogram X} {W : Finset X} {w : X}
    (hpend : ∃ e : Sym2 T.V, IsPendantEdgeOf T W w e) : w ∈ HangOff T W w := by
  obtain ⟨e, he⟩ := hpend
  exact ⟨e, he, fun h => h (inSide_self T e (T.leaf w))⟩

/-- ★★★ **∀-形式塌缩到 `{w}`**（**第四轮**写法的机器反证）。

「对**所有**外边都与 `leaf w` 同侧」的物种集至多 `{w}`：因为**叶边**外侧只有叶自己
（`sideLeaves_leaf_edge`），任何 `z ≠ w` 都被叶边分离。 -/
theorem forall_form_subset_singleton {T : Cladogram X} {W : Finset X} {w : X} {b : T.V}
    (hb : T.graph.Adj (T.leaf w) b)
    (hpend : IsPendantEdgeOf T W w s(T.leaf w, b)) :
    {z : X | ∀ e : Sym2 T.V, IsPendantEdgeOf T W w e → ¬ T.IsSep e (T.leaf w) (T.leaf z)}
      ⊆ {w} := by
  classical
  intro z hz
  rw [Set.mem_singleton_iff]
  by_contra hne
  have hnotin : z ∉ T.sideLeaves s(T.leaf w, b) (T.leaf w) := by
    rw [T.sideLeaves_leaf_edge hb]
    simp only [Finset.mem_singleton]
    exact hne
  rw [T.mem_sideLeaves_iff_inSide] at hnotin
  exact (hz s(T.leaf w, b) hpend) hnotin

/-- ★★★ **∃-形式取 `IsSep` 则等于 `{w}ᶜ`**（**第五轮**写法的机器反证）。

第五轮把 `HangOff` 写成「存在外边把 `leaf z` 与 `leaf w` **分开**」；由叶边的存在性
（`hb` ＋ `hpend`）与 `sideLeaves_leaf_edge`，该集合**恰好**是除 `w` 以外的所有物种 ——
即**太大**（把任意 `z ≠ w` 都算成「挂在 `w` 上」）⇒ 会把「任取 `x` 都行」假证出来 ✗。 -/
theorem isSep_form_eq_compl_singleton {T : Cladogram X} {W : Finset X} {w : X} {b : T.V}
    (hb : T.graph.Adj (T.leaf w) b)
    (hpend : IsPendantEdgeOf T W w s(T.leaf w, b)) :
    {z : X | ∃ e : Sym2 T.V, IsPendantEdgeOf T W w e ∧ T.IsSep e (T.leaf w) (T.leaf z)}
      = {z : X | z ≠ w} := by
  classical
  ext z
  constructor
  · rintro ⟨e, _, hsep⟩ hzw
    exact not_isSep_self T e (T.leaf w) (hzw ▸ hsep)
  · intro hz
    refine ⟨s(T.leaf w, b), hpend, ?_⟩
    have hnotin : z ∉ T.sideLeaves s(T.leaf w, b) (T.leaf w) := by
      rw [T.sideLeaves_leaf_edge hb]
      simp only [Finset.mem_singleton]
      exact hz
    rw [T.mem_sideLeaves_iff_inSide] at hnotin
    rw [isSep_iff_not_inSide]
    exact hnotin

end Cladogram

end
