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
  `isSep_form_eq_compl_singleton`（**∃-形式取 `IsSep` 则等于 `{w}ᶜ`**）；
* **第七轮新增（(A) 的几何核）**：
  `inSide_of_not_inSide_of_not_inSide`（**三顶点同侧律**：树删一条边恰有两个分量，
  由 `inSide_or_inSide` 二分律证）、
  `isPendantEdgeOf_subset_gain_of_adj`（在 (B) 计数前提下，`w` 的每条外边都落在 `Gain(w)` 里
  —— 即 (A) 所需的 `¬cov(W',e) ∧ cov(W'∪{w},e)`）。

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

1. **(A) 的 PD 求和装配未完成**（第七轮试过，**如实记录卡点**）：需要
   `PD(W) − PD(W∖{w}) = Σ_e [IsPendantEdgeOf] · w_e` 与并集版两个差分恒等式 ＋ 最终一次实数重排。
   本文件里 **`ring` 不可用**（`unknown tactic`）✗、**`ite` 的两个旧引理名已弃用**（须用
   `ite_eq_left`／`ite_eq_right`；用旧名会产生**告警** ⇒ 非 0 输出 ⇒ 验收失败）✗、`Edge` 拆成相邻对时
   `SimpleGraph.mem_edgeSet` 名字解析失败 ✗ ⇒ 这三处需换写法（`split_ifs` ＋ `sub_add_cancel`/
   `add_le_add_iff_right` 等显式引理 ＋ 正确 API 名）后再做一次；
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

/-- ★★★ **三顶点同侧律**（树删去一条边恰有两个连通分量）：若 `u` 与 `v`、`u` 与 `w`
都**不同侧**（`¬inSide`），则 `v` 与 `w` **同侧**。用 `inSide_or_inSide`（二分律）证。 -/
theorem inSide_of_not_inSide_of_not_inSide {T : Cladogram X} {a b : T.V}
    (hab : T.graph.Adj a b) {u v w : T.V}
    (huv : ¬ T.inSide s(a, b) u v) (huw : ¬ T.inSide s(a, b) u w) :
    T.inSide s(a, b) v w := by
  rcases T.inSide_or_inSide hab (x := u) with hu | hu
  · have hv : T.inSide s(a, b) v b := by
      rcases T.inSide_or_inSide hab (x := v) with hv | hv
      · exact absurd (inSide_trans T _ hu ((inSide_comm T _ v a).mp hv)) huv
      · exact hv
    have hw : T.inSide s(a, b) w b := by
      rcases T.inSide_or_inSide hab (x := w) with hw | hw
      · exact absurd (inSide_trans T _ hu ((inSide_comm T _ w a).mp hw)) huw
      · exact hw
    exact inSide_trans T _ hv ((inSide_comm T _ w b).mp hw)
  · have hv : T.inSide s(a, b) v a := by
      rcases T.inSide_or_inSide hab (x := v) with hv | hv
      · exact hv
      · exact absurd (inSide_trans T _ hu ((inSide_comm T _ v b).mp hv)) huv
    have hw : T.inSide s(a, b) w a := by
      rcases T.inSide_or_inSide hab (x := w) with hw | hw
      · exact hw
      · exact absurd (inSide_trans T _ hu ((inSide_comm T _ w b).mp hw)) huw
    exact inSide_trans T _ hv ((inSide_comm T _ w a).mp hw)

/-- ★★★ **(A) 的几何核**：在「计数前提」(B) 下，`w` 的外边 `s(a,b)` **属于** `Gain(w)`，
即 `¬cov(W',s(a,b)) ∧ cov(W'∪{w},s(a,b))`。

`W'` 的每个元素都被 `s(a,b)` 与 `leaf w` 分离：若该元素在 `W` 内用核心引理
（`isSep_of_isPendantEdgeOf_of_ne`），否则用 (B) 的「不在 `HangOff` 里」。
于是 `W'` 整体落在另一侧 —— **这一步正是三顶点同侧律**（`W'` 的两个见证不可能被分开）。 -/
theorem isPendantEdgeOf_subset_gain_of_adj {T : Cladogram X} {W W' : Finset X} {w : X}
    {a b : T.V} (hab : T.graph.Adj a b) (hW' : W'.Nonempty) (hwW' : w ∉ W')
    (hcount : ∀ z ∈ W' \ W, z ∉ HangOff T W w)
    (he : IsPendantEdgeOf T W w s(a, b)) :
    ¬ IsCovered T W' s(a, b) ∧ IsCovered T (W' ∪ {w}) s(a, b) := by
  classical
  have key : ∀ z ∈ W', T.IsSep s(a, b) (T.leaf w) (T.leaf z) := by
    intro z hz
    by_cases hzW : z ∈ W
    · exact isSep_of_isPendantEdgeOf_of_ne he hzW (fun h => hwW' (h ▸ hz))
    · by_contra hsep
      exact hcount z (Finset.mem_sdiff.mpr ⟨hz, hzW⟩) ⟨s(a, b), he, hsep⟩
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    have hin : T.inSide s(a, b) (T.leaf p) (T.leaf q) :=
      inSide_of_not_inSide_of_not_inSide hab (key p hp) (key q hq)
    exact hpq hin
  · obtain ⟨z, hz⟩ := hW'
    exact ⟨w, Finset.mem_union_right _ (Finset.mem_singleton_self w), z,
      Finset.mem_union_left _ hz, key z hz⟩

end Cladogram

end
