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

## 已完成（第九–十轮）

* ✅ **(A) 已完整落地**：`PD_sub_erase`／`PD_sub_insert`（两个差分恒等式）＋ `pdExchange_of_gain`
  （装配）＋ **`pdExchange_gap_of_counting`**（条件形态：`(B) 的计数 ⇒ pdExchange_gap T`，命名如实 ✓）；
* ✅ **(B) ⇐ (C) 已落地**：`exists_unblocked_of_hangOff_disjoint`（**鸽巢计数**：
  `z ∉ W` 至多落在一个 `HangOff(w)` ＋ `|W'∖W| < |W∖W'|` ⇒ 存在未被挡住的 `w`）＋
  `pdExchange_gap_of_hangOff_disjoint`（**(C) ⇒ 无条件 `pdExchange_gap T`**）＋
  `greedy_gap_correct_shape_of_hangOff_disjoint`（**(C) ⇒ 修复形态**，与已入库的
  `greedy_gap_correct_shape_of_exchange` 合成；原 `def greedy_gap_correct_shape` **逐字保留** ✓）。

## 唯一的剩余缺口 (C)（如实）

**(C)**：`∀ W, ∀ z ∉ W, ∀ w₁ w₂ ∈ W, z ∈ HangOff(w₁) → z ∈ HangOff(w₂) → w₁ = w₂`
（即「`z ∉ W` **至多挂在一条**悬挂路径上」）。它需要一条**树分量几何**：
`region(w) := outer(最内侧外边)` 是 `T − f(w)` 的一个连通分量（含 `leaf w`，且 `region(w) ∩ W = {w}` ✓ 已可由
`isSep_of_isPendantEdgeOf_of_ne` 得），而**树中两条边的割分量若相交必含一个另一个** ⇒ 若
`z ∈ region(w₁) ∩ region(w₂)`（且 `z ∉ W`）则 `region(w₁) ⊆ region(w₂)` 或反之，
于是 `w₁ ∈ region(w₂) ∩ W = {w₂}` ⇒ `w₁ = w₂` ✗ 矛盾 ✓。

⇒ **要证的就是「两条边的割分量相交 ⇒ 嵌套」这一条**（可用 `existsUnique_path`／`spanVerts` 的路径论证，
或 `inSide_or_inSide` 的二分类性导出）。**本批未证**；`pdExchange_gap` 与 `greedy_gap_correct_shape`
**仍是开放目标**（未被反驳 ✓；本模块**没有**、也不声称证出它们 ✓）。
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

/-- 任意 `Sym2` 都是一对（非依赖消去，避开依赖 `motive` 的消去器问题）。 -/
theorem sym2_eq_pair (T : Cladogram X) (e : Sym2 T.V) : ∃ a b : T.V, e = s(a, b) :=
  Sym2.ind (fun a b => ⟨a, b, rfl⟩) e

/-- `Edge` 可拆成一对**相邻**顶点（`SimpleGraph.mem_edgeSet` 的**图参数显式**）。 -/
theorem exists_adj_of_mem {T : Cladogram X} {e : Sym2 T.V} (he : e ∈ T.graph.edgeSet) :
    ∃ a b : T.V, T.graph.Adj a b ∧ e = s(a, b) := by
  obtain ⟨a, b, hab⟩ := sym2_eq_pair T e
  refine ⟨a, b, ?_, hab⟩
  rw [hab] at he
  exact (SimpleGraph.mem_edgeSet T.graph).mp he

/-- `Edge` 版：取相邻的一对。 -/
theorem exists_adj_of_edge (T : Cladogram X) (e : Edge T) :
    ∃ a b : T.V, T.graph.Adj a b ∧ e.1 = s(a, b) :=
  exists_adj_of_mem (T := T) e.2

end Cladogram

/-! ## §2 (A)：PD 求和装配 ＋ 条件形态的 `pdExchange_gap`

第八轮记录的三条卡点绕法（本段全部遵守）：
① **不用 `ring`** —— 实数重排用 `sub_self`／`sub_zero`／`sub_le_iff_le_add`／`add_le_add_iff_right`
   ＋ `add_assoc`／`add_comm`／`sub_add_cancel`；
② **不写弃用引理名** —— 逐边用 `by_cases` ＋ `simp [hA, hB, hP]`
   （⚠️ 不用 `split_ifs with a b c`：自动闭合的分支会错位名字绑定 ✗）；
③ `Edge` 取邻接用 `(SimpleGraph.mem_edgeSet T.graph).mp`，并用**非依赖**的 `sym2_eq_pair` 拆 `Sym2`。

★ 第九轮补的正规形修正：**一律用 `insert w W'`**（`simp` 把 `W' ∪ {w}` 规范化成 `insert w W'`；
假设与目标必须同形，否则 `simp` 报 unused argument 且留残余目标 ✗）。需要 `∪ {·}` 时用
`Finset.union_singleton` 显式换算。 -/

namespace Phylo.PhyloDiversity

open Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **差分定位**：`PD(W) − PD(W∖{w})` 恰好等于「`w` 的外边」的权和。 -/
theorem PD_sub_erase (T : Phylogram X) (W : Finset X) (w : X) :
    PD T W - PD T (W.erase w)
      = ∑ e : Edge T.toCladogram,
          (if Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 then T.w e else 0) := by
  classical
  rw [PD_def, PD_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hA : IsCoveredE T W e
  · by_cases hB : IsCoveredE T (W.erase w) e
    · have hP : ¬ Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 := fun h => h.2 hB
      simp [hA, hB, hP]
    · have hP : Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 := ⟨hA, hB⟩
      simp [hA, hB, hP]
  · have hB : ¬ IsCoveredE T (W.erase w) e :=
      fun h => hA (Cladogram.IsCovered.mono (Finset.erase_subset _ _) h)
    have hP : ¬ Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 := fun h => hA h.1
    simp [hA, hB, hP]

/-- ★★★ **差分定位（并集版，`insert` 正规形）**：`PD(insert w W') − PD(W')` 等于 `Gain(w)` 的权和。 -/
theorem PD_sub_insert (T : Phylogram X) (W' : Finset X) (w : X) :
    PD T (insert w W') - PD T W'
      = ∑ e : Edge T.toCladogram,
          (if ¬ IsCoveredE T W' e ∧ IsCoveredE T (insert w W') e then T.w e else 0) := by
  classical
  rw [PD_def, PD_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hE : IsCoveredE T (insert w W') e
  · by_cases hA : IsCoveredE T W' e
    · simp [hE, hA]
    · simp [hE, hA]
  · have hA : ¬ IsCoveredE T W' e :=
      fun h => hE (Cladogram.IsCovered.mono (Finset.subset_insert w W') h)
    simp [hE, hA]

/-- ★★★ **(A) 装配**：若 `w` 的每条外边都在 `Gain(w)` 里，则交换不等式成立（`insert` 正规形）。 -/
theorem pdExchange_of_gain {T : Phylogram X} {W W' : Finset X} {w : X}
    (hGain : ∀ e : Edge T.toCladogram,
      Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 →
        ¬ IsCoveredE T W' e ∧ IsCoveredE T (insert w W') e) :
    PD T W + PD T W' ≤ PD T (W.erase w) + PD T (insert w W') := by
  classical
  have h1 := PD_sub_erase T W w
  have h2 := PD_sub_insert T W' w
  have hle : (∑ e : Edge T.toCladogram,
        (if Cladogram.IsPendantEdgeOf T.toCladogram W w e.1 then T.w e else 0))
      ≤ ∑ e : Edge T.toCladogram,
        (if ¬ IsCoveredE T W' e ∧ IsCoveredE T (insert w W') e then T.w e else 0) := by
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases hP : Cladogram.IsPendantEdgeOf T.toCladogram W w e.1
    · have hQ := hGain e hP
      simp [hP, hQ.1, hQ.2]
    · by_cases hQ : ¬ IsCoveredE T W' e ∧ IsCoveredE T (insert w W') e
      · simp [hP, hQ, T.w_nonneg e]
      · simp [hP, hQ]
  have hmain : PD T W - PD T (W.erase w) ≤ PD T (insert w W') - PD T W' := by
    rw [h1, h2]; exact hle
  have h3 : PD T W ≤ PD T (insert w W') - PD T W' + PD T (W.erase w) :=
    (sub_le_iff_le_add).mp hmain
  have h4 : PD T W + PD T W' ≤ (PD T (insert w W') - PD T W' + PD T (W.erase w)) + PD T W' :=
    (add_le_add_iff_right (PD T W')).mpr h3
  have h5 : (PD T (insert w W') - PD T W' + PD T (W.erase w)) + PD T W'
      = PD T (W.erase w) + PD T (insert w W') := by
    rw [add_assoc, add_comm (PD T (W.erase w)) (PD T W'), ← add_assoc, sub_add_cancel,
      add_comm (PD T (insert w W')) (PD T (W.erase w))]
  rw [h5] at h4
  exact h4

/-- ★★★ **条件形态的 `pdExchange_gap`**（前提 ＝ (B) 的计数：存在 `w ∈ W∖W'`，
其 `HangOff` 不含 `W'∖W` 的任何元素）。

⚠️ 命名如实：这是**条件形态**（不是 `pdExchange_gap` 的证明）—— 由 (A)（`pdExchange_of_gain`）
＋ 几何核（`isPendantEdgeOf_subset_gain_of_adj`）合成；前提 (B) 本批**未证**。 -/
theorem pdExchange_gap_of_counting (T : Phylogram X)
    (hcount : ∀ W W' : Finset X, 2 ≤ W'.card → W'.card < W.card →
      ∃ w ∈ W \ W', ∀ z ∈ W' \ W, z ∉ Cladogram.HangOff T.toCladogram W w) :
    pdExchange_gap T := by
  classical
  intro W W' hW' hlt
  obtain ⟨w, hw, hwcount⟩ := hcount W W' hW' hlt
  have hwW : w ∈ W := (Finset.mem_sdiff.mp hw).1
  have hwW' : w ∉ W' := (Finset.mem_sdiff.mp hw).2
  have hfin := pdExchange_of_gain (W := W) (W' := W') (w := w) fun e he => by
    obtain ⟨a, b, hab, heab⟩ := Cladogram.exists_adj_of_edge T.toCladogram e
    have he' : Cladogram.IsPendantEdgeOf T.toCladogram W w s(a, b) := heab ▸ he
    have hkey := Cladogram.isPendantEdgeOf_subset_gain_of_adj hab
      (Finset.card_pos.mp (by omega)) hwW' hwcount he'
    exact ⟨fun h => hkey.1 (by simpa only [IsCoveredE, heab] using h),
      by simpa only [IsCoveredE, heab, Finset.union_singleton] using hkey.2⟩
  refine ⟨w, hw, ?_⟩
  rw [Finset.union_singleton]
  exact hfin

/-- ★★★ **(C) ⇒ (B)：鸽巢计数**。

若 `z ∉ W` **至多**落在一个 `HangOff(w)`（`w ∈ W`）里，且 `|W'∖W| < |W∖W'|`，
则存在 `w ∈ W∖W'`，其 `HangOff` 不含 `W'∖W` 的任何元素。

**证明**：反设每个 `w ∈ W∖W'` 都被某个 `z ∈ W'∖W` 挡住；用 `Classical.choose` 取挡者，
由 (C) 得该选择在 `W∖W'` 上**单射**，于是 `|W∖W'| ≤ |W'∖W|`，与 `|W'∖W| < |W∖W'|` 矛盾。 -/
theorem exists_unblocked_of_hangOff_disjoint (T : Cladogram X) {W W' : Finset X}
    (hdisj : ∀ z : X, z ∉ W → ∀ w₁ ∈ W, ∀ w₂ ∈ W,
      z ∈ HangOff T W w₁ → z ∈ HangOff T W w₂ → w₁ = w₂)
    (hcard : (W' \ W).card < (W \ W').card) :
    ∃ w ∈ W \ W', ∀ z ∈ W' \ W, z ∉ HangOff T W w := by
  classical
  by_contra hcon
  have hblocked : ∀ w ∈ W \ W', ∃ z ∈ W' \ W, z ∈ HangOff T W w := by
    intro w hw
    by_contra h
    exact hcon ⟨w, hw, fun z hz hzh => h ⟨z, hz, hzh⟩⟩
  let g : ↥(W \ W') → ↥(W' \ W) := fun w =>
    ⟨Classical.choose (hblocked w.1 w.2), (Classical.choose_spec (hblocked w.1 w.2)).1⟩
  have hghang : ∀ w : ↥(W \ W'), (g w : X) ∈ HangOff T W w.1 := fun w =>
    (Classical.choose_spec (hblocked w.1 w.2)).2
  have ginj : Function.Injective g := by
    intro w₁ w₂ heq
    have h1 : (g w₁ : X) ∈ HangOff T W w₁.1 := hghang w₁
    have h2 : (g w₁ : X) ∈ HangOff T W w₂.1 := by rw [heq]; exact hghang w₂
    have hzW : (g w₁ : X) ∉ W := (Finset.mem_sdiff.mp (g w₁).2).2
    have hw₁W : w₁.1 ∈ W := (Finset.mem_sdiff.mp w₁.2).1
    have hw₂W : w₂.1 ∈ W := (Finset.mem_sdiff.mp w₂.2).1
    exact Subtype.ext (hdisj (g w₁) hzW w₁.1 hw₁W w₂.1 hw₂W h1 h2)
  have hle : (W \ W').card ≤ (W' \ W).card := by
    have h : Fintype.card ↥(W \ W') ≤ Fintype.card ↥(W' \ W) :=
      Fintype.card_le_of_injective g ginj
    rwa [Fintype.card_coe, Fintype.card_coe] at h
  exact absurd hle (not_le.mpr hcard)

/-- ★★★ **(C) ⇒ 无条件 `pdExchange_gap`**：把上一条与已入库的
`pdExchange_gap_of_counting` 合成（`|W'| < |W|` ⇒ `|W'∖W| < |W∖W'|` 用 `card_inter_add_card_sdiff`）。

⚠️ 命名如实：结论以 **(C)（挂点两两不交）**为前提；**(C) 本批未证**。 -/
theorem pdExchange_gap_of_hangOff_disjoint (T : Phylogram X)
    (hC : ∀ (W : Finset X) (z : X), z ∉ W → ∀ w₁ ∈ W, ∀ w₂ ∈ W,
      z ∈ Cladogram.HangOff T.toCladogram W w₁ →
        z ∈ Cladogram.HangOff T.toCladogram W w₂ → w₁ = w₂) :
    pdExchange_gap T := by
  classical
  refine pdExchange_gap_of_counting T fun W W' hW' hlt => ?_
  have hcard : (W' \ W).card < (W \ W').card := by
    have ha := Finset.card_inter_add_card_sdiff W' W
    have hb := Finset.card_inter_add_card_sdiff W W'
    rw [Finset.inter_comm W W'] at hb
    omega
  exact exists_unblocked_of_hangOff_disjoint T.toCladogram (hC W) hcard

/-- ★★★ **(C) ⇒ 修复形态**（原 `def greedy_gap_correct_shape` **逐字保留**）：
由 `pdExchange_gap_of_hangOff_disjoint` 与已入库的
`greedy_gap_correct_shape_of_exchange` 合成。⚠️ **条件形态**（前提 ＝ (C) ✓），命名如实。 -/
theorem greedy_gap_correct_shape_of_hangOff_disjoint (T : Phylogram X)
    (hC : ∀ (W : Finset X) (z : X), z ∉ W → ∀ w₁ ∈ W, ∀ w₂ ∈ W,
      z ∈ Cladogram.HangOff T.toCladogram W w₁ →
        z ∈ Cladogram.HangOff T.toCladogram W w₂ → w₁ = w₂) :
    greedy_gap_correct_shape T :=
  greedy_gap_correct_shape_of_exchange T (pdExchange_gap_of_hangOff_disjoint T hC)

end Phylo.PhyloDiversity

end
