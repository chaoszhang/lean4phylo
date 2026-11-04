/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERNJStep
import Phylo.Stat.NJShrink

/-!
# `Phylo.Stat.CASTERNJ` —— CASTER-NJ 的两条**登记缺口**（W44 · L5a / L5b）

## 定位

**CASTER-NJ**（对归一化 `D̃` 跑 NJ）与库内既有的 CASTER 定理 1/2（贪心放置）是**不同下游**。
本文件不证新数学，只把「CASTER-NJ 还缺什么」按本库纪律落成 `def … : Prop`。

## ★ 2026-11-05 01:0x 重写（协调侧 W46 复核第 ② 条：两条 `def` 曾是**恒真命题**）

旧形态**不提 NJ、不提距离矩阵**：

```lean
-- 旧（恒真，一行 `⟨T, ⟨Iso.refl T⟩⟩` 即可证）
def njAdditiveGap : Prop := ∀ (T : Cladogram X) (w : …), (∀ e, 0 < w e) → ∃ M, Nonempty (Iso M T)
```
⇒ 台账 74 里有 2 条是虚的。现按 `CASTERNJStep` 的 `njStep` / `mergeStep` **重写成真陈述**：

| 缺口 | 新内容 | 为什么不是恒真 |
|---|---|---|
| `njAdditiveGap` | **归约保持「正权实现树」**：`δ` 有正权实现、`3 ≤ |X|` ⇒ 对任何 `njStep` 选出的对 `(a,b)`，`mergeStep δ a b` 仍有正权实现 | 结论提到 `njStep`（Q 判据的全局最小）与 `mergeStep`（θ=½ 归约），**不**由 `Iso.refl` 给出；`3 ≤ |X|` 见下面的**陈述更正**（`|X| = 2` 时原陈述为假） |
| `njConsistencyGap` | 三条具名义务的**合取**：① 正权实现 ⇒ 存在正樱桃分离界 `δmin`；② Atteson 半径内扰动下每轮选择仍是真樱桃；③ `njAdditiveGap` | ①③ 都未被证；② 已由库内 `njConsistencyStep` 证出（见下） |

## 台账口径

两条 `def` 的名字含 `Gap` ⇒ `list_gaps.sh` 的口径 A 自动计入。

## 引用口径（派单 §3.8，★ 必须照此写）

* **定理本体**（NJ 对可加矩阵正确）：**Studier & Keppler 1988**
  （`references/pdf/StudierKeppler1988_NoteNeighborJoiningAlgorithm.md` `:20-22`），
  假设「all branches are positive」= 本文件的 `HasPositiveRealization`。
* **单步**（Q 的最小对是樱桃）：**Mihaescu–Levy–Pachter 2006** `:135-139` **Theorem 1**；
  与库内 ★★★ `maxZCherryCore`（`Phylo/Algorithm/NJHardCore.lean:308`，**无条件**）同一句。
* **归约**：MLP2006 `:141-148`（`δ(i,j_ab) = ½(δ(i,a)+δ(i,b))`）—— 即 `mergeStep`（θ = ½）。
* **归纳骨架**：SK1988 `:321-329`（基例 `|X| ≤ 4`）。
* ⚠️ **不许**把 Saitou–Nei 1987 当证明出处：SK1988 `:46` 逐字说 SN 的证明「is incorrect」，
  `:315` 说它「misapply the induction hypothesis」。SN1987 只引**算法本身**。
-/

noncomputable section

namespace Phylo.Stat.CASTERNJ

open Phylo
open Phylo.Stat.CASTERNJStep

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## 1. L5a：可加版的缺口 -/

/-- 局部缩写：`δ` 有**边权全正**的实现树。与 `NJ.Dissimilarity.HasPositiveRealization`
同一件事，但**钉死宇宙**（`Phylogram.{0, 0}`）以免 `def … : Prop` 里出现宇宙元变量。 -/
def HasPosReal (δ : NJ.Dissimilarity X) : Prop :=
  ∃ T : Phylogram.{0, 0} X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
    ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y

/-! ★★★ **L5a 的缺口（可加版，按 `njStep`/`mergeStep` 重写）**：
**归约保持「存在边权全正的实现树」**。

即：`δ` 有正权实现树、`(a,b)` 是 NJ 判据 `Q_δ` 的全局最小对 ⇒ 归约后的
`mergeStep δ a b`（θ = ½ 的 `mergeDissim`）**同样有正权实现树**。

**这为什么正是 L5a 卡住的那一步**：SK1988 的归纳（`:321-329`）要在**每一轮**之后继续用
「正权实现树」这个前提；度量侧的归约（`mergeDissim`）库内已有，**树侧的收缩没有**
（把樱桃 `{a,b}` 换成挂在樱桃中点 `w` 上、边权 `½(w_a+w_b)` 的单叶）。
⇒ 有了本命题，L5a 只剩「算法本体 ＋ 装 配」两层工程；没有它，归纳根本走不动。

**要证它需要什么**（`CASTERNJStep.lean` 文件头 §3 步骤 A，150–250 行）：
取 `T` 与樱桃中点的公共邻居 `w`，令 `V' := {v : T.V // v ≠ T.leaf b}`、
图取诱导子图、`w—a` 的权改成 `½(w_a+w_b)`；距离对齐用
`Phylogram.dist_eq_add_of_adj_leaf_dist`（`Phylo/CherryQuartet.lean:79`）。

**诚实边界**：本命题**未被本库证明**。它的**单步正确性**（哪一对被选中）已由
★★★ `njStep_isCherry`（`CASTERNJStep.lean`）证出 —— 缺的是**树层收缩**。

## ★★ 2026-11-05（W46 长程第 32 轮）：**加上了 `3 ≤ |X|`** —— 原陈述在 `|X| = 2` 时**为假**

原陈述（无基数限制）不成立，反例是**退化基数**，与 NJ 无关：

```text
X = Fin 2，δ = 唯一一对的正距离（单边树实现 ⇒ HasPosReal δ 成立）
njStep δ 0 1 成立（只有一对，Q 最小化平凡）
⇒ 归约后 MergeIdx X 0 1 = (X ∖ {0,1}) ⊕ Unit ≃ Unit  —— 只剩**一个**标签
⇒ mergeStep δ 0 1 是 1×1 矩阵（唯一取值 = 0）
```

而**单标签集上不存在 `Cladogram`**（更不存在 `Phylogram`）：
`leaf : X ↪ T.V` 只有一个像；若树只有一个顶点，其度为 `0 ≠ 1`；若树有 ≥ 2 个顶点，
由 Mathlib `SimpleGraph.IsTree.exists_ne_and_degree_eq_one` 存在两个互异的度 1 顶点，
其中至少一个不是标签像 ⇒ `leaf_iff_degree_one` 被违反。
⇒ `HasPosReal (mergeStep δ 0 1)` **为假**，故原 `njAdditiveGap` 为假。

这**不是** NJ 的缺陷（算法在 `|X| ≤ 3` 时本来就没有「恢复拓扑」的内容 —— 见
`CASTERNJStep.lean` §4 与 SK1988 的基例 `|X| ≤ 4`），而是**陈述的量化域**必须与
其它同族结论一致：库内 ★★★ `Cladogram.exists_isCherry_of_max_z` 也带 `3 ≤ Fintype.card X`。
⇒ 本缺口加上 `3 ≤ Fintype.card X`（`|X| = 3` 时归约后是 2 标签、单边树，**可实现且正权**）。

⚠️ 该反例的**完整形式化尚未落盘**（缺的是「单标签集上无 `Cladogram`」这一条，
器械已定位：`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`）；本轮只做**陈述更正 ＋ 论证记录**，
不声称已证。 -/
/-- ★★ **正权 **binary** 实现树** —— SK1988 `:20-22` 的**原假设**（binary＋所有分支为正）。

为什么要把它从 `HasPosReal` 里拆出来：**树层收缩确实用到二叉性**
—— 樱桃中点 `w` 的第三邻居 `z` 只在 `deg w = 3` 时存在且唯一
（★★★ `CASTERNJStep.exists_third`）。非二叉的情形需要**另一支**构造
（`deg w ≥ 4` 时只删叶、把新叶挂回 `w`），**本库未做**（见下面的诚实边界）。 -/
def HasPosRealBinary (δ : NJ.Dissimilarity X) : Prop :=
  ∃ T : Phylogram.{0, 0} X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
    T.toCladogram.IsBinary ∧ ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y

/-- ★★★ **L5a 的缺口（按 `njStep`/`mergeStep` 重写，**binary** 版）**：
**归约保持「存在正权实现树**」**。 -/
def njAdditiveGap : Prop :=
  ∀ (δ : NJ.Dissimilarity X), HasPosRealBinary δ → 3 ≤ Fintype.card X →
    ∀ a b : X, njStep δ a b → HasPosReal (mergeStep δ a b)

/-! ## 1′. 陈述更正的**形式化核**：单标签集上不存在 `Cladogram`

这条是上面反例（`|X| = 2` 归约后只剩 1 个标签）的**唯一非平凡成分**，
与 NJ 无关，纯 `Cladogram` 结构事实。

证法（`IsTree.exists_ne_and_degree_eq_one`，Mathlib）：
* 若 `Nontrivial T.V`：树有**两个互异**的度 1 顶点；由 `leaf_iff_degree_one` 二者都是标签像，
  但标签集是单点集 ⇒ 两个像相等，矛盾。
* 若 `Subsingleton T.V`：`T.leaf y` 的度必为 `1`（它是标签像），但任一同伴都等于它本身
  ⇒ 度为 `0`，矛盾。 -/
theorem not_cladogram_of_subsingleton {Y : Type} [Fintype Y] [DecidableEq Y]
    [Subsingleton Y] [Nonempty Y] (T : Cladogram Y) : False := by
  classical
  obtain ⟨y⟩ := ‹Nonempty Y›
  by_cases hV : Nontrivial T.V
  · haveI := hV
    haveI : Finite T.graph.edgeSet := Finite.of_fintype _
    obtain ⟨u, v, huv, hu1, hv1⟩ := T.isTree.exists_ne_and_degree_eq_one
    obtain ⟨x, hx⟩ := (T.isLeaf_iff_degree_eq_one u).mpr hu1
    obtain ⟨x', hx'⟩ := (T.isLeaf_iff_degree_eq_one v).mpr hv1
    exact huv (by rw [← hx, ← hx']; exact congrArg T.leaf (Subsingleton.elim x x'))
  · haveI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV
    have h1 : T.graph.degree (T.leaf y) = 1 :=
      (T.isLeaf_iff_degree_eq_one (T.leaf y)).mp ⟨y, rfl⟩
    have h2 : T.graph.degree (T.leaf y) = 0 := by
      rw [SimpleGraph.degree_eq_zero]
      intro w hw
      have hww : w = T.leaf y := Subsingleton.elim w (T.leaf y)
      rw [hww] at hw
      exact T.graph.loopless.irrefl (T.leaf y) hw
    omega

/-- ★★ **推论**：单标签集上的任何 `Dissimilarity` 都**没有**正权实现。

（`|X| = 2` 时 `MergeIdx X a b ≃ Unit` ⇒ `mergeStep δ a b` 落在这条上 ⇒
原（无基数限制的）`njAdditiveGap` 在 `|X| = 2` 时为假。） -/
theorem not_hasPosReal_of_subsingleton {Y : Type} [Fintype Y] [DecidableEq Y]
    [Subsingleton Y] [Nonempty Y] (τ : NJ.Dissimilarity Y) :
    ¬ HasPosReal (X := Y) τ := by
  rintro ⟨T, -, -⟩
  exact not_cladogram_of_subsingleton (Y := Y) T.toCladogram

/-- ★★★ **A8 收口｜`njAdditiveGap` **已证**（不再是缺口）**。

给定正权 **binary** 实现树 `T` 与 `njStep δ a b`：
1. ★★★ `NJShrink.isCherry_of_njStep`（`Q = −2z` → Weller eq (3) → Thm 2）给出**树层** `T.IsCherry a b`；
2. 取樱桃中点 `w` 与第三邻居 `z`（★★★ `NJShrink.exists_third`，用 `IsBinary`）；
3. ★★★ `NJShrink.shrinkPhylogram` 就是归约后的实现树：边权全正（★★★ `shrinkW_pos`）、
   `dist` 与 `mergeStep` **逐点对齐**（★★★ `shrinkPhylogram_dist`）。

⚠️ **诚实边界**：本定理只覆盖**二叉**实现（`HasPosRealBinary`）。非二叉实现
（`deg w ≥ 4`）需要**另一支**构造 —— 只删叶 `b`、把新叶 `u` 以权 `½(w_a+w_b)` 挂回 `w`，
**本库未做**；`dist` 对齐在那支更容易（路径必过 `w`）。 -/
theorem njAdditiveGap_holds : njAdditiveGap (X := X) := by
  intro δ hpos hcard a b hstep
  obtain ⟨T, hwpos, hbin, hT⟩ := hpos
  have hc : T.IsCherry a b := NJShrink.isCherry_of_njStep δ hwpos hT hcard hstep
  have hckeep := hc
  obtain ⟨hab, w, haw, hbw⟩ := hc
  obtain ⟨z, hwz, hza, hzb, -⟩ := NJShrink.exists_third T hbin hab haw hbw
  have hla : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), NJShrink.leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hzm : z ≠ T.leaf b ∧ z ≠ w :=
    ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩
  refine ⟨NJShrink.shrinkPhylogram T hbin hab haw hbw hza hzb hwz hwpos, ?_, ?_⟩
  · intro e
    have key : ∀ e' : Sym2 (NJShrink.ShrinkV T b w),
        e' ∈ (NJShrink.shrinkGraph T a b w z hza).edgeSet →
          0 < NJShrink.shrinkW T a b w z hza hla hzm e' :=
      Sym2.ind (fun u v he =>
        NJShrink.shrinkW_pos T hbin hab haw hbw hza hzb hwz hwpos hla hzm
          ((SimpleGraph.mem_edgeSet _).mp he))
    exact key e.1 e.2
  · intro u v
    exact NJShrink.shrinkPhylogram_dist T δ hbin hab haw hbw hza hzb hwz hwpos hckeep hT u v

/-! ## 2. L5b 的「噪声传播」一步（**已由库内器材证出**，不是缺口） -/

/-- ★★ **L5b 的第 ② 条已成立**（Atteson 1999 **Theorem 1** 的归纳不变式 (c)）：
`δmin` 是 `δ` 的樱桃分离界、`D̃` 在 Atteson 半径内、`5 ≤ |X|` ⇒
NJ 在 `D̃` 上选出的最小对是 **`δ` 的真樱桃**。

依据：★★★ `njCriterion_minimizer_is_cherry`（`Phylo/AttesonRadius.lean:480`，无需新证）。 -/
theorem njConsistencyStep (δ Dtil : NJ.Dissimilarity X) {δmin ε : ℝ}
    (hsep : NJ.Dissimilarity.IsCherrySeparated δ δmin)
    (hnear : NJ.Dissimilarity.NearlyAdditive δ Dtil δmin ε)
    (hcard : 5 ≤ Fintype.card X) {a b : X} (h : njStep Dtil a b) : δ.IsCherry a b :=
  NJ.Dissimilarity.njCriterion_minimizer_is_cherry δ Dtil hnear hcard hsep h.1 h.2

/-! ## 3. L5b：CASTER 的 `D̃` 上、含噪版（三条具名义务的合取） -/

/-- **L5b 的第 ① 条**：正权实现的度量**存在正的樱桃分离界** `δmin`。
（库内 `IsCherrySeparated` 只有假设形态 `Phylo/AttesonRadius.lean:132`，**没有**从实现树推出它的定理。） -/
def njSeparationBound : Prop :=
  ∀ (δ : NJ.Dissimilarity X), HasPosReal δ →
    ∃ δmin : ℝ, 0 < δmin ∧ NJ.Dissimilarity.IsCherrySeparated δ δmin

/-- **L5b 的第 ② 条（噪声传播）**：`δmin` 是 `δ` 的樱桃分离界、`D̃` 在 Atteson 半径内、
`5 ≤ |X|` ⇒ NJ 在 `D̃` 上选出的最小对是 **`δ` 的真樱桃**。 -/
def njNoiseStep : Prop :=
  ∀ (δ Dtil : NJ.Dissimilarity X) (δmin ε : ℝ),
    NJ.Dissimilarity.IsCherrySeparated δ δmin →
      NJ.Dissimilarity.NearlyAdditive δ Dtil δmin ε → 5 ≤ Fintype.card X →
        ∀ a b : X, njStep Dtil a b → δ.IsCherry a b

/-- ★★ **L5b 的第 ② 条已成立**（Atteson 1999 **Theorem 1** 的归纳不变式 (c)）——
依据 ★★★ `njCriterion_minimizer_is_cherry`（`Phylo/AttesonRadius.lean:480`），无需新证。 -/
theorem njNoiseStep_holds : njNoiseStep (X := X) :=
  fun δ Dtil δmin ε hsep hnear hcard a b h => njConsistencyStep δ Dtil hsep hnear hcard h

/-! ## 3. L5b：CASTER 的 `D̃` 上、含噪版（三条具名义务的合取） -/

/-- ★★★ **L5b 的缺口（CASTER 的 `D̃` 上、含噪版）**：三条具名义务的**合取**。

★ **前提必须是「`D̃` 的近似加性」，不是「可加」**：`D̃` 是 quartet 统计量的加权和，
**不是**距离度量（文档 §7.2 自己这么说）⇒ `njAdditiveGap` 的结论**不能**直接搬过来。

**三条具名子义务**（派单 §3.7，缺一不可）：

1. `njSeparationBound`（**近似加性 / 分离界**，统计层）：正权实现 ⇒ `∃ δmin > 0`，
   `IsCherrySeparated δ δmin`。⇒ **开放**（库内只有假设形态）。
2. `njNoiseStep`（**噪声传播**）：Atteson 半径内的扰动不改变 NJ 的**每一轮**选择。
   ⇒ ★ **已证**：★★ `njNoiseStep_holds`。
3. `njAdditiveGap`（**算法层**：树层收缩 ＋ 算法本体 ＋ 归纳）⇒ **开放**。

⚠️ **数值备注只是证据，不是定理**：`n ≤ 16`、85 350 个 quartet、0 错误（文档 §7.1）。
本 `def` **不**声称它在任何参数下成立。

⚠️ 端到端形态（「末态 split 集 = 真树 split 集」）需要把 n−3 轮写成 Lean 递归
（`MergeIdx` 每轮换类型），本文件**不**假装有它 —— 那是 L5a 步骤 B 的内容。 -/
def njConsistencyGap : Prop :=
  njSeparationBound (X := X) ∧ njNoiseStep (X := X) ∧ njAdditiveGap (X := X)

end Phylo.Stat.CASTERNJ
