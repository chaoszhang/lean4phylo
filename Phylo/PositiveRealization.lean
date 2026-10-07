/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.BunemanGraft
import Phylo.DissimilarityPerturb
import Phylo.InductiveAssembly

-- ⚠️ **不能** import `Phylo.Algorithm.NJHardCore`：收口的组装件
-- （`maxZCherryCore_of_exists_pos` + 本文件的目标定理）要放在**两边都能 import** 的新文件里，
-- 若本文件 import 它就会成环。

/-!
# `Phylo.PositiveRealization` —— `δ.addConst ε` 的**正边权实现**（T0.3 收口缺口）

**目标定理**（本文件**未**完成它；见文末「诚实边界」）：

```lean
theorem exists_realizingPhylogram_pos_of_addConst {X : Type u} [Fintype X] [DecidableEq X]
    (δ : Dissimilarity X) (hfp : δ.FourPoint) (hcard : 4 ≤ Fintype.card X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Phylogram X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
      ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = (δ.addConst ε).val x y
```

## 一、已核对的反例（**不要**再证「T0.2 的构造作用在 `δ_ε` 上各边全正」）

星形度量（星心到四叶的距离）`(ρ_p, ρ_q, ρ_r, ρ_x) = (1, 1, 3, 0)`，取 `ε = 1`：

| 对 | `pq` | `pr` | `qr` | `xp` | `xq` | `xr` |
| --- | --- | --- | --- | --- | --- | --- |
| `δ_ε` | `3` | `5` | `5` | `2` | `2` | `4` |

* 第 0 层：`ρ(p;q,r) = ρ(q;p,r) = 3/2`（**不是** `½β(p,q,r) = 7/2`），收缩 `{p,q} → t`
  得 `{r,x,t}`：`δ'(r,x) = 4`、`δ'(r,t) = 7/2`、`δ'(x,t) = 1/2`；
* 第 1 层：三点互异，三个 leg 是 `(t:0,\ x:1/2,\ r:7/2)`。`bunemanScore` 最大化**第三位**的 leg
  （`2·(7/2) = 7`），故被 graft 的必是 `{t,x}`，其中 `t` 的 leg 为 `0`
  ⇒ **挂边权 `ρ'(t;x,r) = 0`**，两个并列极大序对都躲不掉；
* 于是 T0.2 的树是 `r—t₂ (7/2)`、`t₂—x (1/2)`、**`t₂—t (0)`**、`t—p (3/2)`、`t—q (3/2)`：
  **零权内边 `t₂—t`**。

**但同一 `δ_ε` 确有全正实现**：四叶星 `x:1/2`、`p:3/2`、`q:3/2`、`r:7/2`（六条距离逐条相等）。
⇒ 「T0.2 构造 + 该度量 = 全正」**假**；目标定理本身**真**，只是不能直接用 T0.2 那棵树。

## 二、本文件证了什么（**零占位证明、零新公理**）

**(I1) 不变量 `RealPos`**（派单第二节 (2)）：`RealPos δ R :=`
「凡 `c ∈ R`（「实标签」）且 `a,b,c` 互异，则 `β_δ(a,b,c) := δ(a,c) + δ(b,c) − δ(a,b) > 0`」。

* ★ `bunemanScore_addConst`：`β_{δ_ε}(a,b,c) = β_δ(a,b,c) + ε`；
* ★ `bunemanScore_nonneg`：`δ.FourPoint ⟹ β_δ ≥ 0`（由 ★ `triangle`）；
* ★★ `realPos_addConst`：**第 0 层基例** `δ.FourPoint → 0 < ε → (δ.addConst ε).RealPos univ`
  （`β_ε = β_δ + ε ≥ ε > 0`）；
* ★★ `realPos_shrinkVal`：**归纳步（一步保持）** —— 收缩 `{p,q}` 时 `ρ(p;q,r)` 项在
  「恰有一个合成点」的情形**相消**，剩下的正是 `β_δ(·, p, c)`；故**不需要**极大三元组的任何假设
  （比 `shrinkVal_fourpoint` 便宜）；
* ★★ `realPos_shrinkDissimilarity`：上一条在 `shrinkDissimilarity` 上的打包形式；
* ★★ `rho_pos_of_realPos` / ★★ `rho_addConst_pos`：**派单第二节 (3)** ——
  **实标签 `x` 被 graft 时的挂边权 `ρ(x;i,j) = ½β(i,j,x) > 0`**；
* ★★ `addConst_val_pos`：**(I2)** `x ≠ y → 0 < δ_ε(x,y)`；
* ★★ `exists_realizingPhylogram_addConst`：**无条件存在性**（T0.2 直接给出 `δ_ε` 的实现树，
  无正性结论）—— 它把缺口**精确地**隔离成「正性」一条。

## 三、诚实边界：缺的那一条是 **(G2) 消零权边**

(I1)+(I2) 说明：**实标签**的挂边、以及两端都是实标签的基例边**全正**；零权边只可能由
**合成点**（`BunemanShrink` 造出的 `Sum.inr ()`）造成。

**数值证据**（有理数精确算术探针，400 组随机退化树度量：`n = 3..8`、树边权按概率取 `0`、
`ε ∈ {1,2,3}`）：

* (I1)、(I2) **零反例**；
* 标准 T0.2 递归共产生 **261** 条零权边，**没有一条**触到实标签
  （全是「新合成点 ↔ 旧合成点」或「基例边两端都是合成点」）；
* 合成点在最终树里**必是内部点**：它就是自己那一层的 graft 中心，挂上两片叶后度 `1 + 2 = 3`。

⇒ **收口只差**：在「零权边两端都非叶（度 ≥ 3）」的前提下把零权边**收缩**掉
（商顶点 + 树性/度数/`dist` 记账）。Mathlib 的 `SimpleGraph` **没有** contraction 器械，
但 `SimpleGraph.ConnectedComponent` + `IsAcyclic.isTree_connectedComponent` 可复用。

**这条前提本身有一个便宜得多的证法**（不需要 (I1) 的整套归纳）：设实标签 `x` 的挂边权为 `0`、
邻点为 `v`；`v` 非叶（否则该边连接两片叶，两个标签距离为 `0`，与 (I2) 矛盾），故 `deg v ≥ 3`
（`no_degree_two`）；取 `v` 的两个分支各一片标签叶 `y, z`，则 `v` 在 `y–z` 路径上，于是

`δ(y,z) + ε = δ_ε(y,z) = d(y,z) = d(y,x) + d(x,z) = δ(y,x) + δ(x,z) + 2ε`，

即 `δ(y,z) = δ(y,x) + δ(x,z) + ε > δ(y,x) + δ(x,z) ≥ δ(y,z)`（★ `triangle`）——矛盾。
**所需的唯一器械**是 `Cladogram` 层的一条图论引理「树中每个分支含一片标签」。
该引理与 (G2) **均未在本文件落地**。

## 四、收口计划（路线 (A)：真做收缩；成本估计 350–600 行）

**(A1) 前提「零权边不触叶」**。需要的唯一器械是一条库内**尚无**的图论引理

```lean
theorem exists_leaf_reachable_of_adj (T : Cladogram X) {u v : T.V} (h : T.graph.Adj u v) :
    ∃ x : X, (T.graph.deleteEdges {s(u, v)}).Reachable u (T.leaf x)   -- 「u 侧含一片标签叶」
```

有了它，第三节的 3 行三角不等式即给出前提。可行器械：
`SimpleGraph.ConnectedComponent` + `SimpleGraph.IsAcyclic.isTree_connectedComponent`
（Mathlib `.../SimpleGraph/Acyclic.lean:135`）、
`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`（`Phylo/InductiveAssembly.lean:146` 已在用）、
`reachable_deleteEdges_of_edges_notMem`（`Phylo/QuartetInhabitation.lean:623` 已在用）、
侧集 API `T.sideLeaves` / `T.mem_sideLeaves` / `T.compl_sideLeaves`（`Phylo/Split.lean:529+`）。

**(A2) 收缩**（不动既有文件）：

* `Setoid`：`u ~ v := T.dist u v = 0`（refl `Phylogram.dist_self`、symm `Phylogram.dist_comm`、
  trans `Phylogram.dist_triangle` + `Phylo.TreeDist.dist_nonneg`）；
* 顶点 `Quotient`；邻接 `Adj' C D := ∃ u v, T.graph.Adj u v ∧ T.wExt s(u,v) ≠ 0 ∧ mk u = C ∧ mk v = D`
  （排除零权边，否则出现自环）；
* 边权经代表元取：**同一对类之间的边权是类不变量** `T.wExt s(u,v) = T.dist u v`
  （`Phylo/TreeDistance.lean` 的 `dist_eq_wExt_of_adj`），故**只需权的良定义**、不需边的唯一性；
* `leaf := fun x => mk (T.leaf x)`：单射由 **(I2)** 给出（`mk` 相等 ⇒ `dist = 0` ⇒ `δ_ε(x,y) = 0` ⇒ `x = y`）；
* 无度 2：(A1) ⇒ 零权边两端都非叶 ⇒ 度 ≥ 3（`no_degree_two`）⇒ 合并后度 ≥ 4；
* 树性 / `dist` 记账：把 `T` 的路径按类投影（类内只走零权边 ⇒ 权和不变）。 -/

noncomputable section

open Finset
open scoped BigOperators

universe u

namespace NJ

namespace Dissimilarity

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. `β`（Buneman 得分）的平移与非负性 -/

omit [Fintype X] in
/-- ★ **`β` 在 `addConst` 下的平移**：三个配对都非对角时
`β_{δ_ε}(a,b,c) = β_δ(a,b,c) + ε`。 -/
theorem bunemanScore_addConst (δ : Dissimilarity X) (ε : ℝ) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (δ.addConst ε).bunemanScore a b c = δ.bunemanScore a b c + ε := by
  rw [bunemanScore, bunemanScore, addConst_val_ne δ ε hac, addConst_val_ne δ ε hbc,
    addConst_val_ne δ ε hab]
  ring

omit [Fintype X] [DecidableEq X] in
/-- ★ **`β_δ ≥ 0`**（四点条件 ⟹ 三角不等式，用 `triangle δ hfp c a b`）。 -/
theorem bunemanScore_nonneg (δ : Dissimilarity X) (hfp : δ.FourPoint) (a b c : X) :
    0 ≤ δ.bunemanScore a b c := by
  have h := triangle δ hfp c a b
  simp only [bunemanScore]
  linarith [δ.symm c a, δ.symm c b]

/-! ## 2. 不变量 (I1) `RealPos`：第 0 层基例 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **(I1) 不变量**（派单第二节 (2)）：`R` 是「实标签」集合 ——
即第 `k` 层里仍是原 `X` 元素的那些标签（在 `BunemanShrink` 里用 `Sum.inl` 嵌入）。

**含义**：把「实标签」放在 `bunemanScore` 的**第三位**时得分**严格为正** ——
这正是「实标签的挂边权为正」的来源（见 ★★ `rho_pos_of_realPos`）。 -/
def RealPos (δ : Dissimilarity X) (R : Set X) : Prop :=
  ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → c ∈ R → 0 < δ.bunemanScore a b c

omit [Fintype X] in
/-- ★★ **第 0 层基例**：`δ_ε` 对所有标签满足 (I1)。

`β_ε(a,b,c) = β_δ(a,b,c) + ε ≥ 0 + ε > 0`（★ `bunemanScore_addConst` + ★ `bunemanScore_nonneg`）。 -/
theorem realPos_addConst (δ : Dissimilarity X) (hfp : δ.FourPoint) {ε : ℝ} (hε : 0 < ε) :
    (δ.addConst ε).RealPos (Set.univ : Set X) := by
  intro a b c hab hac hbc _
  rw [bunemanScore_addConst δ ε hab hac hbc]
  have h := bunemanScore_nonneg δ hfp a b c
  linarith

/-! ## 3. (I1) 的归纳步：收缩 `{p,q}` 后不变量保持 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **(I1) 的一步保持**（派单第二节的归纳步）。

设 `R` 是第 `k` 层的实标签集合、`p, q ∉ R`；收缩 `{p,q} → t` 后，第 `k+1` 层的实标签是
`Sum.inl ⟨c, ·⟩`（`c ∈ R`），且 (I1) 仍成立。

**证明要点**：`a, b` 里恰有一个是合成点 `t = Sum.inr ()` 时，
`δ'(t,c) = δ(c,p) − ρ(p;q,r)`、`δ'(t,b) = δ(b,p) − ρ(p;q,r)`，两个 `ρ` 项在 `β'` 里**相消**，
剩下 `δ(c,p) + δ(b,c) − δ(b,p) = β_δ(b,p,c)`。故本引理**不假设** `(p,q,r)` 极大。 -/
theorem realPos_shrinkVal (δ : Dissimilarity X) {R : Set X} (hR : δ.RealPos R) (p q r : X)
    {a b : BunemanShrink p q} (hab : a ≠ b) {c : X} (hc : c ∈ R) (hcp : c ≠ p) (hcq : c ≠ q)
    (hac : a ≠ (Sum.inl (⟨c, hcp, hcq⟩ : {x : X // x ≠ p ∧ x ≠ q}) : BunemanShrink p q))
    (hbc : b ≠ (Sum.inl (⟨c, hcp, hcq⟩ : {x : X // x ≠ p ∧ x ≠ q}) : BunemanShrink p q)) :
    0 < (δ.shrinkDissimilarity p q r).bunemanScore a b
      (Sum.inl (⟨c, hcp, hcq⟩ : {x : X // x ≠ p ∧ x ≠ q})) := by
  let emb : {z : X // z ≠ p ∧ z ≠ q} → BunemanShrink p q := fun z => Sum.inl z
  simp only [bunemanScore, shrinkDissimilarity]
  rcases a with x | u <;> rcases b with y | v
  · -- `inl` / `inl`：三项都归约成 `δ.val`，直接用 (I1)
    have h1 : x.1 ≠ y.1 := fun h => hab (congrArg emb (show x = y from Subtype.ext h))
    have h2 : x.1 ≠ c := fun h => hac (congrArg emb (show x = ⟨c, hcp, hcq⟩ from Subtype.ext h))
    have h3 : y.1 ≠ c := fun h => hbc (congrArg emb (show y = ⟨c, hcp, hcq⟩ from Subtype.ext h))
    have h := hR x.1 y.1 c h1 h2 h3 hc
    simp only [shrinkVal_inl_inl, bunemanScore] at h ⊢
    linarith
  · -- `inl x` / `inr v`：两个 `ρ(p;q,r)` 相消，剩下 `β_δ(x, p, c)`
    have h2 : x.1 ≠ c := fun h => hac (congrArg emb (show x = ⟨c, hcp, hcq⟩ from Subtype.ext h))
    have h := hR x.1 p c x.2.1 h2 hcp.symm hc
    simp only [shrinkVal_inl_inl, shrinkVal_inl_inr, shrinkVal_inr_inl, bunemanScore] at h ⊢
    linarith [δ.symm p c]
  · -- `inr u` / `inl y`：同上（对称）
    have h3 : y.1 ≠ c := fun h => hbc (congrArg emb (show y = ⟨c, hcp, hcq⟩ from Subtype.ext h))
    have h := hR y.1 p c y.2.1 h3 hcp.symm hc
    simp only [shrinkVal_inl_inl, shrinkVal_inr_inl, bunemanScore] at h ⊢
    linarith [δ.symm p c]
  · -- `inr` / `inr`：`Unit` 是子singleton，故 `a = b`，与 `hab` 矛盾
    exact absurd (by rw [Subsingleton.elim u v]) hab

omit [Fintype X] [DecidableEq X] in
/-- ★★ **(I1) 在 `shrinkDissimilarity` 上的打包形式**：实标签集合 `R` 去掉 `p, q` 后不变。 -/
theorem realPos_shrinkDissimilarity (δ : Dissimilarity X) {R : Set X} (hR : δ.RealPos R)
    {p q r : X} (hpR : p ∉ R) (hqR : q ∉ R) :
    (δ.shrinkDissimilarity p q r).RealPos
      {a : BunemanShrink p q |
        ∃ (x : X) (hx : x ∈ R),
          a = (Sum.inl (⟨x, fun h => hpR (h ▸ hx), fun h => hqR (h ▸ hx)⟩ :
            {x : X // x ≠ p ∧ x ≠ q}) : BunemanShrink p q)} := by
  rintro a b c hab hac hbc ⟨x, hxR, rfl⟩
  exact realPos_shrinkVal δ hR p q r hab hxR (fun h => hpR (h ▸ hxR))
    (fun h => hqR (h ▸ hxR)) hac hbc

/-! ## 4. 推论：实标签的挂边权为正（派单第二节 (3)） -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **(G1)（任意层版）**：设 (I1) 对实标签集合 `R` 成立。则 `x ∈ R` 被 graft 时，
挂边权 `ρ(x;i,j) = ½β_δ(i,j,x)` **严格为正**（`i, j, x` 互异）。 -/
theorem rho_pos_of_realPos (δ : Dissimilarity X) {R : Set X} (hR : δ.RealPos R) {x i j : X}
    (hx : x ∈ R) (hxi : x ≠ i) (hxj : x ≠ j) (hij : i ≠ j) : 0 < δ.rho x i j := by
  have h := hR i j x hij hxi.symm hxj.symm hx
  simp only [bunemanScore, rho] at h ⊢
  linarith [δ.symm i x, δ.symm j x]

omit [Fintype X] in
/-- ★★ **(G1)（第 0 层版）**：`δ_ε` 的实标签挂边权为正（等价于「所有 leg ≥ ε/2 > 0」）。 -/
theorem rho_addConst_pos (δ : Dissimilarity X) (hfp : δ.FourPoint) {ε : ℝ} (hε : 0 < ε)
    {x i j : X} (hxi : x ≠ i) (hxj : x ≠ j) (hij : i ≠ j) : 0 < (δ.addConst ε).rho x i j :=
  rho_pos_of_realPos (δ.addConst ε) (realPos_addConst δ hfp hε) (Set.mem_univ x) hxi hxj hij

/-! ## 5. (I2)：`δ_ε` 的非对角项严格为正 -/

omit [Fintype X] in
/-- ★★ **(I2)**：`δ_ε` 的非对角项 `≥ ε > 0`（基例边的正性来源）。 -/
theorem addConst_val_pos (δ : Dissimilarity X) (hfp : δ.FourPoint) {ε : ℝ} (hε : 0 < ε)
    {x y : X} (hxy : x ≠ y) : 0 < (δ.addConst ε).val x y := by
  rw [addConst_val_ne δ ε hxy]
  have h := val_nonneg δ hfp x y
  linarith

/-! ## 6. 无条件存在性（把缺口精确隔离成「正性」） -/

/-- ★★ **T0.2 对 `δ_ε` 的直接推论**：`δ_ε` **有**实现树（无正性结论）。

缺口就在这里：本引理给出 `∃ T`，但要喂给 `Phylo/Algorithm/NJHardCore.lean` 的
`Dissimilarity.maxZCherryCore_of_exists_pos`（「存在边权全正的实现树 ⟹ `δ.MaxZCherryCore`」）
还需要 `∀ e : Edge T.toCladogram, 0 < T.w e` —— T0.2 的那棵树**做不到**
（见文件头第一节的反例）。

⚠️ 本文件**不能** import `Phylo.Algorithm.NJHardCore`（会与收口的组装件成环），
故此处只以**文字**引用它。 -/
theorem exists_realizingPhylogram_addConst (δ : Dissimilarity X) (hfp : δ.FourPoint)
    (hcard : 4 ≤ Fintype.card X) {ε : ℝ} (hε : 0 < ε) :
    (δ.addConst ε).ExistsRealizingPhylogram :=
  Phylo.exists_realizingPhylogram_of_card_ne_one (δ.addConst ε) (by omega)
    (fourPoint_addConst δ hε.le hfp)

end Dissimilarity

end NJ
