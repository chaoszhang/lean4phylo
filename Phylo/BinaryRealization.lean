/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PauplinFormula
import Phylo.InductiveAssembly

/-!
# `Phylo.BinaryRealization` —— 二叉忠实形态 `bme_pauplin_identity_gap_binary` 的**收口件**（W27-c）

## 本文件解决什么

`Phylo/BMELeastSquares.lean:1247` 的 `def bme_pauplin_identity_gap_binary δ T`
（W26-B 另立的**二叉忠实形态**，旧 `def` 逐字未动）要求三件：

1. `T.IsBinary`（`Phylo/Core.lean:93`）；
2. `T` 实现 `δ`（`∀ i j, T.dist (T.leaf i) (T.leaf j) = δ.val i j`）；
3. `BmePauplinNormalization T`（式 (9)，`BMELeastSquares.lean:465`）。

派单（`DISPATCH.md` T3 段）登记的两件缺件，状态如下：

* **②「二叉上 `D_e(u) = 1`」** —— ⚠️ **派单信息过期**：该定理已在
  ★★★ `Phylo.SideDoubling.sideDoublingSum_eq_one_of_isBinary`
  （`Phylo/SideDoubling.lean:530`，零 `sorry`）落地。本文件**不重复证明**，直接引用。
* **① `exists_binary_realizing_phylogram`** —— 本文件落地
  ★★★ `exists_binary_realizingPhylogram`（§3）：在
  `Phylo/InductiveAssembly.lean` 的 Buneman 归纳装配上**加挂 `T.IsBinary`**。

## 结构

### §1 桥：Pauplin 的「有序对双重和」＝ `plane` 求和

`Phylo/PauplinFormula.lean` 的 ★★★ `double_sum_eq_two` 给出（`incidence`/`topoDist` 口径）

　`Σ_x Σ_y 2^{1−p_xy}·S_xy(e) = 2·D_e(u)·D_e(v)`（`e = s(u,v)`），

而 `BmePauplinNormalization` 用的是 `plane`（有序对，`BMELeastSquares.lean:172`）与
`pathOf` 口径。★★★ `bmePauplinNormalization_of_isBinary` 把两者接起来：
**二叉树 ⇒ `BmePauplinNormalization T`**（式 (7)(9) 的树级内容）。

### §2 二叉忠实形态的充分条件

★★★ `bme_pauplin_identity_gap_binary_of_isBinary`：`T.IsBinary` + `T` 实现 `δ`
⇒ `bme_pauplin_identity_gap_binary δ T`。

### §3 二叉实现树（= 缺件 ①）＋ 收口

★★★ `exists_binary_realizingPhylogram`：`2 ≤ |X|` + 四点条件 ⇒ 存在**二叉**实现树。
沿用 `Phylo.exists_realizingPhylogram_of_card_ne_one` 的强归纳骨架，只多加一个合取项：

* 基例 `|Y| = 2`：★★ `Phylo.twoLeafPhylogram` 是单边树（**无内部顶点** ⇒ 二叉义务为空）；
* 归纳步：★★★ `Phylo.graftPhylogram` 在锚点 `t = T'.leaf (Sum.inr ())` 上挂两叶 ——
  `graftGraph_degree_inl_self` 给 `deg t : 1 → 3`，`graftGraph_degree_inl_ne` 给其余旧点度不变，
  `graftGraph_degree_inr` 给新叶度 `1` ⇒ ★★★ `graftPhylogram_isBinary`：**二叉保持**。

### ⚠ 忠实性边界：字面形态在 `|X| ≤ 1` 处为**假**

派单把目标写成「`∀ δ, δ.FourPoint → δ.PositiveDefinite → ∃ T, …`」而**没有**基数前提。
这在 `|X| = 1` 处为假（`|X| = 0` 处也为假，见 §4 注）：

* `|X| = 1`：`Phylogram X` 是**空类型**（`Phylo.not_nonempty_phylogram_of_subsingleton`）；
* `|X| = 0`：`Cladogram.leaf_iff_degree_one` 迫使**所有**顶点度 `≠ 1`；而有限树若有 `≥ 2` 个
  顶点必含两个度 `1` 顶点 ⇒ 唯一的 `Phylogram` 是**单顶点树**（度 `0`）⇒ `IsBinary` 为假。

⇒ 忠实形态必须带 `2 ≤ Fintype.card X`。★★★ `bme_pauplin_identity_gap_binary_literal_form_false_of_card_eq_one`
把 **`|X| = 1`** 的反例机器化，故本文件给的是「**判定 ＋ 忠实形态收口**」，
而不是原字面形态的无假设 `_holds`。

## 文献行号（自核）

`references/md/DesperGascuel2004_BalancedMinimumEvolution.md`：
`:378–383` 平衡平均 `d^T_AB` 只在「两个子树」上递归定义（⇒ `IsBinary` 进数据的依据）；
式 (7) `:2001–2007`「`Σ_{a,b} 2^{r_AB} p_ab = 1`」；式 (9) `:2027`「`SᵗF = 1`」；
Theorem 1 `:619–625`，proof 见 Appendix 2 `:2019` 起。本文件对应的是式 (7)(9) 的**树级**版本
（`BmePauplinNormalization`）及其**二叉**成立范围。
-/

noncomputable section

open Finset
open scoped BigOperators

namespace NJ.Dissimilarity

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## §1 桥：`plane` 求和 ＝ Pauplin 有序对双重和 -/

/-- ★★★ **二叉树 ⇒ `BmePauplinNormalization`**（式 (7)(9) 的树级内容）。

逐边取 `e = s(u,v)`（`Adj u v` ⇒ 是真边）：
`plane` 求和 = `Σ_x Σ_y 2^{1−p_xy}·S_xy(e)`（★★ `sum_sum_eq_plane` ＋
`pathWalk_eq_pathOf` 把 `topoDist`/`incidence` 换成 `pathOf` 口径）
= `2·D_e(u)·D_e(v)`（★★★ `NJ.Pauplin.double_sum_eq_two`）
= `2·1·1 = 2`（★★★ `Phylo.SideDoubling.sideDoublingSum_eq_one_of_isBinary`，`T.IsBinary`）。 -/
theorem bmePauplinNormalization_of_isBinary (T : Phylogram X) (hbin : T.IsBinary) :
    BmePauplinNormalization T := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    -- 二叉 ⇒ 两侧倍增和都 = 1
    have hDu : sideDoublingSum T.toCladogram s(u, v) u = 1 :=
      Phylo.SideDoubling.sideDoublingSum_eq_one_of_isBinary T.toCladogram hbin _ u s(u, v)
        (by simp) (by rw [SimpleGraph.mem_edgeSet]; exact he) rfl
    have hDv : sideDoublingSum T.toCladogram s(u, v) v = 1 :=
      Phylo.SideDoubling.sideDoublingSum_eq_one_of_isBinary T.toCladogram hbin _ v s(u, v)
        (by simp) (by rw [SimpleGraph.mem_edgeSet]; exact he) rfl
    -- 把 `plane` 求和换成 Pauplin 口径的有序对双重和
    have hpow : ∀ x y : X,
        (T.pathOf (T.leaf x) (T.leaf y)).edges.length = NJ.Pauplin.topoDist T x y := by
      intro x y
      rw [NJ.Pauplin.topoDist, NJ.Pauplin.pathWalk_eq_pathOf, SimpleGraph.Walk.length_edges]
    have hinc : ∀ x y : X,
        (if s(u, v) ∈ (T.pathOf (T.leaf x) (T.leaf y)).edges then (1 : ℝ) else 0)
          = NJ.Pauplin.incidence T x y s(u, v) := by
      intro x y
      rw [NJ.Pauplin.incidence, NJ.Pauplin.pathWalk_eq_pathOf]
    have hstep : (∑ x ∈ plane,
          bmeCoeff ((T.pathOf (T.leaf x.1) (T.leaf x.2)).edges.length)
            * (if s(u, v) ∈ (T.pathOf (T.leaf x.1) (T.leaf x.2)).edges then (1 : ℝ) else 0))
        = ∑ x ∈ plane,
            bmeCoeff (NJ.Pauplin.topoDist T x.1 x.2) * NJ.Pauplin.incidence T x.1 x.2 s(u, v) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hpow x.1 x.2, hinc x.1 x.2]
    have hbridge : (∑ x ∈ plane,
            bmeCoeff (NJ.Pauplin.topoDist T x.1 x.2) * NJ.Pauplin.incidence T x.1 x.2 s(u, v))
        = ∑ x : X, ∑ y : X,
            bmeCoeff (NJ.Pauplin.topoDist T x y) * NJ.Pauplin.incidence T x y s(u, v) := by
      rw [← sum_sum_eq_plane
        (fun i j => bmeCoeff (NJ.Pauplin.topoDist T i j) * NJ.Pauplin.incidence T i j s(u, v))]
    rw [hstep, hbridge, NJ.Pauplin.double_sum_eq_two T he, hDu, hDv]
    norm_num

/-! ## §2 二叉忠实形态的充分条件 -/

/-- ★★★ **足够条件**：`T` 二叉**且**实现 `δ` ⇒ 二叉忠实形态
（`bme_pauplin_identity_gap_binary`，`BMELeastSquares.lean:1247`，`def` 逐字未动）。 -/
theorem bme_pauplin_identity_gap_binary_of_isBinary (δ : Dissimilarity X) (T : Phylogram X)
    (hbin : T.IsBinary) (hreal : ∀ i j : X, T.dist (T.leaf i) (T.leaf j) = δ.val i j) :
    bme_pauplin_identity_gap_binary δ T :=
  ⟨hbin, hreal, bmePauplinNormalization_of_isBinary T hbin⟩

/-! ## §3 二叉实现树（缺件 ①）与收口 -/

/-- ★★★ **二叉实现树（命题名）**：`δ` 有**二叉**实现树。
形制同 `NJ.Dissimilarity.ExistsRealizingPhylogram`（`Phylo/Buneman.lean:563`，顶点宇宙钉在 `u`），
只是多一个 `T.IsBinary` 合取项。 -/
def ExistsBinaryRealizingPhylogram (δ : Dissimilarity X) : Prop :=
  ∃ T : Phylogram.{u, u} X, T.IsBinary ∧ ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y

/-- ★★ **两叶单边树是二叉的**：无内部顶点 ⇒ `IsBinary` 的义务为空。 -/
theorem twoLeafPhylogram_isBinary (hcard : Fintype.card X = 2) (c : ℝ) (hc : 0 ≤ c) :
    (Phylo.twoLeafPhylogram hcard c hc).IsBinary := by
  intro v hv
  have hdeg : (Phylo.twoLeafPhylogram hcard c hc).graph.degree v = 1 :=
    Phylo.degree_top_eq_one_of_card_eq_two hcard v
  exact absurd (((Phylo.twoLeafPhylogram hcard c hc).isLeaf_iff_degree_eq_one v).mpr hdeg) hv

/-- ★★★ **基例 `|Y| = 2`（二叉版）**：单边树，权 `δ(a,b)`。 -/
theorem exists_binary_realizingPhylogram_of_card_eq_two (δ : Dissimilarity X)
    (hfp : δ.FourPoint) (hcard : Fintype.card X = 2) :
    δ.ExistsBinaryRealizingPhylogram := by
  classical
  obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two (s := (Finset.univ : Finset X)).mp (by
    rw [Finset.card_univ]; exact hcard)
  refine ⟨Phylo.twoLeafPhylogram hcard (δ.val a b) (δ.val_nonneg hfp a b),
    twoLeafPhylogram_isBinary hcard _ _, ?_⟩
  intro x y
  rw [Phylo.twoLeafPhylogram_dist]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy, hxy, δ.diag]
  · rw [ite_eq_right hxy]
    have hx : x = a ∨ x = b := by
      have hmem : x ∈ (Finset.univ : Finset X) := Finset.mem_univ x
      rw [huniv] at hmem
      simpa using hmem
    have hy : y = a ∨ y = b := by
      have hmem : y ∈ (Finset.univ : Finset X) := Finset.mem_univ y
      rw [huniv] at hmem
      simpa using hmem
    rcases hx with hxa | hxb <;> rcases hy with hya | hyb
    · exact absurd (hxa.trans hya.symm) hxy
    · rw [hxa, hyb]
    · rw [hxb, hya, δ.symm b a]
    · exact absurd (hxb.trans hyb.symm) hxy

omit [Fintype X] in
/-- ★★★ **挂叶手术保持二叉性**：锚点 `t = T'.leaf (Sum.inr ())` 的度 `1 → 3`，
其余旧点度不变、新叶度 `1` ⇒ `IsBinary` 保持。

★ 这是 `InductiveAssembly` 的归纳装配**没有**记在账上的那一条：`no_degree_two` 与
`leaf_iff_degree_one` 在 `BunemanGraft` 里已给，但 `IsBinary`（内部点度**恰** 3）是新的。 -/
theorem graftPhylogram_isBinary (δ : Dissimilarity X) (hfp : δ.FourPoint) (p q r : X)
    (hpq : p ≠ q) (T' : Phylogram (BunemanShrink p q)) (hbin : T'.IsBinary) :
    (Phylo.graftPhylogram δ hfp p q r hpq T').IsBinary := by
  classical
  intro x hx
  rcases x with v | i
  · by_cases hv : v = T'.leaf (Sum.inr ())
    · subst hv
      -- 锚点：`deg t = 1` ⇒ 挂叶后 `1 + 2 = 3`
      have hdeg : (T'.graph.neighborSet (T'.leaf (Sum.inr ()))).ncard = 1 := by
        rw [SimpleGraph.ncard_neighborSet]
        exact (T'.isLeaf_iff_degree_eq_one (T'.leaf (Sum.inr ()))).mp ⟨Sum.inr (), rfl⟩
      show (Phylo.graftGraph T'.graph (T'.leaf (Sum.inr ()))).degree
        (Sum.inl (T'.leaf (Sum.inr ()))) = 3
      rw [Phylo.graftGraph_degree_inl_self, ← SimpleGraph.ncard_neighborSet, hdeg]
    · show (Phylo.graftGraph T'.graph (T'.leaf (Sum.inr ()))).degree (Sum.inl v) = 3
      rw [Phylo.graftGraph_degree_inl_ne T'.graph hv]
      have hnv : ¬ T'.IsLeaf v := by
        intro hl
        refine hx (((Phylo.graftPhylogram δ hfp p q r hpq T').isLeaf_iff_degree_eq_one
          (Sum.inl v)).mpr ?_)
        rw [Phylo.graftGraph_degree_inl_ne T'.graph hv, ← SimpleGraph.ncard_neighborSet,
          SimpleGraph.ncard_neighborSet]
        exact (T'.isLeaf_iff_degree_eq_one v).mp hl
      have hn3 : (T'.graph.neighborSet v).ncard = 3 := by
        rw [SimpleGraph.ncard_neighborSet]
        exact hbin v hnv
      rw [← SimpleGraph.ncard_neighborSet, hn3]
  · have hleaf : (Phylo.graftPhylogram δ hfp p q r hpq T').IsLeaf (Sum.inr i) := by
      refine ((Phylo.graftPhylogram δ hfp p q r hpq T').isLeaf_iff_degree_eq_one
        (Sum.inr i)).mpr ?_
      show (Phylo.graftGraph T'.graph (T'.leaf (Sum.inr ()))).degree (Sum.inr i) = 1
      exact Phylo.graftGraph_degree_inr T'.graph (T'.leaf (Sum.inr ())) i
    exact absurd hleaf hx

/-- ★★★★ **缺件 ①（二叉实现树）**：`2 ≤ |X|` + 四点条件 ⇒ 存在**二叉**实现树。

对 `Fintype.card X` 强归纳（骨架同 `Phylo.exists_realizingPhylogram_of_card_ne_one`）：

* `n = 2`：★★★ `exists_binary_realizingPhylogram_of_card_eq_two`；
* `n ≥ 3`：`exists_max_triple` 取极大三元组 ⇒ 缩小到 `BunemanShrink p q`（`n − 1`，
  仍 `≥ 2`）⇒ 归纳假设给**二叉**实现 `T'` ⇒ `graftPhylogram` 挂回 `p, q`，
  ★★★ `graftPhylogram_isBinary` 保二叉，八个距离情形同 `InductiveAssembly`。 -/
theorem exists_binary_realizingPhylogram (δ : Dissimilarity X) (h2 : 2 ≤ Fintype.card X)
    (hfp : δ.FourPoint) : δ.ExistsBinaryRealizingPhylogram := by
  classical
  have key : ∀ n : ℕ, ∀ {Z : Type u} [Fintype Z] [DecidableEq Z] (δ : Dissimilarity Z),
      Fintype.card Z = n → 2 ≤ Fintype.card Z → δ.FourPoint →
      δ.ExistsBinaryRealizingPhylogram := by
    intro n
    refine Nat.strong_induction_on (p := fun k => ∀ {Z : Type u} [Fintype Z] [DecidableEq Z]
        (δ : Dissimilarity Z), Fintype.card Z = k → 2 ≤ Fintype.card Z → δ.FourPoint →
        δ.ExistsBinaryRealizingPhylogram) n ?_
    intro m ih Z _iZ _dZ δ hcardZ h2Z hfpZ
    rcases eq_or_ne m 2 with hm2 | hm2
    · exact exists_binary_realizingPhylogram_of_card_eq_two δ hfpZ (hcardZ.trans hm2)
    · have h3 : 3 ≤ Fintype.card Z := by omega
      obtain ⟨p, q, r, hpq, hpr, hqr, hmax⟩ := δ.exists_max_triple h3
      have hfp' : (δ.shrinkDissimilarity p q r).FourPoint := by
        intro a b c d
        exact shrinkVal_fourpoint δ hfpZ hpr hqr hmax a b c d
      have hcardShrink : Fintype.card (BunemanShrink p q) = Fintype.card Z - 1 :=
        Phylo.card_bunemanShrink hpq
      have hlt : Fintype.card (BunemanShrink p q) < m := by omega
      have h2' : 2 ≤ Fintype.card (BunemanShrink p q) := by omega
      obtain ⟨T', hbin', hT'⟩ := ih (Fintype.card (BunemanShrink p q)) hlt
        (δ.shrinkDissimilarity p q r) rfl h2' hfp'
      have hT'' : ∀ a b : BunemanShrink p q,
          T'.dist (T'.leaf a) (T'.leaf b) = δ.shrinkVal p q r a b :=
        fun a b => (hT' a b).trans rfl
      refine ⟨Phylo.graftPhylogram δ hfpZ p q r hpq T',
        graftPhylogram_isBinary δ hfpZ p q r hpq T' hbin', ?_⟩
      intro x y
      by_cases hxp : x = p
      · subst x
        by_cases hyp : y = p
        · subst y
          rw [Phylogram.dist_self, δ.diag]
        · by_cases hyq : y = q
          · subst y
            rw [Phylo.graftPhylogram_dist_leaf_pq δ hfpZ p q r hpq T', rho_add_rho δ p q r]
          · rw [Phylo.graftPhylogram_dist_leaf_p δ hfpZ p q r hpq T' hyp hyq,
              hT'' (Sum.inr ()) (Sum.inl ⟨y, hyp, hyq⟩),
              ← attach_left δ p q r ⟨y, hyp, hyq⟩, δ.symm y p]
      · by_cases hxq : x = q
        · subst x
          by_cases hyp : y = p
          · subst y
            rw [Phylogram.dist_comm, Phylo.graftPhylogram_dist_leaf_pq δ hfpZ p q r hpq T',
              rho_add_rho δ p q r, δ.symm q p]
          · by_cases hyq : y = q
            · subst y
              rw [Phylogram.dist_self, δ.diag]
            · rw [Phylo.graftPhylogram_dist_leaf_q δ hfpZ p q r hpq T' hyp hyq,
                hT'' (Sum.inr ()) (Sum.inl ⟨y, hyp, hyq⟩),
                ← attach_right δ hfpZ hpr hqr hmax ⟨y, hyp, hyq⟩, δ.symm y q]
        · by_cases hyp : y = p
          · subst y
            rw [Phylogram.dist_comm,
              Phylo.graftPhylogram_dist_leaf_p δ hfpZ p q r hpq T' hxp hxq,
              hT'' (Sum.inr ()) (Sum.inl ⟨x, hxp, hxq⟩),
              ← attach_left δ p q r ⟨x, hxp, hxq⟩]
          · by_cases hyq : y = q
            · subst y
              rw [Phylogram.dist_comm,
                Phylo.graftPhylogram_dist_leaf_q δ hfpZ p q r hpq T' hxp hxq,
                hT'' (Sum.inr ()) (Sum.inl ⟨x, hxp, hxq⟩),
                ← attach_right δ hfpZ hpr hqr hmax ⟨x, hxp, hxq⟩]
            · rw [Phylo.graftPhylogram_dist_leaf_old δ hfpZ p q r hpq T' hxp hxq hyp hyq,
                hT'' (Sum.inl ⟨x, hxp, hxq⟩) (Sum.inl ⟨y, hyp, hyq⟩),
                shrinkVal_inl_inl]
  exact key (Fintype.card X) δ rfl h2 hfp

/-- ★★★★ **T3 收口（忠实形态）**：`2 ≤ |X|` + 四点条件（`PositiveDefinite` **不被使用**，
与 `InductiveAssembly` 的 (B') 同款）⇒ 存在二叉实现树满足 `bme_pauplin_identity_gap_binary`。

⚠ **与派单字面形态的差异（四要素）**：
① 旧字面形态：`∀ δ, δ.FourPoint → δ.PositiveDefinite → ∃ T, bme_pauplin_identity_gap_binary δ T`（**无基数前提**）
② 新形态（本定理）：同上**加** `2 ≤ Fintype.card X`
③ 依据：`Phylo/Buneman.lean:563` 的 `ExistsRealizingPhylogram` 与库内
   `Phylo.not_inductiveAssembly_without_card_hypothesis`（`InductiveAssembly.lean:150`）——
   同一处已判定「对**所有**有限类型量化是假命题」，须补 `Fintype.card ≠ 1`
④ 理由：`|X| = 1` 时 `Phylogram X` 为空（★★★ `bme_pauplin_identity_gap_binary_literal_form_false_of_card_eq_one`）；
   `|X| = 0` 时唯一实现树是单顶点树（度 `0`），`IsBinary` 假 ⇒ 字面形态不可证、
   加 `2 ≤ |X|` 是**唯一**忠实修正（且 `2 ≤ |X|` 强于库内用的 `|X| ≠ 1`，覆盖 `|X| = 0`）。

**★ W32：删去 `PositiveDefinite` 前提（定理加强）**（四要素）：
① 旧形态：`… (hfp : δ.FourPoint) (_hpos : δ.PositiveDefinite) : ∃ T, bme_pauplin_identity_gap_binary δ T`；
② 新形态：`… (hfp : δ.FourPoint) : ∃ T, bme_pauplin_identity_gap_binary δ T`
   —— **前提 `_hpos` 被删**，名字与其余签名（含 `h2`、`hfp`）逐字不变；
③ 文献依据/库内先例：`Phylo/AttesonRadius.lean:857`（「证明连 `PositiveDefinite` 都不需要
   （只用 `FourPoint` 与 `4 ≤ |X|`）」）、`Phylo/Buneman.lean:93-96`（**不需要** `PositiveDefinite`
   的无条件收口）、`Phylo/DissimilarityPerturb.lean:332`（`h : δ.PositiveDefinite`「保留只为签名兼容」）；
   且 PD **在收缩下不保持**：`Phylo/BunemanShrinkPD.lean:12-18` 的阴性结论 ＋ ★★★
   `not_positiveDefinite_shrinkDissimilarity`（同文件 `:92`，机器反例 `starWitness`，
   `δ'(inl 3, inr()) = 0` 而两点不等）⇒ 它本不该出现在 Buneman 递推中途；
④ 理由：本定理证明体（`:341-342`）只调 `exists_binary_realizingPhylogram`，
   **从未引用** `_hpos`；`PositiveDefinite` 与 `FourPoint` **互不蕴含**（`Dissimilarity` 允许
   `δ(x,y) = 0` 而 `x ≠ y`，零边权树度量即例）⇒ 删前提是**严格加强**。
   **不违反 ★C**：★C 禁的是**加**前提或**削弱**结论，删前提只加强定理。 -/
theorem bme_pauplin_identity_gap_binary_holds (δ : Dissimilarity X) (h2 : 2 ≤ Fintype.card X)
    (hfp : δ.FourPoint) :
    ∃ T : Phylogram.{u, u} X, bme_pauplin_identity_gap_binary δ T := by
  obtain ⟨T, hbin, hreal⟩ := exists_binary_realizingPhylogram δ h2 hfp
  exact ⟨T, bme_pauplin_identity_gap_binary_of_isBinary δ T hbin hreal⟩

/-- ★★★★ **BME 分解（四点条件形态，无 `PositiveDefinite`）**：`2 ≤ |X|` ＋ `FourPoint`
⇒ 存在边集 `E`（`Type 0`）、关联 `S`、边权 `l`、拓扑距离 `p` 使三条合取成立
（可加性 / 指示和 = `p` / Pauplin 归一化）—— 即 `def bme_pauplin_identity_gap`
（`Phylo/BMELeastSquares.lean`）的 ∃-体**脱离 `def` 前提**后的更强形态。

**W32（定理加强）**：只需 `2 ≤ |X|` 与 `FourPoint`，**不需要** `PositiveDefinite`
（`bme_pauplin_identity_gap_of_normalization` 的证明体 `intro _hFP _hPD` 把两者皆弃用；
`PositiveDefinite` 与 `FourPoint` 互不蕴含，且 PD 在**收缩下不保持**：
`Phylo/BunemanShrinkPD.lean:12-18` 与 ★★★ `not_positiveDefinite_shrinkDissimilarity`（`:92`））。
路线：`exists_binary_realizingPhylogram δ h2 hfp` 取**二叉**实现树 `T`，
二叉 ⇒ `BmePauplinNormalization T`（★★★ `bmePauplinNormalization_of_isBinary`），
再喂进 ★★★★ `exists_bmeDecomposition_of_normalization`。
★ 命名**刻意不含** `gap`/`Gap`：它不是缺口，而是缺口的**结论内容**（旧 `def` 逐字未动，★C）。 -/
theorem exists_bmeDecomposition_of_fourPoint (δ : Dissimilarity X) (h2 : 2 ≤ Fintype.card X)
    (hfp : δ.FourPoint) :
    ∃ (E : Type) (_ : Fintype E) (S : X → X → E → ℝ) (l : E → ℝ) (p : X → X → ℕ),
      (∀ i j : X, δ.val i j = ∑ e : E, S i j e * l e) ∧
      (∀ i j : X, i ≠ j → (∑ e : E, S i j e) = (p i j : ℝ)) ∧
      (∀ e : E, ∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e = 2) := by
  obtain ⟨T, hbin, hreal⟩ := exists_binary_realizingPhylogram δ h2 hfp
  exact exists_bmeDecomposition_of_normalization δ T hreal
    (bmePauplinNormalization_of_isBinary T hbin)

/-! ## §4 字面形态的反例（`|X| = 1`） -/

/-- ★★★ **字面形态的反例**：派单把目标写成「`∀ δ, … → ∃ T, …`」，
但 `|X| = 1` 时 `Phylogram X` 是**空类型**（`Phylo.not_nonempty_phylogram_of_subsingleton`）
⇒ 后件恒假 ⇒ 前件全真（`δ ≡ 0`）故整个命题假。忠实形态须带 `2 ≤ Fintype.card X`。

★ 库内同款先例：`Phylo.not_inductiveAssembly_without_card_hypothesis`
（`InductiveAssembly.lean:150`）—— 同一现象、同一修正。 -/
theorem bme_pauplin_identity_gap_binary_literal_form_false_of_card_eq_one :
    ¬ (∀ (δ : Dissimilarity (Fin 1)), δ.FourPoint → δ.PositiveDefinite →
        ∃ T : Phylogram.{0, 0} (Fin 1), bme_pauplin_identity_gap_binary δ T) := by
  intro h
  let δ : Dissimilarity (Fin 1) :=
    { val := fun _ _ => 0, symm := fun _ _ => rfl, diag := fun _ => rfl }
  have hfp : δ.FourPoint := fun _ _ _ _ => Or.inl (by simp [δ])
  have hpos : δ.PositiveDefinite := fun x y _ => Subsingleton.elim x y
  obtain ⟨T, -⟩ := h δ hfp hpos
  exact Phylo.not_nonempty_phylogram_of_subsingleton (Y := Fin 1) ⟨T⟩

end NJ.Dissimilarity
