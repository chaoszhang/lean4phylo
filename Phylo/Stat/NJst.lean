/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJHardCore
import Phylo.DissimilarityPerturb
import Phylo.InductiveAssembly
import Phylo.Stat.MSC

/-!
# `Phylo.Stat.NJst` —— NJst（USTAR/NJ）的统计一致性（T0.4）

**NJst**（Liu–Yu 2011）用**基因树的平均距离**跑 NJ 恢复物种树；不依赖任何度量信息，
只依赖基因树**拓扑**。文献：**Allman–Degnan–Rhodes 2016**（下称 **ADR**，arXiv:1604.05364）
把它重命名为 **USTAR/NJ**，并在 **Thm 4.1 / 4.2** 下证明其统计一致性。

## 本文件的内容

1. `structure NJstData` —— ADR 的输入，逐条**显式化**（出处见下「诚实边界」）；
2. ★★ `NJstData.fourPoint` —— **式 (4)(5)**：由 STAR 侧的四点条件（式 (4)）加**挂边修正**（式 (2)(3)）
   推出 USTAR 相异度 `δ` 的四点条件（经 `Phylo/DissimilarityPerturb.lean` 的 ★★ `fourPoint_of_pendant`）；
3. ★★★ `NJstData.core` + ★ `njst_cherry` —— NJ 硬核 `MaxZCherryCore` 现在是**定理**
   （由 ★★ `HasPositiveRealization` 经 ★★★ `maxZCherryCore_of_hasPositiveRealization` 推出），
   故 ★ `njst_cherry`（`Q` 最小的对是真树的 cherry = NJ 迭代的**归纳基例**）**不再有 `hcore` 假设**；
4. ★★★ `njst_statisticallyConsistent` —— **ADR Thm 4.1 的证明骨架**（条件 (1)(2) + 公理化的 SLLN）。

## 诚实边界（三层分清：文献照抄 / 显式假设 / 工程桥）

* **文献照抄**：挂边修正的代数（ADR 式 (2)(3)(5)，见 `Phylo/DissimilarityPerturb.lean` §6）；
  Thm 4.1 的论证结构（SLLN + 条件 (1)(2) ⇒ 最终返回正确拓扑；ADR `:754–763`）。
* **显式假设**（文献结论，但其依赖层**不在本库**）：
  - `starFourPoint : δr.FourPoint` —— ADR **式 (4)**；出处是 **[4] = ADR 2013
    *Generalizations* 的 Theorem 3.2**（`AllmanDegnanRhodes2013_STARGeneralizations.md:548–557`：
    MSC 下 `E_σ(D^r_{T^r})` **超度量强拟合**有根物种树）—— **STAR 层未形式化**；
  - `T` / `hT_pos` / `hT_dist`（合起来即 ★★ `Dissimilarity.HasPositiveRealization δ`，
    见 ★★ `NJstData.hasPositiveRealization`）—— ADR **Thm 4.2 的树层结论**：`D` 由物种树拓扑
    **各边全正**地实现（内部边 = STAR 的内部边 `> 0`，挂边 = `1`）。⚠️ 它**不能**由 `δ.FourPoint`
    （即使再加 `PositiveDefinite`）推出：取 5 元树 `((a,b),(c,d))` 各边 `1`、把 `x` 以 **`0` 权挂边**
    挂在中心点，则四个 quartet **全部解析** ⇒ 拓扑被四点条件钉死 ⇒ 边长的线性方程组唯一解把 `x` 的
    挂边逼成 `0` ⇒ **无**全正实现树；
  - `hT_binary : T.toCladogram.IsBinary` —— ADR `:193–195` 的 "binary metric tree" 的**拓扑**一半
    （另一半「内部边长全正」由 `hT_pos` 覆盖）。
* **工程桥**（本库自创，非文献内容）：`DissClose`（相异度的逐点 `ε`-接近）、`USTARSampling`
  （**公理化的大数定律**）、`ReturnsFittingTree` / `ContinuousAtBinaryTreeMetrics`
  （把 ADR 条件 (1)(2) 写成 `def`）。
  ⚠️ `USTARSampling.converges` 是**公理层**：把「几乎必然收敛」抽象成「最终 `ε`-接近」，
  **不得**读成真·依概率一致性（同一取舍见 `Phylo/Stat/MSC.lean:157–167`）。
* **不在本批**：ADR 式 (6)(7) / Thm 5.1（split 概率决定 `E_µ(D_T)`；需新建「有限树分布 + 期望」层）、
  Cor 5.2、「NJ 满足条件 (1)(2)」（**不在 ADR 内**：ADR `:622–623` 只是**引用**；形式化它须先写出
  NJ 算法本体，属独立工程）、§6 多样品（含式 (8)）。
* ⚠️ **非空见证是退化的**：`njstDataFin2` 在 `|X| = 2` 上给出实例（`δr` = 零相异度、`w ≡ 0`、
  `δ` = 正权双叶树的距离），它证明**字段集相容（可居留）**，但 `hT_binary` 在 `|X| = 2` 上是**空真**的；
  **非退化**的 `12|34`（各边 `1`）见证需要新建一棵 ≥3 叶的**具体正权** `Phylogram`
  （库内暂无此器械：`twoLeafPhylogram` 只到 2 叶；`Laminar.toCladogram` 只给拓扑、无 `w`/`dist` 记账），
  估 150–300 行，**单列一批**。
-/

universe u v

open NJ

variable {X : Type u} [Fintype X] [DecidableEq X]

noncomputable section

/-- ★★ **ADR 2016 的 NJst（USTAR）输入数据**（每条假设的出处见模块文档）。

* `δ` —— USTAR 相异度 `D = E_σ(D_T)`；
* `δr` / `w` / `ustar` —— STAR 相异度 `D^r` 与式 (2)(3) 的**挂边修正**关系；
* `T` / `hT_binary` / `hT_pos` / `hT_dist` —— 真物种树的**正权 binary 实现**（Thm 4.2 的树层结论）；
* `starFourPoint` —— 式 (4)（STAR 侧的四点条件）。 -/
structure NJstData (X : Type u) [Fintype X] [DecidableEq X] where
  /-- USTAR 相异度 `D = E_σ(D_T)`（ADR §3，`:228–242`）。 -/
  δ : Dissimilarity X
  /-- STAR 相异度 `D^r = E_σ(D^r_{T^r})`（ADR 式 (1) 的上标 `r`）。 -/
  δr : Dissimilarity X
  /-- `w x = E_σ(w_x)`：根被抑制后 `x` 的挂边长度的期望（ADR 式 (2)(3)）。 -/
  w : X → ℝ
  /-- ★ **式 (2)(3)**：`D(x,y) = D^r(x,y) + (1 − w x) + (1 − w y)`（`x ≠ y`）——
  即 ★★ `IsPendantCorrected δ δr (fun x => 1 - w x)`。 -/
  ustar : Dissimilarity.IsPendantCorrected δ δr (fun x => 1 - w x)
  /-- 真物种树的**正权实现**（ADR Thm 4.2 的树层结论）。 -/
  T : Phylogram.{u, v} X
  /-- ★ 实现树的拓扑是 **binary**（ADR `:193–195` 的拓扑一半）。 -/
  hT_binary : T.toCladogram.IsBinary
  /-- ★ 实现树**各边权全正**（ADR `:193–195` 的另一半；Weller 2023 Thm 2 与
  ★★★ `maxZCherryCore_of_exists_pos` 的前提）。 -/
  hT_pos : ∀ e : Edge T.toCladogram, 0 < T.w e
  /-- ★ 实现树在叶上给出 `δ`（距离相等）。 -/
  hT_dist : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y
  /-- ★ **式 (4)**：STAR 相异度满足四点条件（出处 = [4] ADR 2013 Thm 3.2，未形式化）。 -/
  starFourPoint : δr.FourPoint

namespace NJstData

variable (M : NJstData.{u, v} X)

/-- 真物种树的底层 cladogram（投影别名；`M.tree` 与 `M.T.toCladogram` 定义上相同）。 -/
abbrev tree (M : NJstData.{u, v} X) : Cladogram.{u, v} X := M.T.toCladogram

/-- ★★ **各边全正的实现树**（= ★★ `Dissimilarity.HasPositiveRealization`，T0.3 的打包命题名）。

它同时含两件事：**边权全正**（`hT_pos`）与**距离相等**（`hT_dist`）。 -/
theorem hasPositiveRealization : Dissimilarity.HasPositiveRealization.{u, v} M.δ :=
  ⟨M.T, M.hT_pos, M.hT_dist⟩

/-- ★★ **`δ` 的三角不等式**（由实现树的 ★★ `Phylogram.dist_triangle` 给出）。 -/
theorem triangle (a k l : X) : M.δ.val k l ≤ M.δ.val a k + M.δ.val a l := by
  have h := Phylogram.dist_triangle M.T (M.T.leaf k) (M.T.leaf a) (M.T.leaf l)
  rw [Phylo.TreeDist.dist_comm M.T (M.T.leaf k) (M.T.leaf a)] at h
  rw [← M.hT_dist k l, ← M.hT_dist a k, ← M.hT_dist a l]
  exact h

/-- ★★ **式 (4)(5)**：由 STAR 侧的四点条件（式 (4)）与挂边修正（式 (2)(3)）推出 `δ` 的四点条件。

* 四个标签互异：三对和同加 `(1-w a)+(1-w b)+(1-w c)+(1-w d)` ⇒ 用
  ★★ `fourSum_sub_eq_of_pendant` 把 `δr.FourPoint` 搬到 `δ`；
* 有重复下标：用 ★★ `triangle`（ADR `:737–746` 用「每个 `D_T` 都是树度量」另行处理该情形）。 -/
theorem fourPoint : M.δ.FourPoint :=
  Dissimilarity.fourPoint_of_pendant M.ustar M.starFourPoint M.triangle

/-- ★★★ **NJ 硬核 `MaxZCherryCore` 是定理**（T0.3 验收项：该 `def` 不再作为假设出现在下游）。

由 ★★ `hasPositiveRealization` + ★★★ `maxZCherryCore_of_hasPositiveRealization` 直接给出。 -/
theorem core : M.δ.MaxZCherryCore :=
  Dissimilarity.maxZCherryCore_of_hasPositiveRealization.{u, v} M.δ M.hasPositiveRealization

/-- ★ **NJst 的第一步正确**：`Q` 最小的叶对（等价地 `z` 最大）是真树的 cherry。

这是 NJ 迭代算法的**归纳基例**。 -/
theorem njst_cherry (a b : X) (hab : a ≠ b)
    (hmin : ∀ i j : X, i ≠ j → M.δ.Q a b ≤ M.δ.Q i j) : M.δ.IsCherry a b :=
  M.δ.nj_cherry M.core M.fourPoint a b hab hmin

/-- **四点条件可传**（便于下游直接引用）。 -/
theorem four_point (a b c d : X) :
    M.δ.val a b + M.δ.val c d ≤ M.δ.val a c + M.δ.val b d
    ∨ M.δ.val a b + M.δ.val c d ≤ M.δ.val a d + M.δ.val b c :=
  M.fourPoint a b c d

end NJstData

/-! ## ADR Thm 4.1：统计一致性的骨架

ADR Thm 4.1（`:604–616`）说：若方法 `M`（1）对树度量返回**唯一**拟合树、且（2）在
**binary 树度量**处**连续**，则 `USTAR/M` 在 MSC 下对 binary 物种树**统计一致**。
其证明（`:754–763`）只有两步：**SLLN**（经验 USTAR 相异度 → 理论值 `D`）+「**(1)+(2)**」。

下面把条件 (1)(2) 写成 `def`（**不是**新 `axiom`），把 SLLN 公理化进 `structure USTARSampling`
（形制同 `MSCSampling`），得到 ★★★ `njst_statisticallyConsistent`。 -/

/-- **相异度的逐点 `ε`-接近**（工程桥：`Dissimilarity` 上的「距离」）。 -/
def DissClose (δ δ' : Dissimilarity X) (ε : ℝ) : Prop :=
  ∀ x y : X, |δ.val x y - δ'.val x y| < ε

/-- ★★ **（公理化）USTAR 相异度的采样 + 大数定律**。

* `emp M n` —— 在**真实模型 `M`** 下、`n` 棵基因树给出的**经验** USTAR 相异度；
* `converges` —— **公理化的 SLLN**：在模型 `M` 下，经验相异度最终 `ε`-接近理论值 `M.δ`。

📌 **形状说明（2026-10-09 修正）**：`emp` **必须依赖真实模型 `M`**。
早期版本写成 `ℕ → Dissimilarity X`（不依赖 `M`），而 `converges` 却对**所有**
`M : NJstData X` 断言 —— 只要有两个模型的 `δ` 在某点不同，要求即自相矛盾，
该结构因此是**空类型**（历史上由 `Phylo.Stat.SamplingAxiomVacuity` 证明）。
现按「在真实模型下采样」的语义修正，并由 `ustarSampling_nonempty` 给出显式居民。

⚠️ **公理层**：形制同 `MSCSampling.converges`（`Phylo/Stat/MSC.lean`），
把「**几乎必然**收敛」抽象成「**最终** `ε`-接近」的确定性形式；**不得**读成真·依概率一致性
（把 `converges` 换成真概率陈述即课题 `Phylo.Stat.MSCProof`）。 -/
structure USTARSampling (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 在**真实模型 `M`** 下，`n` 棵基因树的经验 USTAR 相异度。 -/
  emp : NJstData.{u, v} X → ℕ → Dissimilarity X
  /-- ★ **公理化的 MSC 大数定律**：在模型 `M` 下，经验相异度收敛到理论值 `M.δ`。 -/
  converges : ∀ M : NJstData.{u, v} X, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, DissClose (emp M n) M.δ ε

/-- ★★★ **`USTARSampling` 非空洞**（理想样本 `emp M n := M.δ`）。 -/
theorem ustarSampling_nonempty (X : Type u) [Fintype X] [DecidableEq X] :
    Nonempty (USTARSampling.{u, v} X) :=
  ⟨{ emp := fun M _ => M.δ
     converges := fun M ε hε =>
       ⟨0, fun _ _ x y => by
         show |M.δ.val x y - M.δ.val x y| < ε
         rw [sub_self, abs_zero]
         exact hε⟩ }⟩

/-- **ADR Thm 4.1 条件 (1)**：`M` 对树度量返回**唯一**拟合树
（`M δ` 与**任何**实现 `δ` 的树同构）。 -/
def ReturnsFittingTree (E : Dissimilarity X → Cladogram.{u, v} X) : Prop :=
  ∀ (δ : Dissimilarity X) (T : Phylogram.{u, v} X),
    (∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) →
      Nonempty (Iso (E δ) T.toCladogram)

/-- **ADR Thm 4.1 条件 (2)**：`M` 在「拓扑 binary **且**内部边长全正」的**树度量**处，
**输出拓扑局部常值**（这就是「连续性」在**离散输出**下的含义 —— ADR `:618–621` 的
"returns the correct tree topology, and edge lengths close to those underlying the tree metric"；
「正确」由条件 (1) 提供，故此处**不**写进条件 (2)）。

⚠️ `IsBinary`（拓扑）与 `0 < w`（**正边权**）**分开写**，对应 ADR `:193–195` 对
"binary metric tree" 的两半定义；正边权**不可省**（否则分段常值方法会混进来）。 -/
def ContinuousAtBinaryTreeMetrics (E : Dissimilarity X → Cladogram.{u, v} X) : Prop :=
  ∀ (T : Phylogram.{u, v} X) (δ : Dissimilarity X),
    T.toCladogram.IsBinary → (∀ e : Edge T.toCladogram, 0 < T.w e) →
    (∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ' : Dissimilarity X, DissClose δ' δ ε →
      Nonempty (Iso (E δ') (E δ))

/-- ★★★ **ADR 2016 Thm 4.1（NJst / USTAR-NJ 统计一致性的骨架形式）**。

设 `sm` 是 USTAR 采样的公理化大数定律、`E` 是任一满足条件 (1)(2) 的树选择方法
（NJ 是其中之一 —— ADR `:622–623` 是**引用**，不在 ADR 内证明），`M` 是 `NJstData`
（其 `T` 是物种树的正权 binary 实现），则**最终** `E` 在经验相异度上输出与物种树同构的树。

**证明**（照抄 ADR `:754–763`）：`M.T` 是 `δ` 的一个正权 binary 实现
⇒ 条件 (2) 给 `ε > 0` 与局部常值 ⇒ 条件 (1) 在 `δ` 上给 `E δ ≅ M.tree`；
再由 SLLN 取 `N` ⇒ `E (emp n) ≅ M.tree`（`Iso.trans`）。 -/
theorem njst_statisticallyConsistent (sm : USTARSampling.{u, v} X) (M : NJstData.{u, v} X)
    (E : Dissimilarity X → Cladogram.{u, v} X)
    (h1 : ReturnsFittingTree E) (h2 : ContinuousAtBinaryTreeMetrics E) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp M n)) M.tree) := by
  obtain ⟨ε, hε, hcont⟩ := h2 M.T M.δ M.hT_binary M.hT_pos M.hT_dist
  obtain ⟨N, hN⟩ := sm.converges M ε hε
  have hδ : Nonempty (Iso (E M.δ) M.tree) := h1 M.δ M.T M.hT_dist
  refine ⟨N, fun n hn => ?_⟩
  have hn' : Nonempty (Iso (E (sm.emp M n)) (E M.δ)) := hcont (sm.emp M n) (hN n hn)
  exact ⟨hn'.some.trans hδ.some⟩

/-! ## 非空见证（**退化**：`|X| = 2`）

⚠️ 本见证只证明 `NJstData` 的**字段集相容（可居留）**：`δr` 取**零相异度**、`w ≡ 0`、
`δ` 取**正权双叶树**的距离。**非退化**的 `12|34` 见证（各边 `1`）需要库内**暂无**的
「≥3 叶的具体正权 `Phylogram`」器械，见模块文档末。 -/

/-- `Fintype.card (Fin 2) = 2`（**命名一次**，保证见证各处用的是同一个证明项）。 -/
theorem twoLeafCard : Fintype.card (Fin 2) = 2 := by decide

/-- `(0 : ℝ) ≤ 2`（同上，命名一次）。 -/
theorem twoLeafNonneg : (0 : ℝ) ≤ 2 := by norm_num

/-- 正权双叶树（两叶一条边，边权 `2 > 0`）。 -/
abbrev twoLeafP : Phylogram.{0, 0} (Fin 2) :=
  Phylo.twoLeafPhylogram twoLeafCard 2 twoLeafNonneg

/-- 零相异度。 -/
abbrev zeroDissim : Dissimilarity (Fin 2) :=
  { val := fun _ _ => 0, symm := fun _ _ => rfl, diag := fun _ => rfl }

/-- 正权双叶树的距离相异度（非对角恒为 `2`）。 -/
abbrev twoLeafDissim : Dissimilarity (Fin 2) :=
  { val := fun x y => twoLeafP.dist (twoLeafP.leaf x) (twoLeafP.leaf y)
    symm := fun x y => Phylo.TreeDist.dist_comm twoLeafP (twoLeafP.leaf x) (twoLeafP.leaf y)
    diag := fun x => Phylogram.dist_self twoLeafP (twoLeafP.leaf x) }

/-- 双叶树距离的显式形式：同一标签给 `0`，不同标签给 `2`。 -/
theorem twoLeafP_dist (x y : Fin 2) :
    twoLeafP.dist (twoLeafP.leaf x) (twoLeafP.leaf y) = if x = y then 0 else 2 :=
  Phylo.twoLeafPhylogram_dist twoLeafCard 2 twoLeafNonneg x y

/-- ★★ **非空见证（退化）**：`|X| = 2` 上 `NJstData` 的字段集**相容（可居留）**。

⚠️ 退化之处：`δr` 是零相异度、`w ≡ 0`；并且 `hT_binary` 在 `|X| = 2` 上（没有内部顶点）
是**空真**的。见模块文档末的说明。 -/
abbrev njstDataFin2 : NJstData.{0, 0} (Fin 2) where
  δ := twoLeafDissim
  δr := zeroDissim
  w := fun _ => 0
  ustar := by
    intro x y h
    have h2 : twoLeafDissim.val x y = 2 := by
      show twoLeafP.dist (twoLeafP.leaf x) (twoLeafP.leaf y) = 2
      rw [twoLeafP_dist]
      simp [h]
    rw [h2]
    norm_num [zeroDissim]
  T := twoLeafP
  hT_binary := by
    intro v hv
    have h1 : twoLeafP.graph.degree v = 1 :=
      Phylo.degree_top_eq_one_of_card_eq_two twoLeafCard v
    exact absurd (Cladogram.degree_eq_one_isLeaf (T := twoLeafP.toCladogram) h1) hv
  hT_pos := by
    intro e
    have hw : twoLeafP.w e = 2 := rfl
    rw [hw]
    norm_num
  hT_dist := fun _ _ => rfl
  starFourPoint := fun _ _ _ _ => Or.inl (by simp)

end
