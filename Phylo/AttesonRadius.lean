/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Algorithm.NJHardCore
import Phylo.Buneman
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Phylo.Split
import Phylo.InternalEdge
import Phylo.TreeDistance

/-!
# `Phylo.AttesonRadius` —— Atteson 安全半径 `1/2`（W11g · D1）

## 文献与逐行依据

`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md`
（K. Atteson, *The Performance of Neighbor-Joining Methods of Phylogenetic Reconstruction*,
Algorithmica 25:251–278 (1999)）。本文件所有行号都指该 md 文件。

* **Definition 3**（`:187–197`）：`‖D̃ − D̃'‖_∞ = max_{i,j} |D̃_ij − D̃'_ij|`；
  `:192–206`：方法 `f` 有 **l₁ radius `β`**，若对每个加权二叉树 `τ` 及每个满足
  `‖D_τ − D̃‖_∞ < β · min_{e∈E(T_τ)} l(e)` 的距离矩阵 `D̃` 都有 `f(D̃) = T_τ`。
* **Lemma 3**（`:276–288`）：**没有**方法有 l₁ radius `> 1/2`（`1/2` 最优）。
* **Definition 4**（`:335–346`）：`D̃` 对 `τ` **nearly additive**，若
  `‖D̃ − D_τ‖_∞ < min_{e∈E(T_τ)} l(e) / 2`。 ← **本文件的 `safeRadius`**
* **Lemma 1**（`:160–172`）：四点条件 —— `D` 可加 ⟺ 任意四点可标号为 `i,j,k,l` 使
  `D_ij + D_kl ≤ D_ik + D_jl = D_il + D_jk`。
* **Lemma 6**（`:677–694`）：可加矩阵上合并一对**邻居** `i,j`（更新式 (6)，`:611`）仍得可加矩阵，
  对应「删去 `i,j`」的树；边权由式 (7)（`:688–694`）给出。
* **Lemma 7**（`:749–751`）：`‖D̃_m − D_m‖_∞ ≤ ‖D̃ − D‖_∞`（归约**不放大**扰动）。
* **Theorem 1**（`:868–916`）：若 NJ 方法 (1) 在近可加输入下优化判据的对必是邻居、(2) 用更新式 (6)，
  则输出 `T_τ`，即 **l₁ radius `1/2`**。证明用三个同时成立的归纳不变量
  (a) `D_m` 可加、(b) `min_e l_m(e) ≥ min_e l_1(e)`、(c) 第 `m` 步所选对是邻居。
* **式 (12)**（`:1751–1755`）：NJ 判据 `S_{i,j} = (n−2)D_ij − Σ_k D_ik − Σ_k D_jk`（**最小化**）。
  ← **本库 `Dissimilarity.Q`（`Phylo/Algorithm/NJ.lean:88`）就是它。**
* **Lemma 8**（`:1030–1033`）：`‖D̃ − D_τ‖_∞ = "` 且边 `e` 分离 `i,j` 与 `k,l` ⇒
  `i,j` 赢四点的条件（`" < l(e)` 的定量版）。
* **Lemma 10**（`:1774–1804`）：`S_{i,j} = Σ_{e∈E} w_e(i,j)·l(e)`，其中
  `w_e(i,j) = −2`（`e ∈ P_{i,j}`）、`= −2|L − L_i(e)|`（否则）。
* **Lemma 11**（`:1989–2009`）：`k,l` 不是邻居 ⟹ 存在邻居对 `i,j` 使
  `S_{k,l} − S_{i,j} ≥ 3(n−4)·min_e l(e)`（两对不交）或 `≥ 2(n−3)·min_e l(e)`（恰交一个标签）。
* **Lemma 12 / 式 (16)**（`:2181–2201`）：证明的关键是**扰动抵消**：
  `(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) = (n−2)(ε_kl − ε_ij) + Σ_m (ε_im + ε_jm − ε_km − ε_lm)`，
  其中 `ε_ab = D̃_ab − D_ab`。**朴素估计 `|Ŝ_kl − S_kl| ≤ (3n−2)ε` 会给出错误（更小）的半径**——
  抵消把 `n` 降回 `n−4`，正是 `1/2` 得以取到的原因。
* **Theorem 4**（`:2263–2303`）：**NJ has l₁ radius `1/2`**。证明：
  `Ŝ_kl − Ŝ_ij = [Ŝ_kl − S_kl + S_ij − Ŝ_ij] + [S_kl − S_ij] ≥ −6(n−4)ε + 3(n−4)·min_e l(e)
  = 3(n−4)(min_e l(e) − 2ε) > 0`，故第一轮必选邻居对，再由 Lemma 1 收口。

## 本文件证了什么 / 缺什么

✅ **已证（零 `sorry` / 零 `axiom` / 零 `native_decide`）**

* ★★★ `qPerturb_cancel`：**Atteson 式 (16) 的精确恒等式**（`:2195–2201`）；
* ★★★ `qPerturb_reduced` / `qPerturb_reduced_ik`：把上式化简成
  `(n−4)(ε_kl − ε_ij) + Σ_{m ∉ {i,j,k,l}} (…)`（`n=4` 时**恒为 0**）；
* ★★ `qPerturb_bound_disjoint` / `qPerturb_bound_shared`：**Lemma 12 的两条界**
  `≥ −6(n−4)ε`（`:2183`）与 `≥ −4(n−3)ε`（`:2187`）；
* ★★★ `njCriterion_minimizer_is_cherry`：**「`ε < safeRadius δmin` ⟹ NJ 第一轮判据的
  任何最小点都是真树的一颗樱桃」**（`n ≥ 5`；Theorem 4 的第一步，`:2266–2303`）；
* ★★★ `njCriterion_minimizer_is_cherry_card_four`：`n = 4` 版本（只用「恰交一个标签」分支）；
* ★★ `qPerturb_cancel_of_card_four`：`n = 4` 时 `Q` 的**排序在不相交对上完全不受扰动影响**；
* ★★ `linfClose_update`：**Lemma 7 的一步形式**（`:749–751`，更新式 (6) 不放大 `L∞` 扰动）；
* ★C `Fin 4` 显式数值例子：挂边 `1,2,3,4`、内部边 `5`，真矩阵与扰动矩阵上
  `Q` 的最小点都恰是两颗樱桃。

⚠️ **缺口（落成 `Prop`，都不是数学缺口，是本库的工程缺口）**

* `IsCherrySeparated`：**Atteson Lemma 11 的度量版**（`:1989–2009`）—— 本文件唯一的非纯代数假设；
* `atteson_lemma11_gap_order_form`：上述假设对树度量的**可实现性**；
* `atteson_reduction_gap`：**Atteson Lemma 6 的归约步**（`:677–694`）—— 需要类型迁移
  `X ↝ (X \ {i,j}) ∪ {u}` 与实现树层的「合并樱桃」算子。

-/

open Finset
open scoped BigOperators

noncomputable section

namespace NJ

namespace Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 0. 安全半径与「接近」谓词 -/

omit [Fintype X] [DecidableEq X] in
/-- **安全半径** `½ · δmin`（Atteson1999 Definition 3/4，`:201–204`、`:340–346`）。

`δmin` 取真加权二叉树 `τ` 的**最短边长** `min_{e∈E(τ)} l(e)`。Atteson 的结论是
（Theorem 4，`:2263`）：`‖D̃ − D_τ‖_∞ < safeRadius δmin` 时 NJ 仍输出 `τ` 的形状；
且 `1/2` 是**最优**常数（Lemma 3，`:276`）。 -/
def safeRadius (δmin : ℝ) : ℝ := δmin / 2

/-- **L∞ 接近**：`‖δ' − δ‖_∞ ≤ ε`（Atteson1999 Definition 3，`:187–197`）。 -/
def IsLinfClose (δ δ' : Dissimilarity X) (ε : ℝ) : Prop :=
  ∀ i j : X, |δ'.val i j - δ.val i j| ≤ ε

/-- **近可加**（Atteson1999 Definition 4，`:335–346`）：`‖δ' − δ_τ‖_∞ ≤ ε` 且
`ε < safeRadius δmin = δmin/2`。 -/
def NearlyAdditive (δ δ' : Dissimilarity X) (δmin ε : ℝ) : Prop :=
  IsLinfClose δ δ' ε ∧ ε < safeRadius δmin

omit [Fintype X] [DecidableEq X] in
/-- `{i,j}` 与 `{k,l}` **完全不相交**（Atteson1999 Lemma 12 第一式的情形，`:2183–2185`）。 -/
def DisjointPairs (i j k l : X) : Prop :=
  i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l

omit [Fintype X] [DecidableEq X] in
/-- `{i,j}` 与 `{k,l}` **恰交于一个标签**（Atteson1999 Lemma 12 第二式的情形，`:2187–2189`）。

四种形态各自带上后续证明所需的互异性（`i ≠ j`、`k ≠ l` 在调用处另行给出）。 -/
def SharesOneLabel (i j k l : X) : Prop :=
  (i = k ∧ j ≠ k ∧ j ≠ l) ∨ (i = l ∧ j ≠ k ∧ j ≠ l) ∨
  (j = k ∧ i ≠ k ∧ i ≠ l) ∨ (j = l ∧ i ≠ k ∧ i ≠ l)

/-- ★★ **Atteson Lemma 11 的度量版**（`:1989–2009`）—— 本文件**唯一的非纯代数假设**。

「若 `(k,l)` 不是真树 `τ` 的一颗樱桃，则存在 `τ` 的樱桃 `(i,j)`，使 NJ 判据 `Q` 在 `(k,l)` 处
比在 `(i,j)` 处至少大 `3(n−4)·δmin`（两对不交）或 `2(n−3)·δmin`（恰交一个标签）。」

✦ **为什么是假设**：Lemma 11 的证明先用 Lemma 10（`:1774–1804`）把 `Q(i,j)` 写成
`Σ_{e∈E} w_e(i,j)·l(e)`（权重只依赖拓扑），再逐边比较并使用「路径旁子树的叶数」单调性
（`:2023–2056`）。这需要**实现树 + 路径关联 + 子树叶数**这一层，本库尚未搭好。
可解性见 ★★ `atteson_lemma11_gap_order_form` 的说明。 -/
def IsCherrySeparated (δ : Dissimilarity X) (δmin : ℝ) : Prop :=
  ∀ k l : X, k ≠ l → ¬ δ.IsCherry k l →
    ∃ i j : X, δ.IsCherry i j ∧
      ((DisjointPairs i j k l ∧
          3 * ((Fintype.card X : ℝ) - 4) * δmin ≤ δ.Q k l - δ.Q i j) ∨
       (SharesOneLabel i j k l ∧
          2 * ((Fintype.card X : ℝ) - 3) * δmin ≤ δ.Q k l - δ.Q i j))

/-! ## 1. 有限和的拆解 -/

omit [DecidableEq X] in
/-- `∑ (a + b − c − d) = ∑a + ∑b − ∑c − ∑d`。 -/
theorem sum_four_sub (f g h k : X → ℝ) :
    (∑ m : X, (f m + g m - h m - k m))
      = (∑ m : X, f m) + (∑ m : X, g m) - (∑ m : X, h m) - (∑ m : X, k m) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

omit [Fintype X] in
/-- 三元集上的求和展开。 -/
theorem sum_three_elems (F : X → ℝ) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ m ∈ ({a, b, c} : Finset X), F m) = F a + (F b + F c) := by
  have h1 : a ∉ ({b, c} : Finset X) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset X) := by simp [hbc]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]

omit [Fintype X] in
/-- 四元集上的求和展开。 -/
theorem sum_four_elems (F : X → ℝ) {a b c d : X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ m ∈ ({a, b, c, d} : Finset X), F m) = F a + (F b + (F c + F d)) := by
  have h1 : a ∉ ({b, c, d} : Finset X) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset X) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset X) := by simp [hcd]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]

omit [Fintype X] in
/-- 三元集的基数。 -/
theorem card_three_elems (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset X).card = 3 := by
  have h1 : a ∉ ({b, c} : Finset X) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset X) := by simp [hbc]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]

omit [Fintype X] in
/-- 四元集的基数。 -/
theorem card_four_elems (a b c d : X) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset X).card = 4 := by
  have h1 : a ∉ ({b, c, d} : Finset X) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset X) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset X) := by simp [hcd]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- 从全体中挖掉 `s` 之后的基数。 -/
theorem card_sdiff_univ (s : Finset X) :
    ((Finset.univ : Finset X) \ s).card = Fintype.card X - s.card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

/-! ## 2. 扰动抵消：Atteson 式 (16)（`:2195–2201`） -/

omit [Fintype X] in
/-- ★★★ **四点指标集上的「四元组合和」精确值**（Atteson1999 `:2205–2221` 的化简）：

`Σ_{m ∈ {i,j,k,l}} (g_im + g_jm − g_km − g_lm) = 2·g_ij − 2·g_kl`（`g` 对称且零对角）。

**正是这一项**（连同 `(n−2)(ε_kl − ε_ij)`）把系数从 `n−2` 削到 `n−4` ——
安全半径 `1/2` 能否取到，全看这里。 -/
theorem sum_quartet_four (g : X → X → ℝ) (hsymm : ∀ a b, g a b = g b a) (hdiag : ∀ a, g a a = 0)
    {i j k l : X} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ m ∈ ({i, j, k, l} : Finset X), (g i m + g j m - g k m - g l m))
      = 2 * g i j - 2 * g k l := by
  rw [sum_four_elems (fun m => g i m + g j m - g k m - g l m) hij hik hil hjk hjl hkl]
  simp only [hdiag, zero_add, add_zero, sub_zero]
  rw [hsymm j i, hsymm k i, hsymm l i, hsymm k j, hsymm l j, hsymm l k]
  ring

omit [DecidableEq X] in
/-- ★ **NJ 判据 `Q` 的对称性**：`Q(i,j) = Q(j,i)`。

式 (12)（Atteson1999 `:1751–1755`）`S_{i,j} = (n−2)D_ij − Σ_k D_ik − Σ_k D_jk` 对 `i,j`
显然对称；本库 `Dissimilarity.Q` 即此式（`Phylo/Algorithm/NJ.lean:88`）。 -/
theorem Q_comm (δ : Dissimilarity X) (i j : X) : δ.Q i j = δ.Q j i := by
  simp only [Q]
  rw [δ.symm j i]
  ring

omit [DecidableEq X] in
/-- 单个 `Q` 的扰动展开（式 (16) 的左半，Atteson1999 `:2195–2201`）。 -/
theorem Q_perturb_pos (δ δ' : Dissimilarity X) (i j : X) :
    δ'.Q i j - δ.Q i j
      = ((Fintype.card X : ℝ) - 2) * (δ'.val i j - δ.val i j)
        - (∑ m : X, (δ'.val i m - δ.val i m))
        - (∑ m : X, (δ'.val j m - δ.val j m)) := by
  have e1 : (∑ m : X, δ'.val i m) - (∑ m : X, δ.val i m)
      = ∑ m : X, (δ'.val i m - δ.val i m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val i m) (g := fun m => δ.val i m)).symm
  have e2 : (∑ m : X, δ'.val j m) - (∑ m : X, δ.val j m)
      = ∑ m : X, (δ'.val j m - δ.val j m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val j m) (g := fun m => δ.val j m)).symm
  simp only [Q]
  linarith

omit [DecidableEq X] in
/-- 单个 `Q` 的扰动展开（式 (16) 的右半；取向与 `Q_perturb_pos` **相同**，
省去「`Σ(−f) = −Σf`」这一步）。 -/
theorem Q_perturb_neg (δ δ' : Dissimilarity X) (i j : X) :
    δ.Q i j - δ'.Q i j
      = -(((Fintype.card X : ℝ) - 2) * (δ'.val i j - δ.val i j))
        + (∑ m : X, (δ'.val i m - δ.val i m))
        + (∑ m : X, (δ'.val j m - δ.val j m)) := by
  have e1 : (∑ m : X, δ'.val i m) - (∑ m : X, δ.val i m)
      = ∑ m : X, (δ'.val i m - δ.val i m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val i m) (g := fun m => δ.val i m)).symm
  have e2 : (∑ m : X, δ'.val j m) - (∑ m : X, δ.val j m)
      = ∑ m : X, (δ'.val j m - δ.val j m) :=
    (Finset.sum_sub_distrib (f := fun m => δ'.val j m) (g := fun m => δ.val j m)).symm
  simp only [Q]
  linarith

omit [DecidableEq X] in
/-- ★★★ **Atteson 式 (16) 的精确恒等式**（`:2195–2201`），记 `ε_ab = δ'.val a b − δ.val a b`：

`(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) = (n−2)(ε_kl − ε_ij) + Σ_m (ε_im + ε_jm − ε_km − ε_lm)`。

这是整个安全半径证明的**命门**：右端第二项对 `m ∈ {i,j,k,l}` 的贡献恰为 `2ε_ij − 2ε_kl`
（见 ★★★ `sum_quartet_four`），与第一项合并后系数从 `n−2` 掉到 `n−4`。 -/
theorem qPerturb_cancel (δ δ' : Dissimilarity X) (i j k l : X) :
    (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 2)
          * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j))
        + ∑ m : X, ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
                    - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
  rw [Q_perturb_pos δ δ' k l, Q_perturb_neg δ δ' i j]
  rw [sum_four_sub]
  ring

/-- ★★★ **式 (16) 的「已化简」形式**：把 `m ∈ {i,j,k,l}` 的四项用
★★★ `sum_quartet_four` 算掉之后，剩下 `(n−4)(ε_kl − ε_ij)` 与一个**只跑
`m ∉ {i,j,k,l}`** 的和（Atteson1999 `:2205–2221`）。 -/
theorem qPerturb_reduced (δ δ' : Dissimilarity X) {i j k l : X}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 4) * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j))
        + ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
            ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
  have hS := sum_quartet_four (fun a b => δ'.val a b - δ.val a b)
    (fun a b => by rw [δ.symm a b, δ'.symm a b])
    (fun a => by rw [δ.diag a, δ'.diag a, sub_self])
    hij hik hil hjk hjl hkl
  have hsplit := Finset.sum_sdiff (s₁ := ({i, j, k, l} : Finset X))
    (s₂ := (Finset.univ : Finset X))
    (f := fun m => ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)))
    (Finset.subset_univ _)
  rw [qPerturb_cancel δ δ' i j k l, ← hsplit, hS]
  ring

/-- ★★ **`i = k` 时的化简**（Atteson1999 Lemma 12 第二种情形 `:2223–2252`）。 -/
theorem qPerturb_reduced_ik (δ δ' : Dissimilarity X) {i j l : X}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (δ'.Q i l - δ.Q i l) + (δ.Q i j - δ'.Q i j)
      = ((Fintype.card X : ℝ) - 3)
          * ((δ'.val i l - δ.val i l) - (δ'.val i j - δ.val i j))
        + ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
            ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
  have h1 : (∑ m : X, ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
              - (δ'.val i m - δ.val i m) - (δ'.val l m - δ.val l m)))
      = ∑ m : X, ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
    refine Finset.sum_congr rfl ?_
    intro m _
    ring
  rw [qPerturb_cancel δ δ' i j i l, h1]
  have h3 : (∑ m ∈ ({i, j, l} : Finset X),
        ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)))
      = (δ'.val i j - δ.val i j) - (δ'.val i l - δ.val i l) := by
    rw [sum_three_elems (fun m => (δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m))
      hij hil hjl]
    rw [δ.symm j i, δ'.symm j i, δ.symm l i, δ'.symm l i, δ.symm l j, δ'.symm l j,
        δ.diag j, δ'.diag j, δ.diag l, δ'.diag l]
    ring
  have h4 := Finset.sum_sdiff (s₁ := ({i, j, l} : Finset X)) (s₂ := (Finset.univ : Finset X))
    (f := fun m => ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)))
    (Finset.subset_univ _)
  rw [← h4, h3]
  ring

/-! ## 3. 两条界：Atteson Lemma 12（`:2181–2189`） -/

omit [Fintype X] [DecidableEq X] in
/-- ★ `NearlyAdditive` ⟹ **`δmin > 0`**。

由 `IsLinfClose` 的**对角项** `|δ'(i,i) − δ(i,i)| = |0| = 0 ≤ ε` 得 `ε ≥ 0`，
再由 `ε < safeRadius δmin = δmin/2` 得 `δmin > 0`。

⇒ ★★★ `njCriterion_minimizer_is_cherry` 的陈述**不需**把 `δmin > 0` 列为假设
（它由 `NearlyAdditive` 自动给出）。 -/
theorem nearlyAdditive_deltaMin_pos (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε) (i : X) : 0 < δmin := by
  obtain ⟨hε, hεr⟩ := hnear
  have hh := hε i i
  rw [δ'.diag i, δ.diag i, sub_self, abs_zero] at hh
  rw [safeRadius] at hεr
  linarith

omit [Fintype X] [DecidableEq X] in
/-- 单点四元组合的下界：`a + b − c − d ≥ −4ε`（若 `|a|,|b|,|c|,|d| ≤ ε`）。 -/
theorem four_term_ge {a b c d ε : ℝ}
    (ha : |a| ≤ ε) (hb : |b| ≤ ε) (hc : |c| ≤ ε) (hd : |d| ≤ ε) :
    -4 * ε ≤ a + b - c - d := by
  have ha1 := (abs_le.mp ha).1
  have hb1 := (abs_le.mp hb).1
  have hc2 := (abs_le.mp hc).2
  have hd2 := (abs_le.mp hd).2
  linarith

omit [Fintype X] [DecidableEq X] in
/-- 单点二元组合的下界：`a − b ≥ −2ε`（若 `|a|,|b| ≤ ε`）。 -/
theorem two_term_ge {a b ε : ℝ} (ha : |a| ≤ ε) (hb : |b| ≤ ε) : -2 * ε ≤ a - b := by
  have ha1 := (abs_le.mp ha).1
  have hb2 := (abs_le.mp hb).2
  linarith

/-- ★★ **Atteson Lemma 12 第一式**（`:2181–2185`）：`{i,j} ∩ {k,l} = ∅` 时
`(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) ≥ −6(n−4)·ε`。 -/
theorem qPerturb_bound_disjoint (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j k l : X} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hcard : 4 ≤ Fintype.card X) :
    -6 * ((Fintype.card X : ℝ) - 4) * ε
      ≤ (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j) := by
  rw [qPerturb_reduced δ δ' hij hik hil hjk hjl hkl]
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card
      = Fintype.card X - 4 := by
    rw [card_sdiff_univ, card_four_elems i j k l hij hik hil hjk hjl hkl]
  have hnn : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 4 := by
    have h : (4 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hA : ((Fintype.card X : ℝ) - 4) * (-2 * ε)
      ≤ ((Fintype.card X : ℝ) - 4)
          * ((δ'.val k l - δ.val k l) - (δ'.val i j - δ.val i j)) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have h1 := (abs_le.mp (hε k l)).1
    have h2 := (abs_le.mp (hε i j)).2
    linarith
  have hB : -4 * (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ) * ε
      ≤ ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
          ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
            - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) := by
    have hpt : ∀ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)),
        -4 * ε ≤ ((δ'.val i m - δ.val i m) + (δ'.val j m - δ.val j m)
            - (δ'.val k m - δ.val k m) - (δ'.val l m - δ.val l m)) :=
      fun m _ => four_term_ge (hε i m) (hε j m) (hε k m) (hε l m)
    have h2 := Finset.sum_le_sum hpt
    have h3 : (∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)), (-4 * ε))
        = -4 * (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ) * ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rwa [h3] at h2
  have hcast : (((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card : ℝ)
      = (Fintype.card X : ℝ) - 4 := by
    rw [hcomp, Nat.cast_sub hcard]
    norm_num
  rw [hcast] at hB
  linarith

/-- ★★ **Atteson Lemma 12 第二式（`i = k` 规范形）**（`:2187–2189`、`:2223–2252`）：
`(Ŝ_il − S_il) + (S_ij − Ŝ_ij) ≥ −4(n−3)·ε`。 -/
theorem qPerturb_bound_shared_canon (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j l : X} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcard : 3 ≤ Fintype.card X) :
    -4 * ((Fintype.card X : ℝ) - 3) * ε
      ≤ (δ'.Q i l - δ.Q i l) + (δ.Q i j - δ'.Q i j) := by
  rw [qPerturb_reduced_ik δ δ' hij hil hjl]
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card
      = Fintype.card X - 3 := by
    rw [card_sdiff_univ, card_three_elems i j l hij hil hjl]
  have hnn : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 3 := by
    have h : (3 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hA : ((Fintype.card X : ℝ) - 3) * (-2 * ε)
      ≤ ((Fintype.card X : ℝ) - 3)
          * ((δ'.val i l - δ.val i l) - (δ'.val i j - δ.val i j)) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have h1 := (abs_le.mp (hε i l)).1
    have h2 := (abs_le.mp (hε i j)).2
    linarith
  have hB : -2 * (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ) * ε
      ≤ ∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
          ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) := by
    have hpt : ∀ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)),
        -2 * ε ≤ ((δ'.val j m - δ.val j m) - (δ'.val l m - δ.val l m)) :=
      fun m _ => two_term_ge (hε j m) (hε l m)
    have h2 := Finset.sum_le_sum hpt
    have h3 : (∑ m ∈ ((Finset.univ : Finset X) \ ({i, j, l} : Finset X)), (-2 * ε))
        = -2 * (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ) * ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rwa [h3] at h2
  have hcast : (((Finset.univ : Finset X) \ ({i, j, l} : Finset X)).card : ℝ)
      = (Fintype.card X : ℝ) - 3 := by
    rw [hcomp, Nat.cast_sub hcard]
    norm_num
  rw [hcast] at hB
  linarith

/-- ★★ **Atteson Lemma 12 第二式（一般重合形态）**（`:2187–2189`）：
`{i,j}` 与 `{k,l}` 恰交一个标签时 `(Ŝ_kl − S_kl) + (S_ij − Ŝ_ij) ≥ −4(n−3)·ε`。

四种重合形态通过 `Q` 的对称性 `Q(a,b) = Q(b,a)` 归约到 `i = k` 规范形。 -/
theorem qPerturb_bound_shared (δ δ' : Dissimilarity X) {ε : ℝ}
    (hε : IsLinfClose δ δ' ε) {i j k l : X} (hij : i ≠ j) (hkl : k ≠ l)
    (hov : SharesOneLabel i j k l) (hcard : 3 ≤ Fintype.card X) :
    -4 * ((Fintype.card X : ℝ) - 3) * ε
      ≤ (δ'.Q k l - δ.Q k l) + (δ.Q i j - δ'.Q i j) := by
  have hQc : ∀ (ρ : Dissimilarity X) (a b : X), ρ.Q a b = ρ.Q b a := by
    intro ρ a b
    simp only [Q]
    rw [ρ.symm b a]
    ring
  rcases hov with ⟨hik, hjk, hjl⟩ | ⟨hil, hjk, hjl⟩ | ⟨hjk, hik, hil⟩ | ⟨hjl, hik, hil⟩
  · rw [← hik]
    exact qPerturb_bound_shared_canon δ δ' hε hij (hik.symm ▸ hkl) hjl hcard
  · rw [hil, hQc δ' k l, hQc δ k l]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hjl) (Ne.symm hkl) hjk hcard
  · rw [hQc δ i j, hQc δ' i j, hjk]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hik) hkl hil hcard
  · rw [hQc δ i j, hQc δ' i j, hQc δ' k l, hQc δ k l, hjl]
    exact qPerturb_bound_shared_canon δ δ' hε (Ne.symm hil) (Ne.symm hkl) hik hcard

/-! ## 4. ★★★ 主定理：安全半径 `1/2` 下 NJ 第一轮必取真樱桃 -/

/-- ★★★ **Atteson 安全半径：`n ≥ 5` 时 NJ 第一轮判据的任何最小点都是真树的樱桃**。

（Atteson1999 Theorem 4 的第一步，`:2266–2303`；Theorem 1 归纳的**基例**，`:889`。）

设 `δ` 是真加权二叉树的距离矩阵（「真」的全部内容通过 ★★ `IsCherrySeparated δ δmin`
以 `δmin =` 实现树最短边长的形式给出），`δ'` 是观测矩阵且
`‖δ' − δ‖_∞ ≤ ε < 1/2 · δmin`。则任何使 NJ 判据 `Q_{δ'}` 取最小值的**相异**标签对
`(a,b)` 都是 `δ` 的一颗樱桃（即真树中相邻）。

**证明链**：反设 `(a,b)` 非樱桃，由 ★★ `IsCherrySeparated` 取樱桃 `(i,j)`
⇒ 由 ★★ `qPerturb_bound_disjoint`（或 ★★ `qPerturb_bound_shared`）得
`Q_{δ'}(a,b) − Q_{δ'}(i,j) ≥ −6(n−4)ε + 3(n−4)δmin = 3(n−4)(δmin − 2ε) > 0`，
与最小性矛盾。 -/
theorem njCriterion_minimizer_is_cherry (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε)
    (hcard : 5 ≤ Fintype.card X) (hsep : IsCherrySeparated δ δmin)
    {a b : X} (hab : a ≠ b)
    (hmin : ∀ x y : X, x ≠ y → δ'.Q a b ≤ δ'.Q x y) :
    δ.IsCherry a b := by
  obtain ⟨hε, hεr⟩ := hnear
  by_contra hnc
  obtain ⟨i, j, hcherry, hcase⟩ := hsep a b hab hnc
  have hij : i ≠ j := hcherry.1
  have hn : (0 : ℝ) < (Fintype.card X : ℝ) - 4 := by
    have h : (5 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  have hε2 : 2 * ε < δmin := by
    rw [safeRadius] at hεr
    linarith
  have hkey : δ'.Q i j < δ'.Q a b := by
    have hdecomp : δ'.Q a b - δ'.Q i j
        = ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by ring
    have hpos : 0 < δ'.Q a b - δ'.Q i j := by
      rw [hdecomp]
      rcases hcase with ⟨hdis, hbnd⟩ | ⟨hsh, hbnd⟩
      · obtain ⟨hik, hil, hjk, hjl⟩ := hdis
        have hb := qPerturb_bound_disjoint δ δ' hε hij hik hil hjk hjl hab
          (le_trans (by norm_num : (4:ℕ) ≤ 5) hcard)
        have hfac : 3 * ((Fintype.card X : ℝ) - 4) * (δmin - 2 * ε)
            ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
          linarith
        have hpos' : 0 < 3 * ((Fintype.card X : ℝ) - 4) * (δmin - 2 * ε) := by
          have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
          exact mul_pos (mul_pos (by norm_num) hn) h2
        linarith
      · have hb := qPerturb_bound_shared δ δ' hε hij hab hsh
          (le_trans (by norm_num : (3:ℕ) ≤ 5) hcard)
        have h3 : (0 : ℝ) < (Fintype.card X : ℝ) - 3 := by
          have h : (5 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
          linarith
        have hfac : 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε)
            ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
          linarith
        have hpos' : 0 < 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε) := by
          have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
          exact mul_pos (mul_pos (by norm_num) h3) h2
        linarith
    linarith
  exact absurd (hmin i j hij) (not_le.mpr hkey)

/-- ★★★ **`n = 4` 版本**（Atteson1999 `:2205–2221` 的 `n = 4` 退化）。

`n = 4` 时两对不可能「不交且一为樱桃」——樱桃的补对是另一颗樱桃
—— 故分离只能走「恰交一个标签」分支，界 `2(n−3)δmin = 2δmin` 与 `−4(n−3)ε = −4ε`
仍然给出 `2(δmin − 2ε) > 0`：**半径 `1/2` 在 `n = 4` 也成立**。 -/
theorem njCriterion_minimizer_is_cherry_card_four (δ δ' : Dissimilarity X) {δmin ε : ℝ}
    (hnear : NearlyAdditive δ δ' δmin ε)
    (hcard : Fintype.card X = 4)
    (hsep : ∀ k l : X, k ≠ l → ¬ δ.IsCherry k l →
      ∃ i j : X, δ.IsCherry i j ∧ SharesOneLabel i j k l ∧
        2 * ((Fintype.card X : ℝ) - 3) * δmin ≤ δ.Q k l - δ.Q i j)
    {a b : X} (hab : a ≠ b)
    (hmin : ∀ x y : X, x ≠ y → δ'.Q a b ≤ δ'.Q x y) :
    δ.IsCherry a b := by
  obtain ⟨hε, hεr⟩ := hnear
  by_contra hnc
  obtain ⟨i, j, hcherry, hsh, hbnd⟩ := hsep a b hab hnc
  have hij : i ≠ j := hcherry.1
  have hcard3 : (3 : ℕ) ≤ Fintype.card X := by rw [hcard]; norm_num
  have h3 : (0 : ℝ) < (Fintype.card X : ℝ) - 3 := by
    rw [hcard]; norm_num
  have hε2 : 2 * ε < δmin := by
    rw [safeRadius] at hεr
    linarith
  have hkey : δ'.Q i j < δ'.Q a b := by
    have hdecomp : δ'.Q a b - δ'.Q i j
        = ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by ring
    have hpos : 0 < δ'.Q a b - δ'.Q i j := by
      rw [hdecomp]
      have hb := qPerturb_bound_shared δ δ' hε hij hab hsh hcard3
      have hfac : 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε)
          ≤ ((δ'.Q a b - δ.Q a b) + (δ.Q i j - δ'.Q i j)) + (δ.Q a b - δ.Q i j) := by
        linarith
      have hpos' : 0 < 2 * ((Fintype.card X : ℝ) - 3) * (δmin - 2 * ε) := by
        have h2 : 0 < δmin - 2 * ε := by linarith [hε2]
        exact mul_pos (mul_pos (by norm_num) h3) h2
      linarith
    linarith
  exact absurd (hmin i j hij) (not_le.mpr hkey)

/-! ## 5. `n = 4` 的精确抵消 -/

/-- ★★ **`n = 4` 时 `Q` 的排序在不相交对上完全不受扰动影响**。

由 ★★★ `qPerturb_reduced`：`n = 4` 且四标签互异时 `n − 4 = 0` 且补集为空
⇒ 式 (16) 的右端**恒为 `0`**。 -/
theorem qPerturb_cancel_of_card_four (hcard : Fintype.card X = 4)
    (δ δ' : Dissimilarity X) {i j k l : X} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    δ'.Q k l - δ'.Q i j = δ.Q k l - δ.Q i j := by
  have hcomp : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card
      = Fintype.card X - 4 := by
    rw [card_sdiff_univ, card_four_elems i j k l hij hik hil hjk hjl hkl]
  have hzero : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)).card = 0 := by
    rw [hcomp, hcard]
  have hempty : ((Finset.univ : Finset X) \ ({i, j, k, l} : Finset X)) = ∅ :=
    Finset.card_eq_zero.mp hzero
  have hred := qPerturb_reduced δ δ' hij hik hil hjk hjl hkl
  rw [hempty, Finset.sum_empty, hcard] at hred
  norm_num at hred
  linarith

/-! ## 6. ★★ Lemma 7 的一步形式：更新式 (6) 不放大 `L∞` 扰动 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **Atteson Lemma 7 的一步形式**（`:749–751`；更新式 (6) 见 `:611`）。

`δ_u(x) = θ·δ_i(x) + (1−θ)·δ_j(x)`（`0 ≤ θ ≤ 1`）是凸组合，
故 `|δ'_u(x) − δ_u(x)| ≤ θ·ε + (1−θ)·ε = ε`：**合并操作不放大 `L∞` 误差**。
这正是 Theorem 1 归纳（`:889–915`）中 `‖D̃_m − D_m‖_∞ ≤ ‖D̃ − D‖_∞` 的递推步。 -/
theorem linfClose_update (δ δ' : Dissimilarity X) {ε θ : ℝ} (hε : IsLinfClose δ δ' ε)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i j x : X) :
    |(θ * δ'.val i x + (1 - θ) * δ'.val j x) - (θ * δ.val i x + (1 - θ) * δ.val j x)| ≤ ε := by
  have h1 : |δ'.val i x - δ.val i x| ≤ ε := hε i x
  have h2 : |δ'.val j x - δ.val j x| ≤ ε := hε j x
  have h3 : (θ * δ'.val i x + (1 - θ) * δ'.val j x) - (θ * δ.val i x + (1 - θ) * δ.val j x)
      = θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x) := by ring
  rw [h3]
  have hb1 : |θ * (δ'.val i x - δ.val i x)| ≤ θ * ε := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left h1 hθ0
  have hb2 : |(1 - θ) * (δ'.val j x - δ.val j x)| ≤ (1 - θ) * ε := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - θ)]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have htri : |θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x)|
      ≤ |θ * (δ'.val i x - δ.val i x)| + |(1 - θ) * (δ'.val j x - δ.val j x)| := by
    have h := abs_sub_le (θ * (δ'.val i x - δ.val i x)) 0
      (-((1 - θ) * (δ'.val j x - δ.val j x)))
    simpa using h
  calc |θ * (δ'.val i x - δ.val i x) + (1 - θ) * (δ'.val j x - δ.val j x)|
      ≤ |θ * (δ'.val i x - δ.val i x)| + |(1 - θ) * (δ'.val j x - δ.val j x)| := htri
    _ ≤ θ * ε + (1 - θ) * ε := add_le_add hb1 hb2
    _ = ε := by ring

/-! ## 7. ★C 最小具体例子：`Fin 4`，挂边 `1,2,3,4`、内部边 `5`

树 `((0,1),(2,3))`：`d(0,1) = 1+2 = 3`、`d(2,3) = 3+4 = 7`、
`d(0,2) = 1+5+3 = 9`、`d(0,3) = 1+5+4 = 10`、`d(1,2) = 2+5+3 = 10`、`d(1,3) = 2+5+4 = 11`。
最短边长 `δmin = 1` ⇒ `safeRadius 1 = 1/2`。

`Q(i,j) = 2·d_ij − S(i) − S(j)`（`n = 4`），`S = (22, 24, 26, 28)`，故

`Q(0,1) = Q(2,3) = −40`（**两颗樱桃**），四个交叉对全部 `= −30`。 -/

/-- `Fin 4` 上的求和展开（`∑ k : Fin 4, f k = f 0 + f 1 + f 2 + f 3`）。 -/
theorem sum_univ_four_fin (f : Fin 4 → ℝ) :
    (∑ k : Fin 4, f k) = f 0 + (f 1 + (f 2 + f 3)) := by
  have h : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by decide)
  rw [← h]
  exact sum_four_elems f (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 真距离矩阵的值函数（★C 最小例子）。 -/
def exVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 3 | 1, 0 => 3
  | 2, 3 => 7 | 3, 2 => 7
  | 0, 2 => 9 | 2, 0 => 9
  | 0, 3 => 10 | 3, 0 => 10
  | 1, 2 => 10 | 2, 1 => 10
  | 1, 3 => 11 | 3, 1 => 11

/-- ★C 的真相异度：树 `((0,1),(2,3))`，挂边 `1,2,3,4`、内部边 `5`。 -/
def exDiss : Dissimilarity (Fin 4) where
  val := exVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- 观测扰动矩阵的值函数：非对角扰动 `∈ {−1/5, +1/5, +2/5}`
（`‖ε‖_∞ = 2/5 < safeRadius 1 = 1/2`）。 -/
def exPertVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 17 / 5 | 1, 0 => 17 / 5
  | 2, 3 => 36 / 5 | 3, 2 => 36 / 5
  | 0, 2 => 44 / 5 | 2, 0 => 44 / 5
  | 0, 3 => 51 / 5 | 3, 0 => 51 / 5
  | 1, 2 => 49 / 5 | 2, 1 => 49 / 5
  | 1, 3 => 56 / 5 | 3, 1 => 56 / 5

/-- ★C 的观测相异度 `δ' = δ + ε`（`|ε_ij| ≤ 2/5`）。 -/
def exPert : Dissimilarity (Fin 4) where
  val := exPertVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  diag := by intro i; fin_cases i <;> rfl

/-- ★C：`(0,1)` 是真树的一颗樱桃（`d(0,1)+d(2,3) = 10 ≤ 20 = d(0,2)+d(1,3) = d(0,3)+d(1,2)`）。 -/
theorem exDiss_isCherry_01 : exDiss.IsCherry 0 1 := by
  refine ⟨by decide, ?_⟩
  intro k l hk0 hk1 hl0 hl1
  have hk : k = 2 ∨ k = 3 := by fin_cases k <;> simp_all
  have hl : l = 2 ∨ l = 3 := by fin_cases l <;> simp_all
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
    (simp only [exDiss, exVal]; constructor <;> norm_num)

/-- ★ **反空转见证（W47 M3）**：`exDiss` 上 `(0,2)` **不是**樱桃。

`d(0,2)+d(1,3) = 9+11 = 20 > 10 = d(0,1)+d(2,3)`，故第一条四点不等式不成立。

**为什么这条重要**：★★★ `IsCherrySeparated` 的前提是「`¬ δ.IsCherry k l`」。
若它在 `|X| = 4` 上**永不成立**，那么 `njSeparationBound` 在小基数上就是**空真**的。
本定理（配 ★★★ `exDiss_isCherrySeparated_five`，其中 8 个交叉对都走这条分支）
把「`n = 4` 时前提非空」落成**机器可查**的事实 —— 这正是派单 M3 要求的★反空转试金石。

★ 机械复跑：`grep -n "exDiss_not_isCherry_02" Phylo/AttesonRadius.lean` 可定位本定理；
`lake env lean` 对 `exDiss.IsCherry 0 2` 做 `decide` 亦得 `false`。 -/
theorem exDiss_not_isCherry_02 : ¬ exDiss.IsCherry 0 2 := by
  intro h
  have h1 := (h.2 1 3 (by decide) (by decide) (by decide) (by decide)).1
  simp only [exDiss, exVal] at h1
  norm_num at h1

/-- ★C：真距离矩阵上 `Q` 的六个值 —— 两颗樱桃 `(0,1)、(2,3)` 取 `−40`，
四个交叉对取 `−30`（`Q(i,j) = 2·d_ij − S(i) − S(j)`）。 -/
theorem exDiss_Q_01 : exDiss.Q 0 1 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_23 : exDiss.Q 2 3 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_02 : exDiss.Q 0 2 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_03 : exDiss.Q 0 3 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_12 : exDiss.Q 1 2 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_13 : exDiss.Q 1 3 = -30 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
  norm_num

theorem exDiss_Q_10 : exDiss.Q 1 0 = -40 := by
  rw [Q_comm exDiss 1 0]
  exact exDiss_Q_01

theorem exDiss_Q_20 : exDiss.Q 2 0 = -30 := by
  rw [Q_comm exDiss 2 0]
  exact exDiss_Q_02

theorem exDiss_Q_30 : exDiss.Q 3 0 = -30 := by
  rw [Q_comm exDiss 3 0]
  exact exDiss_Q_03

theorem exDiss_Q_21 : exDiss.Q 2 1 = -30 := by
  rw [Q_comm exDiss 2 1]
  exact exDiss_Q_12

theorem exDiss_Q_31 : exDiss.Q 3 1 = -30 := by
  rw [Q_comm exDiss 3 1]
  exact exDiss_Q_13

theorem exDiss_Q_32 : exDiss.Q 3 2 = -40 := by
  rw [Q_comm exDiss 3 2]
  exact exDiss_Q_23

/-- ★C：真树上 `Q` 的最小点是樱桃（`Q(0,1) = Q(2,3) = −40 < −30 = ` 任何交叉对）。 -/
theorem exDiss_argmin_isCherry : ∀ i j : Fin 4, i ≠ j → exDiss.Q 0 1 ≤ exDiss.Q i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exDiss_Q_01, exDiss_Q_23, exDiss_Q_02, exDiss_Q_03, exDiss_Q_12, exDiss_Q_13,
      exDiss_Q_10, exDiss_Q_20, exDiss_Q_30, exDiss_Q_21, exDiss_Q_31, exDiss_Q_32] <;>
    norm_num

/-- ★C：观测矩阵上 `Q` 的六个值 —— 与真矩阵的**排序完全一致**
（`(0,1)、(2,3)` 仍取 `−40`，交叉对一致降到 `−153/5`）。 -/
theorem exPert_Q_01 : exPert.Q 0 1 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_23 : exPert.Q 2 3 = -40 := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_02 : exPert.Q 0 2 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_03 : exPert.Q 0 3 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_12 : exPert.Q 1 2 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_13 : exPert.Q 1 3 = -(153 / 5) := by
  simp only [Q, Fintype.card_fin, sum_univ_four_fin, exPert, exPertVal]
  norm_num

theorem exPert_Q_10 : exPert.Q 1 0 = -40 := by
  rw [Q_comm exPert 1 0]
  exact exPert_Q_01

theorem exPert_Q_20 : exPert.Q 2 0 = -(153 / 5) := by
  rw [Q_comm exPert 2 0]
  exact exPert_Q_02

theorem exPert_Q_30 : exPert.Q 3 0 = -(153 / 5) := by
  rw [Q_comm exPert 3 0]
  exact exPert_Q_03

theorem exPert_Q_21 : exPert.Q 2 1 = -(153 / 5) := by
  rw [Q_comm exPert 2 1]
  exact exPert_Q_12

theorem exPert_Q_31 : exPert.Q 3 1 = -(153 / 5) := by
  rw [Q_comm exPert 3 1]
  exact exPert_Q_13

theorem exPert_Q_32 : exPert.Q 3 2 = -40 := by
  rw [Q_comm exPert 3 2]
  exact exPert_Q_23

/-- ★C ★★★ **端到端**：观测矩阵 `δ'`（`‖δ' − δ‖_∞ = 2/5 < 1/2 = safeRadius 1`）上
`Q` 的最小点仍是真树的樱桃 `(0,1)`。 -/
theorem exPert_argmin_isCherry : ∀ i j : Fin 4, i ≠ j → exPert.Q 0 1 ≤ exPert.Q i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exPert_Q_01, exPert_Q_23, exPert_Q_02, exPert_Q_03, exPert_Q_12, exPert_Q_13,
      exPert_Q_10, exPert_Q_20, exPert_Q_30, exPert_Q_21, exPert_Q_31, exPert_Q_32] <;>
    norm_num

/-- ★C：`δ'` 确实在安全半径内（`‖δ' − δ‖_∞ ≤ 2/5 < safeRadius 1`）。 -/
theorem exPert_nearlyAdditive : NearlyAdditive exDiss exPert 1 (2 / 5) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [exPert, exDiss, exPertVal, exVal] <;> norm_num
  · rw [safeRadius]; norm_num

/-- 反空真：`δ` 满足四点条件（Tree metric ⟹ four-point）⇒ 缺口的**前提非空**。 -/
theorem exDiss_fourPoint : exDiss.FourPoint := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [exDiss, exVal] <;> norm_num

/-! ## 8. 缺口命题（**不是数学缺口，是本库的工程缺口**） -/

/-- ★★★ **缺口 1：Atteson Lemma 11 的度量版**（`:1989–2009`）的可实现性。

设 `δ` 是由**正边权**二叉树实现的距离矩阵（本库判据：`FourPoint` + `PositiveDefinite`，
见 `Phylo/Buneman.lean:589` 的 `ExistsRealizingPhylogram`），叶子数 `≥ 4`。则存在
`δmin > 0`（= 实现树的最短边长）使 ★★ `IsCherrySeparated δ δmin` 成立。

**这是把 ★★★ `njCriterion_minimizer_is_cherry` 从条件定理变成
「无条件 Atteson 安全半径定理」的**唯一**剩余缺口。**

缺的机制（Atteson Lemma 10，`:1774–1804`）：`Q(i,j) = Σ_{e∈E} w_e(i,j)·l(e)`，其中
`w_e(i,j) = −2`（`e ∈ P_{i,j}`）、`= −2|L − L_i(e)|`（否则）—— 只依赖拓扑；
于是 `Q(k,l) − Q(i,j) = Σ_e (w_e(k,l) − w_e(i,j))·l(e)`，逐边比较并使用
「路径旁子树的叶数」单调性（`:2023–2056`）即得。

**缺什么**：本库 `Phylogram` 有 `dist` 与边权，但**没有**
(a)「`Dissimilarity.IsCherry δ a b` ⟺ 树中 `a,b` 相邻」的桥，
(b)「路径关联 `e ∈ P_{i,j}` + 子树叶数 `|L_i(e)|`」的层，
(c) Lemma 10 的权重公式 `w_e`。

**反空真**：★★ `exDiss_fourPoint` 给出前提可满足；★C `exDiss_argmin_isCherry`
给出结论方向上 `n = 4` 的具体实例。

**★★ 2026-10-14 W19 文献归属更正（留证 ✓；★ 命题本身未改 ✓）**：
* **旧归属**：本 `def` 原被标为「Atteson **Lemma 11**（度量版可实现性）」✗；
* **原文核验**：`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md:1989-2009`
  的 **LEMMA 11** 逐字是「若 `k, l ∈ L` **不是邻居**，则存在邻居对 `i, j ∈ L` 使
  `S_{k,l} − S_{i,j} ≥ 3(n−4)·min_e l(e)`（且 `{i,j} ∩ {k,l} = ∅`）
  或 `S_{k,l} − S_{i,j} ≥ 2(n−3)·min_e l(e)`（且 `|{i,j} ∩ {k,l}| = 1`）」✗
  —— 那是**NJ 判据的间隙不等式**，**不是**本 `def`（`∃ δmin > 0, IsCherrySeparated δ δmin`）✗；
* **新归属**：本 `def` 是 Atteson **Theorem 1**（同文件 `:868`）的**前提侧** ✓
  —— 由「正边权二叉树实现的距离矩阵」得到**正的最短边长** `min_e l(e) > 0` ✓（原文 `:209` 亦以
  “in multiples of the length of the **shortest edge**” 为尺度 ✓），即 Theorem 1 中**被假定**的那个 `δmin` ✓；
* **为什么不改命题** ✓：它是 ★★★ `njCriterion_minimizer_is_cherry` 从条件定理变成「无条件 Atteson 安全半径定理」的
  **唯一剩余前提** ✓ ⇒ 改成 Lemma 11 的间隙不等式会**破坏该用途** ✗（且库内 docstring 已列明其所缺的三件器材
  (a)(b)(c) ✓）。故依 W19 护栏精神：**改归属 ＋ 留证** ✓，**不动命题** ✓；
* **护栏③**：本处仅改 docstring ⇒ 仍需跑全库 build（**job 数以当批实测为准** ✓ —— 原文写的「应仍 3966」是 W19 开跑前的旧基线，★ **2026-10-15 W20 任务 C 更正**：W20 起点实测为 **3968**，本批新增模块后为 **3972**）＋ `scripts/list_star_claims.sh` ✓。

★ **W36-D 复核（2026-10-27，只改措辞，`def`/`_holds` 一字未动）**：
`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md:1989–2009` 的 **LEMMA 11** 常数是
「**由树算出的**最短边长 `min_e l(e)`」；本 `def` 把它换成 `∃ δmin > 0` —— 二者**不等价**：
数值实测（`.w36/d_mincheck.py`，`ε = 1e-6`）最大可行 `δmin* ≈ 0.667`，是 `min_e l(e)` 的 **6.7×10⁵ 倍**，
且 `ε → 0` 时 `δmin* → 2/3`（常数）而 `min_e l(e) → 0`。
⇒ 本 `def` 证得的是 Lemma 11 的**序关系推论**（「每个非樱桃对都有 `Q` 更小的樱桃对」），
**Lemma 11 的间隙式本身未证**；`IsCherrySeparated`（`:132–138`）的间隙形状是忠实的，弱的只是这个 `∃`。
★ 它作为 Theorem 1 前提的地位**待裁定**（是否从「已收口」降「条件收口」，等老师批；**本批不动桶**）。 -/
def atteson_lemma11_gap_order_form (δ : Dissimilarity X) : Prop :=
  δ.FourPoint → δ.PositiveDefinite → 4 ≤ Fintype.card X →
    ∃ δmin : ℝ, 0 < δmin ∧ δ.IsCherrySeparated δmin

/-! ### 8.1.0 ★ W38-1：忠实形态（定量版）所需的两个胶水定义

方案 d 把原来一条缺口**拆成两半**（老师 2026-10-27 批）：
* 上面那条 `atteson_lemma11_gap_order_form` 证的是**序关系推论**（W38-1 之前它用的无后缀旧名）；
* 下面这条 `atteson_lemma11_gap_quantitative` 才是 Lemma 11 的**忠实形态**（常数由树算出，无 `∃`）。
-/

/-- `T` 的**最短边长** `min_e w(e)`：边权集合的下确界。

    对有限树（边集非空、边权非负）它就是**最小值**；这里写成 `Set.range T.w` 的下确界，
    是为了省掉 `Finset.inf'` 的非空证明枝节（**定义**用下确界，将来要证 `= min` 再补一条小引理）。 -/
noncomputable def minEdgeWeight (T : Phylogram X) : ℝ := sInf (Set.range T.w)

/-- 由 `Phylogram` 诱导的 dissimilarity：`δ(x,y) = T.dist (leaf x) (leaf y)`。

    对称性取 `Phylo.TreeDist.dist_comm`（`Phylo/TreeDistance.lean:121`），对角取 `Phylogram.dist_self`。 -/
noncomputable def toDissimilarity (T : Phylogram X) : Dissimilarity X where
  val x y := T.dist (T.leaf x) (T.leaf y)
  symm x y := Phylo.TreeDist.dist_comm T (T.leaf x) (T.leaf y)
  diag x := T.dist_self (T.leaf x)

/-- ★ **Atteson Lemma 11 的忠实形态（定量版）** —— 本 `def` 里**没有 `∃ δmin`**，
常数被钉成**由树算出的**最短边长 `minEdgeWeight T`。

依据：`references/md/Atteson1999_PerformanceNeighborJoiningAlgorithmica.md:1989–2009` 的
**LEMMA 11**：`k,l` 不是邻居 ⟹ 存在邻居对 `i,j` 使
`S_{k,l} − S_{i,j} ≥ 3(n−4)·min_e l(e)`（两对不交）或 `≥ 2(n−3)·min_e l(e)`（恰交一标签）。
`IsCherrySeparated`（本文件 `:132`）的形状已忠实（两条间隙式 ＋ 两分支），
故这里**直接复用**它，只把自由参数换成 `minEdgeWeight T`。

★ **四要素留证（W38-1）**：
  ① **位置**：本文件新 `def`（`NJ.Dissimilarity.atteson_lemma11_gap_quantitative`）；
  ② **依据**：上述 md `:1989–2009`（`.w36/D_report.md` §2.2 的符号表，已逐字复核）；
  ③ **现状**：库里**已证**的是 `atteson_lemma11_gap_order_form_holds`（序关系版，
     `∃ δmin > 0`）；**本 `def` 未证**，台账记 `[真开放]`（71 → 72）；
  ④ **未证的原因（缺什么）** —— ★ **W48 实核后已改写**（原写「缺 (a)(b)(c) 三件器材」，已过时）：
     **(b)(c) 已备** —— 「路径关联 `e ∈ P_{i,j}`」＝ §13 `mem_pathOf_edges_iff_not_inSide`（`:1680`）、
     「子树叶数 `|L_i(e)|`」＝ §12 `sideLeafCount`（`:1521`）、「Lemma 10 的权重公式 `w_e`」＝
     §13 `attesonW`（`:1715`）＋ §14–§18 的逐边分解与收口（`attesonQ_sub` `:1767`、
     `attesonQ_wExt_eq` `:2032`）；**(a) 不需要** —— `IsCherrySeparated` 的假设是**度量层**
     `¬δ.IsCherry k l`，由既有 ★ `CASTERNJ.isCherry_of_tree_isCherry` 的**逆否**即得树层非樱桃
     （W48 报告 §2）。⇒ **真正缺的只有「逐边单调性」**（Atteson `:2008–2070` 的 `e*` 选法 ＋
     系数和 `3(n−4)` / `2(n−3)`），即 W48 报告 §3 的 `(ii)`。W49 已落 `(i)`（`minEdgeWeight` 的
     `sInf → min` 桥，见 §8.1.0′）与 `(ii)a`（任意 `(k,l)` 的系数差四种情形 ＋「分离 ⇒ 系数非负」，
     见 §19）；**`(ii)b`/`(ii)c`/`(iii)` 未落**，路线见项目根目录 `W49_A_PLAN.md`。

★ **W50 ★D（2026-11-07，机械核）：本 `def` 在「多叉」（polytomy）树上为假** ——
`Phylogram`（`Phylo/Core.lean:157`）只要求 `no_degree_two`，**允许**内点度 ≥ 4；而 Atteson
Lemma 11 的前提是 **binary** tree（md `:1989` “for a weighted **binary** tree”），其证明
case 1（`:2034–2043`）显式用「每个内点恰关联 3 条边」。
反例（`scripts/msc/w50_lemma11_polytomy_refute.py`，精确有理数）：双星 `v1`（度 4）—`v2`（度 4），
两侧各挂 3 片叶、全边权 1（`n = 6`；合法 `Cladogram`：连通、无环、无度 2 点、叶 = 标签集）；
取 `(k,l)` 为两侧各一片（非樱桃，`¬ IsCherry` 已核）⇒ **6 个樱桃的间隙全是 `4`**，
而 `DisjointPairs` 支要求 `3(n−4)·δmin = 6`、`SharesOneLabel` 支要求 `2(n−3)·δmin = 6`
⇒ 两支**全不满足**。同脚本 `m = 2`（二叉，`n = 4`）则满足（间隙 2，要求 0／2）。
⇒ 定量版的**忠实陈述必须带 `T.toCladogram.IsBinary`**；`def` 本体**逐字未动**（引理留证）。
建议老师裁定：把 `IsBinary` 写进 `def`，还是在定理处加前提 —— 本库取后者
（`atteson_lemma11_gap_quantitative_holds_of_binary`，将落在本文件 §22 **之后**；
★ §22 现已用于 `cherry_in_component`，见该节）。 -/
def atteson_lemma11_gap_quantitative (T : Phylogram X) : Prop :=
  4 ≤ Fintype.card X → (toDissimilarity T).IsCherrySeparated (minEdgeWeight T)


/-! ### 8.1.0′ ★★★ W49-A-(i)：`minEdgeWeight` 的 `sInf → min` 桥

`minEdgeWeight T` 定义为 `sInf (Set.range T.w)`（`:891`）。★ 现场复核：`grep -rn 'sInf' Phylo/`
在**全库只命中两处** —— 本 `def` 与 `Phylo/SplitWeak.lean:92` 的一行**注释**
（W48 报告说「只出现这一次」是漏了那条注释，结论不变：**没有任何** `sInf → min` 的桥）。

为什么这层桥不是装饰：`sInf` 只给**下界**，**正性**需要「下确界真的被取到」。
Lemma 11 的装配式 `Σ_e c_e·l(e) ≥ δmin·Σ_e c_e` 同时要这两件事

* `l(e) ≥ δmin`（★ `minEdgeWeight_le`，`csInf_le`）；
* `δmin > 0`（★★ `minEdgeWeight_pos`，**必须**知道 `sInf` 是某个 `T.w e`）。

做法：`Edge T.toCladogram` 是 `Sym2 T.V` 的 `Fintype` 子类型 ⇒ `Set.range T.w` 有限非空
⇒ `sInf` 落在 `Finset.univ.image T.w` 的 `min'` 上（★ `minEdgeWeight_eq_min'`），
再由 `Finset.min'_mem` 取出那条边。 -/

/-- ★ **边集非空**：任取一片叶，它的度是 1（★★ `Cladogram.isLeaf_iff_degree_eq_one`），
故它有**唯一**邻居 `c`，于是 `s(T.leaf x, c)` 是一条边。 -/
theorem edge_nonempty (T : Phylogram X) (x : X) : Nonempty (Edge T.toCladogram) := by
  have hleaf : T.toCladogram.IsLeaf (T.leaf x) := ⟨x, rfl⟩
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.toCladogram.isLeaf_iff_degree_eq_one (T.leaf x)).mp hleaf
  obtain ⟨c, hc, -⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  exact ⟨⟨s(T.leaf x, c), (SimpleGraph.mem_edgeSet T.graph).mpr hc⟩⟩

/-- ★ **`min'` 版的最小边权**（`minEdgeWeight` 的可计算孪生；两者相等见 `minEdgeWeight_eq_min'`）。 -/
noncomputable def minEdgeWeight' (T : Phylogram X) (hne : Nonempty (Edge T.toCladogram)) : ℝ := by
  classical
  exact (Finset.univ.image T.w).min' (by
    haveI := hne
    exact Finset.univ_nonempty.image T.w)

/-- ★ **下界**：`minEdgeWeight T ≤ T.w e`（对**每条**边；这就是 `sInf` 是下界）。
★ 不需要非空假设 —— 空集时 `sInf ∅ = 0` 也照样给一条（此时左边没意义，但等式仍相容）。 -/
theorem minEdgeWeight_le (T : Phylogram X) (e : Edge T.toCladogram) :
    minEdgeWeight T ≤ T.w e := by
  refine csInf_le ?_ (Set.mem_range_self e)
  exact (Set.finite_range T.w).bddBelow

/-- ★★ **`sInf` 就是 `min'`**：边集有限非空 ⇒ 下确界**被取到**，且就是有限集的 `min'`。 -/
theorem minEdgeWeight_eq_min' (T : Phylogram X) (hne : Nonempty (Edge T.toCladogram)) :
    minEdgeWeight T = minEdgeWeight' T hne := by
  classical
  haveI := hne
  have hne' : (Finset.univ : Finset (Edge T.toCladogram)).Nonempty := Finset.univ_nonempty
  have hmin : minEdgeWeight' T hne = (Finset.univ.image T.w).min' (hne'.image T.w) := rfl
  rw [hmin]
  refine le_antisymm ?_ ?_
  · obtain ⟨e, -, he⟩ :=
      Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image T.w) (hne'.image T.w))
    exact csInf_le (Set.finite_range T.w).bddBelow (Set.mem_range.mpr ⟨e, he⟩)
  · refine le_csInf ?_ ?_
    · obtain ⟨e, -⟩ := hne'
      exact ⟨T.w e, Set.mem_range_self e⟩
    · rintro _ ⟨e, -, rfl⟩
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem T.w (Finset.mem_univ e))

/-- ★★ **正性**：全边权为正 ⇒ `0 < minEdgeWeight T` —— 这是 `csInf_le` **给不出**的一半
（要用「下确界被取到」）：`minEdgeWeight = T.w e₀` 对**某条**边 `e₀` 成立。 -/
theorem minEdgeWeight_pos (T : Phylogram X) (hne : Nonempty (Edge T.toCladogram))
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) : 0 < minEdgeWeight T := by
  classical
  haveI := hne
  rw [minEdgeWeight_eq_min' T hne]
  have hne' : (Finset.univ : Finset (Edge T.toCladogram)).Nonempty := Finset.univ_nonempty
  have hmem := Finset.min'_mem (Finset.univ.image T.w) (hne'.image T.w)
  obtain ⟨e, -, he⟩ := Finset.mem_image.mp hmem
  rw [show minEdgeWeight' T hne = (Finset.univ.image T.w).min' (hne'.image T.w) from rfl, ← he]
  exact hpos e



/-! ### 8.1 ★★★ 缺口 1 **已证成**：`atteson_lemma11_gap_order_form` 是定理（W25 泳道 b）

结论 ★★★ `atteson_lemma11_gap_order_form_holds`：`atteson_lemma11_gap_order_form` **不需要任何数学假设**即成立；
且证明**连 `PositiveDefinite` 都不需要**（只用 `FourPoint` 与 `4 ≤ |X|`）。

**路线（不走树层，(a)(b)(c) 三件器材全部绕过）**：§8 原诊断认为本缺口要实现树 + Lemma 10 的
权重公式 `w_e`。关键观察是 —— 本 `def` 里 `δmin` 是 **`∃` 约束的自由参数**，可以取任意小，
故只需「**每个非樱桃对都有严格更小的 `Q` 的樱桃对**」：

1. ★★★ `Dissimilarity.maxZCherryCore`（`Phylo/Algorithm/NJHardCore.lean:308`，**无条件定理**）
   ＋ ★★ `Dissimilarity.nj_cherry`（`Phylo/Algorithm/NJ.lean:351`）
   ⇒ **`Q` 的全局最小点必是樱桃**（有限集上必取到最小值）；
2. 若非樱桃对 `(k,l)` 也取到 `Q` 的全局最小值，则同一条 `nj_cherry` 说它也是樱桃 —— 矛盾
   ⇒ 对全局最小樱桃 `(a,b)` 有 **`Q(a,b) < Q(k,l)`**（严格，这正是 n ≥ 5 时需要的）；
3. ★★★ `disjointPairs_or_sharesOneLabel_of_isCherry`：任意樱桃对任意非樱桃对**形态总是合格**
   （不交或恰交一标签）⇒ **同一个**固定樱桃 `(a,b)` 就能为**所有**非樱桃对作证，
   不需要逐对挑证人；
4. 取 `δmin := (min_{非樱桃 (k,l)} (Q(k,l) − Q(a,b))) / (3·n) > 0`，系数比较
   `3(n−4) ≤ 3n`、`2(n−3) ≤ 3n` 即得两条间隙不等式（n = 4 时 `3(n−4) = 0` 自动成立）。

**诚实边界**：本证明**不用** Atteson Lemma 11 的间隙不等式本身（原文 `:1989–2009`），也不用
Lemma 10 的权重公式（`:1774–1804`）；得到的 `δmin` 是**抽象正数**，**不**声称等于实现树的最短边长
（本 `def` 只要求 `∃ δmin > 0`，故够用 —— 这与 §8 docstring 的 W19 归属更正不冲突：那里说的是
「本 `def` 在 Atteson Theorem 1 里扮演 `min_e l(e) > 0` 的角色」，本定理只证**存在性**）。

**★D 命题核查**（`scripts/msc/w25_lemma11_gap_check.py`）：`∃ δmin > 0, IsCherrySeparated δ δmin`
在 n = 4 全枚举（六距离取值 0–5，3025 个 `FourPoint ∧ PositiveDefinite` 度量）、
n = 5（取值 0–2）以及 n = 4…10 的随机树度量（**含 0 权边 / 零长悬挂边**，共 128 918 个）上
**0 反例** ⇒ 与「该命题为真」一致（故本批**不**走证伪路线）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`IsCherry` 的标签交换对称性**：`IsCherry i j → IsCherry j i`。 -/
theorem IsCherry.swap {δ : Dissimilarity X} {i j : X} (h : δ.IsCherry i j) :
    δ.IsCherry j i := by
  obtain ⟨hij, hrest⟩ := h
  refine ⟨hij.symm, ?_⟩
  intro k l hkj hki hlj hli
  obtain ⟨h1, h2⟩ := hrest k l hki hkj hli hlj
  constructor
  · rw [δ.symm j i]; linarith
  · rw [δ.symm j i]; linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **形态引理**：**任意**樱桃对**任意**非樱桃对都「形态合格」——
二者要么不交（`DisjointPairs`），要么恰交一个标签（`SharesOneLabel`）。

⇒ ★★ `IsCherrySeparated` 的两条分支合起来覆盖**所有**樱桃，其形态前提**永不落空**；
这也是 ★★★ `atteson_lemma11_gap_order_form_holds` 能用**同一个**樱桃为所有非樱桃对作证的原因。 -/
theorem disjointPairs_or_sharesOneLabel_of_isCherry {δ : Dissimilarity X} {i j k l : X}
    (hch : δ.IsCherry i j) (hnc : ¬ δ.IsCherry k l) :
    DisjointPairs i j k l ∨ SharesOneLabel i j k l := by
  -- 若 `i, j` 都在 `{k,l}` 里，则 `{i,j} = {k,l}`，与 `¬IsCherry k l` 矛盾
  have hkey : ¬ ((i = k ∨ i = l) ∧ (j = k ∨ j = l)) := by
    rintro ⟨hi, hj⟩
    apply hnc
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact absurd rfl hch.1
    · exact hch
    · exact IsCherry.swap hch
    · exact absurd rfl hch.1
  have hsplit : ¬ (i = k ∨ i = l) ∨ ¬ (j = k ∨ j = l) := by
    rcases Classical.em (i = k ∨ i = l) with hi | hi
    · exact Or.inr (fun hj => hkey ⟨hi, hj⟩)
    · exact Or.inl hi
  rcases hsplit with hi | hj
  · have hik : i ≠ k := fun h => hi (Or.inl h)
    have hil : i ≠ l := fun h => hi (Or.inr h)
    rcases Classical.em (j = k) with hjk | hjk
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hjk, hik, hil⟩)))
    rcases Classical.em (j = l) with hjl | hjl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hjl, hik, hil⟩)))
    · exact Or.inl ⟨hik, hil, hjk, hjl⟩
  · have hjk : j ≠ k := fun h => hj (Or.inl h)
    have hjl : j ≠ l := fun h => hj (Or.inr h)
    rcases Classical.em (i = k) with hik | hik
    · exact Or.inr (Or.inl ⟨hik, hjk, hjl⟩)
    rcases Classical.em (i = l) with hil | hil
    · exact Or.inr (Or.inr (Or.inl ⟨hil, hjk, hjl⟩))
    · exact Or.inl ⟨hik, hil, hjk, hjl⟩

omit [DecidableEq X] in
/-- ★★★ **缺口 1 已证成**：`atteson_lemma11_gap_order_form` 是**定理**（无任何数学假设）。

证明路线与「诚实边界」见本节抬头（`### 8.1`）：`Q`-最小点必为樱桃
（`maxZCherryCore` + `nj_cherry`）⇒ 非樱桃对的 `Q` 严格更大 ⇒ 形态引理给出统一证人
⇒ `δmin := gap / (3n)`。**不用**实现树层与 Lemma 10 的权重公式。 -/
theorem atteson_lemma11_gap_order_form_holds (δ : Dissimilarity X) : atteson_lemma11_gap_order_form δ := by
  classical
  intro hfp _hpd hcard
  -- ① `4 ≤ |X|` 给出互异两点
  have hc1 : 1 < Fintype.card X := by omega
  obtain ⟨a0⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b0, hb0⟩ := Fintype.exists_ne_of_one_lt_card hc1 a0
  -- ② `Q` 的全局最小点（有限集上取最小）
  have hne2 : ((Finset.univ : Finset (X × X)).filter (fun p => p.1 ≠ p.2)).Nonempty :=
    ⟨(a0, b0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0.symm⟩⟩
  obtain ⟨⟨a, b⟩, hpab, hmin'⟩ :=
    Finset.exists_min_image ((Finset.univ : Finset (X × X)).filter (fun p => p.1 ≠ p.2))
      (fun p : X × X => δ.Q p.1 p.2) hne2
  have hab : a ≠ b := (Finset.mem_filter.mp hpab).2
  have hmin : ∀ i j : X, i ≠ j → δ.Q a b ≤ δ.Q i j := fun i j hij =>
    hmin' (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
  -- ③ 最小点是樱桃
  have hch : δ.IsCherry a b := nj_cherry δ (maxZCherryCore δ) hfp a b hab hmin
  -- ④ 非樱桃对的 `Q` **严格**更大
  have hstrict : ∀ k l : X, k ≠ l → ¬ δ.IsCherry k l → δ.Q a b < δ.Q k l := by
    intro k l hkl hnc
    rcases lt_or_eq_of_le (hmin k l hkl) with h | h
    · exact h
    · exfalso
      exact hnc (nj_cherry δ (maxZCherryCore δ) hfp k l hkl
        (fun i j hij => by rw [← h]; exact hmin i j hij))
  -- ⑤ 非樱桃对的集合
  set P : Finset (X × X) :=
    (Finset.univ : Finset (X × X)).filter (fun p => p.1 ≠ p.2 ∧ ¬ δ.IsCherry p.1 p.2)
    with hP
  by_cases hPne : P.Nonempty
  · -- ⑥ 非平凡情形：取最小间隙
    obtain ⟨w, hw⟩ := hPne
    set G : Finset ℝ := P.image (fun p : X × X => δ.Q p.1 p.2 - δ.Q a b) with hG
    have hGne : G.Nonempty := by
      rw [hG]
      exact ⟨_, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
    set gap : ℝ := G.min' hGne with hgap
    have hgappos : 0 < gap := by
      have hmem : gap ∈ G := by rw [hgap]; exact Finset.min'_mem G hGne
      rw [hG] at hmem
      obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hmem
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.1
      have hpnc : ¬ δ.IsCherry p.1 p.2 := (Finset.mem_filter.mp hp).2.2
      have hs := hstrict p.1 p.2 hpne hpnc
      linarith [hpv, hgap]
    have hnpos : (0 : ℝ) < (Fintype.card X : ℝ) := by
      have h4 : (4 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
      linarith
    set δmin : ℝ := gap / (3 * (Fintype.card X : ℝ)) with hδmin
    have hδminpos : 0 < δmin := by
      rw [hδmin]; exact div_pos hgappos (by linarith)
    have hgapdiv : 3 * (Fintype.card X : ℝ) * δmin = gap := by
      rw [hδmin]; field_simp
    refine ⟨δmin, hδminpos, ?_⟩
    intro k l hkl hnc
    have hmemP : (k, l) ∈ P := by
      rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl, hnc⟩
    have hmemG : δ.Q k l - δ.Q a b ∈ G := by
      rw [hG]; exact Finset.mem_image.mpr ⟨(k, l), hmemP, rfl⟩
    have hgaple : gap ≤ δ.Q k l - δ.Q a b := by
      rw [hgap]; exact Finset.min'_le G _ hmemG
    refine ⟨a, b, hch, ?_⟩
    rcases disjointPairs_or_sharesOneLabel_of_isCherry (k := k) (l := l) hch hnc with
      hdis | hsh
    · refine Or.inl ⟨hdis, ?_⟩
      have hcoef : 3 * ((Fintype.card X : ℝ) - 4) ≤ 3 * (Fintype.card X : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hδminpos)
      linarith [hmul, hgapdiv, hgaple]
    · refine Or.inr ⟨hsh, ?_⟩
      have hcoef : 2 * ((Fintype.card X : ℝ) - 3) ≤ 3 * (Fintype.card X : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hδminpos)
      linarith [hmul, hgapdiv, hgaple]
  · -- ⑦ 空真情形：所有互异对都是樱桃
    refine ⟨1, one_pos, ?_⟩
    intro k l hkl hnc
    have hmemP : (k, l) ∈ P := by
      rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl, hnc⟩
    exact absurd ⟨(k, l), hmemP⟩ hPne


/-! ### 8.1.2 ★ W39-3：`_order_form` 在**具体树度量**上的实例（逐项实算，非特化）

上一节把 `atteson_lemma11_gap_order_form` 证成「对一切 `δ` 成立」——但**特化一条 `∀δ` 定理
是零信息量的**，所以那不能算「这条缺口被用在具体对象上」（W35 审计对 15 条的口径即此）。

本节给的是**不经过上一节**的实例：取 ★C 的 4 叶真树度量 `exDiss`（树 `((0,1),(2,3))`，
挂边 `1,2,3,4`、内部边 `5`），**逐对算出** `Q` 并直接给出 `δmin = 5`：

* 两颗樱桃 `(0,1)`、`(2,3)` 上 `Q = −40`；四个交叉对（非樱桃）上 `Q = −30`；
* ⇒ 间隙 `Q(k,l) − Q(i,j) = 10 = 2·(n−3)·5`（`n = 4`，`SharesOneLabel` 分支），
  与 Atteson Lemma 11 的 `2(n−3)·δmin` 常数**逐字吻合**，`δmin := 5` 是它的精确解
  （不是 `∃` 里随便取的数）。

⇒ 这条缺口从「无实例」升为**有非退化实例**：具体 4 叶树上是真的，且常数看得见。 -/

/-- ★C 的 `exDiss` 上 `(2,3)` 也是樱桃（与 `exDiss_isCherry_01` 对称）。 -/
theorem exDiss_isCherry_23 : exDiss.IsCherry 2 3 := by
  refine ⟨by decide, ?_⟩
  intro k l hk2 hk3 hl2 hl3
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp_all
  have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp_all
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
    (simp only [exDiss, exVal]; constructor <;> norm_num)

/-- ★★★ **`exDiss` 上 `IsCherrySeparated` 的具体常数**：`δmin = 5`。

逐对验证：12 个异于对角的有序对里，4 个是樱桃（`(0,1),(1,0),(2,3),(3,2)`，被前提排除），
其余 8 个交叉对都以 `(0,1)` 为证人、走 `SharesOneLabel` 分支，间隙恰为 `10 = 2·(4−3)·5`。 -/
theorem exDiss_isCherrySeparated_five : exDiss.IsCherrySeparated (X := Fin 4) 5 := by
  intro k l hkl hnc
  fin_cases k <;> fin_cases l <;> first
    | (exfalso; exact hkl rfl)
    | (exfalso; exact hnc exDiss_isCherry_01)
    | (exfalso; exact hnc exDiss_isCherry_01.swap)
    | (exfalso; exact hnc exDiss_isCherry_23)
    | (exfalso; exact hnc exDiss_isCherry_23.swap)
    | exact ⟨0, 1, exDiss_isCherry_01, Or.inr ⟨by unfold SharesOneLabel; decide, by
        simp only [Dissimilarity.Q, Fintype.card_fin, sum_univ_four_fin, exDiss, exVal]
        norm_num⟩⟩

/-- ★ W39-3：**`_order_form` 在具体对象上的实例** —— `exDiss` 满足该缺口，
`δmin = 5` 逐项算出（`exDiss_isCherrySeparated_five`）。

注意：本定理**不**调用 `atteson_lemma11_gap_order_form_holds`，故它是实例而不是特化。 -/
theorem atteson_lemma11_gap_order_form_at_exDiss :
    atteson_lemma11_gap_order_form (X := Fin 4) exDiss :=
  fun _ _ _ => ⟨5, by norm_num, exDiss_isCherrySeparated_five⟩

/-- ⚠️ **已证伪，非待证目标** —— 机器反例见 `atteson_reduction_gap_refuted`（`Phylo/AttesonRadius.lean:1144`）。
★★★ **缺口 2：Atteson Lemma 6 的归约步**（`:677–694` 边权公式 (7)），
即 Theorem 1（`:868–916`）归纳不变量 (a)(b) 的递推。

设 `δ` 可加（`FourPoint`）、`(i,j)` 是 `δ` 的樱桃、`θ ∈ [0,1]`。则把 `i,j` 按更新式 (6)
（`:611`）合并成新标签后，在**商标签集** `Y` 上得到的 `δm` 满足：
`card Y + 1 = card X`、非 `{i,j}` 对的取值不变、新标签处的取值是凸组合、
且 `δm.FourPoint`（⇒ 仍是可加的、更小的实例）。

**为什么落成 `Prop`（而非定理）**：本库的 `Dissimilarity` 固定在**单一类型** `X` 上，
「合并两个标签」需要类型迁移 `X ↝ (X \ {i,j}) ∪ {u}`；`Phylogram` 也没有
「合并樱桃后重取实现树」的接口。Atteson `:688–694` 的式 (7) 还额外给出
**每条边长度只增不减**，从而 `min_e l_{m+1}(e) ≥ min_e l_m(e)`（`:912–914`）——
这是归纳不变量 (b)，本 `Prop` 未把它形式化（需要边权层）。

✦ **「扰动不放大」（Lemma 7，`:749–751`）的对应部分已由 ★★ `linfClose_update` 证出**，
故缺口只剩「可加 + 最短边长不降」这一半。 -/
def atteson_reduction_gap : Prop :=
  ∀ (δ : Dissimilarity X) (i j : X) (θ : ℝ),
    δ.IsCherry i j → δ.FourPoint → 0 ≤ θ → θ ≤ 1 →
      ∃ (Y : Type) (_ : Fintype Y) (_ : DecidableEq Y) (q : X → Y) (δm : Dissimilarity Y),
        Fintype.card Y + 1 = Fintype.card X ∧
        (∀ x y : X, x ≠ i → x ≠ j → y ≠ i → y ≠ j →
          q x ≠ q y ∧ δm.val (q x) (q y) = δ.val x y) ∧
        (∀ x : X, x ≠ i → x ≠ j →
          δm.val (q x) (q j) = θ * δ.val x i + (1 - θ) * δ.val x j) ∧
        δm.FourPoint

/-- 反空真：缺口 2 的**前提**在 ★C 例子中可满足
（存在樱桃、满足四点条件、`θ = 1/2 ∈ [0,1]`）。 -/
theorem atteson_reduction_gap_hypotheses_nonempty :
    exDiss.IsCherry 0 1 ∧ exDiss.FourPoint ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 :=
  ⟨exDiss_isCherry_01, exDiss_fourPoint, by norm_num, by norm_num⟩

/-! ## 9. ★★★ 归约步的 `FourPoint` 一半（W12e2）

`atteson_reduction_gap`（§8）要求：把樱桃 `i,j` 按 `f x = θ·δ x i + (1−θ)·δ x j` 合并成新叶 `u`
后，得到的 `δm` 仍满足四点条件。**这一半只用到 `IsCherry i j + FourPoint`**（不需要树层），
本节把它证成定理；剩下的**类型迁移** `X ↝ (X∖{i,j})∪{u}`（连同 `Dissimilarity` 构造、
`card Y + 1 = card X`）**仍是缺口**。

★D 命题核查：先在 `scripts/msc/w12e2_merge_fourpoint_check.py` 上穷举核过
（5 叶全部二叉拓扑 × 有理边权网格 × `θ ∈ {0,1/4,1/2,3/4,1}` ⇒ 1 187 500 次检查 0 反例；
5 点整值度量 `{1,2,3}` 全枚举 59 049 个，其中 653 个满足 `FourPoint ∧ IsCherry`，
**0 反例**）后才动手证明。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **樱桃的交叉相等**：`FourPoint` ＋ `IsCherry i j` ⟹ 对任意 `b,c ∉ {i,j}`，

　　`δ i b + δ j c = δ i c + δ j b`

（树层即「`i,j` 相邻」的交叉相等；证明用 `FourPoint (i,b,j,c)` 的两个析取支搭配
`IsCherry` 的两条不等式，再对 `b,c` 互换一次得反向不等式）。 -/
theorem IsCherry.cross_eq (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {b c : X}
    (hb : b ≠ i) (hb' : b ≠ j) (hc : c ≠ i) (hc' : c ≠ j) :
    δ.val i b + δ.val j c = δ.val i c + δ.val j b := by
  have h1 : δ.val i b + δ.val j c ≤ δ.val i c + δ.val j b := by
    rcases hfp i b j c with h | h
    · have h2 := (hch.2 b c hb hb' hc hc').2
      linarith
    · simpa [δ.symm b j] using h
  have h2 : δ.val i c + δ.val j b ≤ δ.val i b + δ.val j c := by
    rcases hfp i c j b with h | h
    · have h3 := (hch.2 c b hc hc' hb hb').2
      linarith
    · simpa [δ.symm c j] using h
  linarith

omit [Fintype X] [DecidableEq X] in
set_option linter.unusedVariables false in
/-- ★★★ **凸合并的四点条件（W12e2）**：`δ` 满足四点条件、`i,j` 是樱桃、`θ ∈ [0,1]`、
`a,b,c ∉ {i,j}`。则「把 `i,j` 合并成新叶 `u`（`d(u,x) = θ·δ x i + (1−θ)·δ x j`）」后，
四元组 `(u,a,b,c)` 满足四点条件（库内 `FourPoint` 的析取形态；`δ.val i a` 即 `δ.val a i`）。

证明：设 `A_i = δ i a + δ b c`、`P_i = δ i b + δ a c`、`Q_i = δ i c + δ a b`（`j` 同理），
由 ★★ `IsCherry.cross_eq` 得 `P_i − Q_i = P_j − Q_j`；对 `FourPoint (i,a,b,c)` 与
`FourPoint (j,a,b,c)` 的两个析取支做 4 组分类讨论，再用 `θ ≥ 0`、`1 − θ ≥ 0` 加权即得。

⚠️ `a ≠ i`、`a ≠ j` 属「`a` 未被合并」这一类型迁移前提，在纯算术证明里不出现，
故仅对本条声明关掉 `linter.unusedVariables`。 -/
theorem fourPoint_merge (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {a b c : X}
    (ha : a ≠ i) (ha' : a ≠ j) (hb : b ≠ i) (hb' : b ≠ j) (hc : c ≠ i) (hc' : c ≠ j) :
    θ * δ.val i a + (1 - θ) * δ.val j a + δ.val b c ≤
        θ * δ.val i b + (1 - θ) * δ.val j b + δ.val a c ∨
      θ * δ.val i a + (1 - θ) * δ.val j a + δ.val b c ≤
        θ * δ.val i c + (1 - θ) * δ.val j c + δ.val a b := by
  have hce := IsCherry.cross_eq δ hfp hch hb hb' hc hc'
  have hDD : δ.val i b + δ.val a c - (δ.val i c + δ.val a b)
      = δ.val j b + δ.val a c - (δ.val j c + δ.val a b) := by linarith
  have hθ1 : (0 : ℝ) ≤ 1 - θ := by linarith
  rcases hfp i a b c with hAi | hAi
  · rcases hfp j a b c with hAj | hAj
    · left; nlinarith [hAi, hAj, h0, hθ1]
    · by_cases hcase : δ.val i b + δ.val a c ≤ δ.val i c + δ.val a b
      · right; nlinarith [hAi, hcase, hAj, h0, hθ1]
      · left
        have hPj : δ.val j c + δ.val a b ≤ δ.val j b + δ.val a c := by
          linarith [hDD, not_le.mp hcase]
        nlinarith [hAi, hAj, hPj, h0, hθ1]
  · rcases hfp j a b c with hAj | hAj
    · by_cases hcase2 : δ.val j b + δ.val a c ≤ δ.val j c + δ.val a b
      · right; nlinarith [hAi, hAj, hcase2, h0, hθ1]
      · left
        have hPi : δ.val i c + δ.val a b ≤ δ.val i b + δ.val a c := by
          linarith [hDD, not_le.mp hcase2]
        nlinarith [hAi, hPi, hAj, h0, hθ1]
    · right; nlinarith [hAi, hAj, h0, hθ1]
/-! ## 10. ★★★ 类型迁移 `X ↝ (X∖{i,j}) ∪ {u}`（W12e3）

W12e2 已把归约步的 `FourPoint` 一半证成 ★★★ `fourPoint_merge`；本节补齐**装置**：
标签类型 `Y`、合并映射 `q`、相异度 `δm`、基数等式，以及缺口的三条取值性质与 `δm.FourPoint`。

⚠️ **★D 命题核查（先说结论）**：§8 的原 `def atteson_reduction_gap` 的第二条合取
`∀ x y, x ≠ i → x ≠ j → y ≠ i → y ≠ j → q x ≠ q y ∧ …` 在 `x = y` 时要求 `q x ≠ q x` ——
**为假**（★★★ `atteson_reduction_gap_refuted`，用 ★C 例子 `exDiss` 与 `x = y = 2`）。
⇒ 本节的**修复形态** `atteson_reduction_gap_correct_shape` 只补一条 `x ≠ y`
（★★★ `atteson_reduction_gap_correct_shape_proved` 把它**证成定理**）。 -/

/-- ★★★ **反例检查：`atteson_reduction_gap` 为假**（第二条合取在 `x = y` 时自相矛盾）。

取 ★C 例子 `exDiss`（`Fin 4`，`i = 0`、`j = 1`、`θ = 1/2`；前提由 ★★ `exDiss_isCherry_01`
与 ★★ `exDiss_fourPoint` 给出）与 `x = y = 2 ∉ {0,1}`：该合取要求 `q 2 ≠ q 2`，矛盾。 -/
theorem atteson_reduction_gap_refuted : ¬ atteson_reduction_gap (X := Fin 4) := by
  intro h
  obtain ⟨Y, _, _, q, δm, _, hval, _, _⟩ :=
    h exDiss 0 1 (1 / 2) exDiss_isCherry_01 exDiss_fourPoint (by norm_num) (by norm_num)
  exact (hval 2 2 (by decide) (by decide) (by decide) (by decide)).1 rfl

/-- ★★★ **旧标签类型** `X ∖ {i,j}`（Finset 子类型：基数由 `Finset.card_sdiff` 直接给出）。 -/
abbrev MergeOld (X : Type*) [Fintype X] [DecidableEq X] (i j : X) :=
  ↥((Finset.univ : Finset X) \ {i, j})

/-- ★★★ **合并后的标签类型** `Y = (X∖{i,j}) ∪ {u}`，新标签 `u = Sum.inr ()`。 -/
abbrev MergeIdx (X : Type*) [Fintype X] [DecidableEq X] (i j : X) :=
  MergeOld X i j ⊕ Unit

/-- ★★★ **合并映射** `q : X → Y`：`i, j ↦ u`，其余 `x ↦ inl x`。 -/
noncomputable def mergeQ (i j : X) : X → MergeIdx X i j :=
  fun x => if h : x = i ∨ x = j then Sum.inr () else Sum.inl ⟨x, by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact not_or.mp h⟩

theorem mergeQ_of_ne {x : X} (hx : x ≠ i) (hy : x ≠ j) :
    mergeQ i j x = Sum.inl ⟨x, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨hx, hy⟩⟩ := by
  rw [mergeQ]
  exact dite_eq_right (fun h => h.elim hx hy)

theorem mergeQ_i : mergeQ i j i = (Sum.inr () : MergeIdx X i j) := by
  rw [mergeQ]
  exact dite_eq_left (Or.inl rfl)

theorem mergeQ_j : mergeQ i j j = (Sum.inr () : MergeIdx X i j) := by
  rw [mergeQ]
  exact dite_eq_left (Or.inr rfl)

/-- 旧标签的分量不等于 `i`。 -/
theorem mergeOld_ne_left (a : MergeOld X i j) : a.1 ≠ i := by
  have h := a.2
  rw [Finset.mem_sdiff] at h
  intro hi
  exact h.2 (by rw [hi]; exact Finset.mem_insert_self i {j})

/-- 旧标签的分量不等于 `j`。 -/
theorem mergeOld_ne_right (a : MergeOld X i j) : a.1 ≠ j := by
  have h := a.2
  rw [Finset.mem_sdiff] at h
  intro hj
  exact h.2 (by rw [hj]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))

/-- ★★★ **合并度量**：旧–旧取 `δ`，`u`–旧取凸组合 `θ·δ i x + (1−θ)·δ j x`，`u`–`u` 取 `0`。 -/
noncomputable def mergeVal (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    MergeIdx X i j → MergeIdx X i j → ℝ
  | Sum.inl x, Sum.inl y => δ.val x.1 y.1
  | Sum.inl x, Sum.inr _ => θ * δ.val i x.1 + (1 - θ) * δ.val j x.1
  | Sum.inr _, Sum.inl y => θ * δ.val i y.1 + (1 - θ) * δ.val j y.1
  | Sum.inr _, Sum.inr _ => 0

theorem mergeVal_symm (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    ∀ a b : MergeIdx X i j, mergeVal δ i j θ a b = mergeVal δ i j θ b a := by
  intro a b
  cases a with
  | inl x =>
    cases b with
    | inl y => exact δ.symm x.1 y.1
    | inr u => rfl
  | inr u =>
    cases b with
    | inl y => rfl
    | inr v => rfl

theorem mergeVal_self (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    ∀ a : MergeIdx X i j, mergeVal δ i j θ a a = 0 := by
  intro a
  cases a with
  | inl x => exact δ.diag x.1
  | inr u => rfl

/-- ★★★ **合并相异度** `δm : Dissimilarity Y`（类型迁移的产物）。

⚠️ 库内 `Dissimilarity` 只有 `val` / `symm` / `diag` **三个字段**，**没有**三角不等式字段
（`Phylo/Algorithm/NJ.lean:61`），故构造只需这三条。 -/
noncomputable def mergeDissim (δ : Dissimilarity X) (i j : X) (θ : ℝ) :
    Dissimilarity (MergeIdx X i j) where
  val := mergeVal δ i j θ
  symm := mergeVal_symm δ i j θ
  diag := mergeVal_self δ i j θ

/-- ★★★ **基数**：`card Y + 1 = card X`（`i ≠ j` 取自 `IsCherry` 的第一项）。 -/
theorem card_mergeIdx (hij : i ≠ j) :
    Fintype.card (MergeIdx X i j) + 1 = Fintype.card X := by
  classical
  have hpair : ({i, j} : Finset X).card = 2 := Finset.card_pair_eq_two_iff.mpr hij
  have hle : 2 ≤ Fintype.card X := by
    have h := Finset.card_le_card (Finset.subset_univ ({i, j} : Finset X))
    rwa [Finset.card_univ, hpair] at h
  have hcard : ((Finset.univ : Finset X) \ {i, j}).card = Fintype.card X - 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      hpair]
  have hcoe : Fintype.card (MergeOld X i j) = ((Finset.univ : Finset X) \ {i, j}).card :=
    Fintype.card_coe _
  rw [Fintype.card_sum, Fintype.card_unit, hcoe, hcard]
  omega

/-- ★★★ **旧–旧取值不变**（修复形态：`x ≠ y` 是原缺口漏掉的那一条）。 -/
theorem mergeDissim_val_of_ne (δ : Dissimilarity X) (i j : X) (θ : ℝ) {x y : X}
    (hx : x ≠ i) (hx' : x ≠ j) (hy : y ≠ i) (hy' : y ≠ j) (hxy : x ≠ y) :
    mergeQ i j x ≠ mergeQ i j y ∧
      (mergeDissim δ i j θ).val (mergeQ i j x) (mergeQ i j y) = δ.val x y := by
  constructor
  · rw [mergeQ, mergeQ, dite_eq_right (fun h => h.elim hx hx'),
      dite_eq_right (fun h => h.elim hy hy')]
    intro h
    exact hxy (congrArg Subtype.val (Sum.inl.inj h))
  · rw [mergeQ, mergeQ, dite_eq_right (fun h => h.elim hx hx'),
      dite_eq_right (fun h => h.elim hy hy')]
    rfl

/-- ★★★ **新标签处取凸组合**：`δm.val (q x) (q j) = θ·δ x i + (1−θ)·δ x j`。 -/
theorem mergeDissim_val_merged (δ : Dissimilarity X) (i j : X) (θ : ℝ) {x : X}
    (hx : x ≠ i) (hx' : x ≠ j) :
    (mergeDissim δ i j θ).val (mergeQ i j x) (mergeQ i j j)
      = θ * δ.val x i + (1 - θ) * δ.val x j := by
  rw [mergeQ, dite_eq_right (fun h => h.elim hx hx'), mergeQ, dite_eq_left (Or.inr rfl)]
  show θ * δ.val i x + (1 - θ) * δ.val j x = θ * δ.val x i + (1 - θ) * δ.val x j
  rw [δ.symm x i, δ.symm x j]

/-- ★★★ **含新标签（首位）的四点条件**：由 ★★★ `fourPoint_merge` 直接得到。 -/
theorem mergeDissim_fourPoint_merged (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b c : MergeOld X i j) :
    (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl a)
        + (mergeDissim δ i j θ).val (Sum.inl b) (Sum.inl c) ≤
      (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl b)
        + (mergeDissim δ i j θ).val (Sum.inl a) (Sum.inl c) ∨
    (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl a)
        + (mergeDissim δ i j θ).val (Sum.inl b) (Sum.inl c) ≤
      (mergeDissim δ i j θ).val (Sum.inr ()) (Sum.inl c)
        + (mergeDissim δ i j θ).val (Sum.inl a) (Sum.inl b) :=
  fourPoint_merge δ hfp hch h0 h1 (mergeOld_ne_left a) (mergeOld_ne_right a)
    (mergeOld_ne_left b) (mergeOld_ne_right b) (mergeOld_ne_left c) (mergeOld_ne_right c)

/-- ★★★ **`δm` 满足四点条件**（16 种「新旧标签分布」逐个处理）：

* 全旧标签：就是 `δ.FourPoint`；
* 恰一个新标签（4 个位置）：归约到 ★★★ `fourPoint_merge`（不同位置对应老标签的置换）；
* 两个新标签：`d(u,u) = 0`，需要 `δ x y ≤ d(u,x) + d(u,y)`（`hH1`，由
  `FourPoint (x,y,i,i)` 与 `(x,y,j,j)` 的凸组合给出）；
* 三个/四个新标签：两侧同值时用对称性收口。

故 `δm.FourPoint` **不再需要额外假设**（`Dissimilarity` 无三角不等式字段，
退化四元组由 `FourPoint` 的自身实例补足）。 -/
theorem mergeDissim_fourPoint (δ : Dissimilarity X) (hfp : δ.FourPoint) {i j : X}
    (hch : δ.IsCherry i j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (mergeDissim δ i j θ).FourPoint := by
  intro a b c d
  have hθ1 : (0 : ℝ) ≤ 1 - θ := by linarith
  have hH1 : ∀ x y : MergeOld X i j,
      δ.val x.1 y.1 ≤ (θ * δ.val i x.1 + (1 - θ) * δ.val j x.1)
        + (θ * δ.val i y.1 + (1 - θ) * δ.val j y.1) := by
    intro x y
    have hx : δ.val x.1 y.1 ≤ δ.val i x.1 + δ.val i y.1 := by
      rcases hfp x.1 y.1 i i with h | h <;>
        linarith [h, δ.diag i, δ.symm x.1 i, δ.symm y.1 i]
    have hy : δ.val x.1 y.1 ≤ δ.val j x.1 + δ.val j y.1 := by
      rcases hfp x.1 y.1 j j with h | h <;>
        linarith [h, δ.diag j, δ.symm x.1 j, δ.symm y.1 j]
    nlinarith [hx, hy, h0, hθ1]
  rcases a with x | ua <;> rcases b with y | ub <;> rcases c with z | uc <;>
      rcases d with w | ud <;>
    simp only [mergeDissim, mergeVal]
  · exact hfp x.1 y.1 z.1 w.1
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 z x y with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · right; linarith [h, δ.symm z.1 y.1]
    · left; linarith [h, δ.symm z.1 x.1]
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 w x y with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · left; linarith [h, δ.symm w.1 y.1]
    · right; linarith [h, δ.symm w.1 x.1]
  · exact Or.inl (by linarith [hH1 x y])
  · rcases mergeDissim_fourPoint_merged δ hfp hch h0 h1 x z w with h | h <;>
      simp only [mergeDissim, mergeVal] at h
    · right; linarith
    · left; linarith
  · right; linarith
  · left; linarith
  · left; linarith
  · simpa only [mergeDissim, mergeVal] using
      mergeDissim_fourPoint_merged δ hfp hch h0 h1 y z w
  · left; linarith
  · right; linarith
  · left; linarith
  · exact Or.inl (by linarith [hH1 z w])
  · left; linarith
  · left; linarith
  · left; linarith

/-! ## 11. ★★★ 修复形态：把 `x ≠ y` 补回第二条合取 -/

universe u

/-- ★★★ **`atteson_reduction_gap` 的修复形态**：与 §8 的原缺口**只差一处实质内容**
—— 补回 `x ≠ y`（原缺口在 `x = y` 时自相矛盾，见 ★★★ `atteson_reduction_gap_refuted`）。

⚠️ 另有一处**写法层面**的调整：`Y` 的宇宙随 `X` 走（`Type u`）。原缺口写死 `Type`
（即 `Type 0`），这在 `X : Type u`（`u > 0`）时要求一个**小类型** `Y : Type 0`；
数学上仍可满足（取 `Y := Fin (card X - 1)`），但需把 `δm` 沿一个枚举搬运。
本节的重心是数学内容（`δm.FourPoint`），故采用与 `X` 同宇宙的 `Y`（本 `def` 形如
`Phylo/ConsensusAxioms.lean` 的 `mnCorollary_gap`：把 `X` 量化在 `Prop` 内）。 -/
def atteson_reduction_gap_correct_shape : Prop :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X] (δ : Dissimilarity X) (i j : X) (θ : ℝ),
    δ.IsCherry i j → δ.FourPoint → 0 ≤ θ → θ ≤ 1 →
      ∃ (Y : Type u) (_ : Fintype Y) (_ : DecidableEq Y) (q : X → Y) (δm : Dissimilarity Y),
        Fintype.card Y + 1 = Fintype.card X ∧
        (∀ x y : X, x ≠ i → x ≠ j → y ≠ i → y ≠ j → x ≠ y →
          q x ≠ q y ∧ δm.val (q x) (q y) = δ.val x y) ∧
        (∀ x : X, x ≠ i → x ≠ j →
          δm.val (q x) (q j) = θ * δ.val x i + (1 - θ) * δ.val x j) ∧
        δm.FourPoint

/-- ★★★ **修复形态已证成**（W12e3 收口）：类型迁移装置 `Y := (X∖{i,j}) ∪ {u}`、`q := mergeQ`、
`δm := mergeDissim` 一次性满足全部四条（基数、旧–旧不变、凸组合、`δm.FourPoint`）。

⇒ `atteson_reduction_gap` 的**唯一**障碍只是陈述层面的 `x ≠ y`（已修），
数学内容（`δm.FourPoint`）由 ★★★ `fourPoint_merge` 承担。 -/
theorem atteson_reduction_gap_correct_shape_proved :
    atteson_reduction_gap_correct_shape := by
  classical
  intro α _ _ δ i j θ hch hfp h0 h1
  exact ⟨MergeIdx α i j, inferInstance, inferInstance, mergeQ i j, mergeDissim δ i j θ,
    card_mergeIdx hch.1,
    fun x y hx hx' hy hy' hxy => mergeDissim_val_of_ne δ i j θ hx hx' hy hy' hxy,
    fun x hx hx' => mergeDissim_val_merged δ i j θ hx hx',
    mergeDissim_fourPoint δ hfp hch h0 h1⟩


end Dissimilarity

end NJ

/-! ## 12. ★★★ `sideLeafCount`：删边后一侧子树的**叶数**（W12e5）

Atteson Lemma 10（`:1774–1804`）的权重
`w_e(i,j) = −2`（`e ∈ P_ij`）、`= −2|L − L_i(e)|`（否则）
里出现的 `|L_i(e)|` 就是**删去边 `e` 后与顶点 `i` 同侧的叶数**。
库内已有 `Cladogram.sideLeaves`（`Phylo/Split.lean:529`，用 `T - e` 上的 `Reachable` 实现）
—— 但**只有叶集、没有计数 API**，本节把计数补上并给出基本性质。

⚠️ **本节不做**（仍是 `def atteson_lemma11_gap_order_form` 的缺口，§8/:831 逐字未动）：
① `w_e` 的**权重公式**本身（含 Lemma 10 的逐边比较与「路径旁子树叶数单调性」）；
② `Dissimilarity ↔ ExistsRealizingPhylogram`（`Phylo/Buneman.lean:589`）的桥（`δmin > 0` 来源）。 -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **一侧叶数** `|L_u(e)|`：删去边 `e` 后与顶点 `u` **同侧**（在 `T - e` 中可达）的
叶标签个数 —— Atteson Lemma 10 的 `|L_i(e)|`。 -/
noncomputable def sideLeafCount (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : ℕ :=
  (T.sideLeaves e u).card

omit [DecidableEq X] in
/-- 定义式展开（便于把 `sideLeafCount` 归到已有的 `sideLeaves` 引理上）。 -/
theorem sideLeafCount_eq_card_sideLeaves (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    T.sideLeafCount e u = (T.sideLeaves e u).card := rfl

/-- ★★★ **两侧叶数之和 = 总叶数**（`sideLeaves_compl_adj` 的直接推论）：

　　`|L_a(e)| + |L_b(e)| = |X|`（`e = ⟦a,b⟧` 是树边）。

这就是 Atteson 权重里 `|L − L_i(e)|` 能写成「另一侧的叶数」的原因。 -/
theorem sideLeafCount_add_of_adj (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b) :
    T.sideLeafCount s(a, b) a + T.sideLeafCount s(a, b) b = Fintype.card X := by
  have hle : (T.sideLeaves s(a, b) a).card ≤ Fintype.card X := by
    simpa [Finset.card_univ] using Finset.card_le_univ (T.sideLeaves s(a, b) a)
  rw [sideLeafCount, sideLeafCount, T.sideLeaves_compl_adj hab, Finset.card_compl]
  omega

/-- ★★ **侧不变性**：删边后与 `u` 同侧的顶点给出**同一个**叶集，故同一个计数。
（`sideLeaves` 只依赖 `u` 所在的一侧。） -/
theorem sideLeafCount_eq_of_inSide (T : Cladogram X) {e : Sym2 T.V} {u a : T.V}
    (h : T.inSide e u a) : T.sideLeafCount e u = T.sideLeafCount e a := by
  rw [sideLeafCount, sideLeafCount, T.sideLeaves_eq_of_inSide h]

/-- ★★ **叶边的一侧恰含 1 片叶**（`sideLeaves_leaf_edge` 的计数形式）——

　　`|L_x(⟦x,b⟧)| = 1`（`x` 是叶）。这是本节的**显式数值见证**。 -/
theorem sideLeafCount_leaf_edge (T : Cladogram X) {x : X} {b : T.V}
    (h : T.graph.Adj (T.leaf x) b) : T.sideLeafCount s(T.leaf x, b) (T.leaf x) = 1 := by
  rw [sideLeafCount, T.sideLeaves_leaf_edge h, Finset.card_singleton]

/-- ★★ **含自己那片叶的一侧非空**（`x` 总在自己那一侧）。 -/
theorem sideLeafCount_pos_self (T : Cladogram X) (e : Sym2 T.V) (x : X) :
    0 < T.sideLeafCount e (T.leaf x) :=
  Finset.card_pos.mpr ⟨x, T.mem_sideLeaves_self e x⟩

omit [DecidableEq X] in
/-- ★ **上界**：任一侧的叶数 ≤ 总叶数。 -/
theorem sideLeafCount_le_card (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    T.sideLeafCount e u ≤ Fintype.card X := by
  rw [sideLeafCount]
  exact Finset.card_le_univ (T.sideLeaves e u)

/-- ★★ **真边两侧都含叶**（`sideLeaves_nonempty_of_adj'` 的计数形式）⇒ 任一侧的计数 ≥ 1。 -/
theorem sideLeafCount_pos_of_adj (T : Cladogram X) {a b u : T.V} (hab : T.graph.Adj a b) :
    0 < T.sideLeafCount s(a, b) u :=
  Finset.card_pos.mpr (T.sideLeaves_nonempty_of_adj' hab)

/-- ★★ **任一侧都不是全叶集**（另一侧非空）⇒ 计数 < 总叶数。 -/
theorem sideLeafCount_lt_card_of_adj (T : Cladogram X) {a b u : T.V} (hab : T.graph.Adj a b) :
    T.sideLeafCount s(a, b) u < Fintype.card X := by
  rw [sideLeafCount]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, T.sideLeaves_ne_univ_of_adj (u := u) hab⟩)

/-- ★★★ **端点非叶时一侧含 ≥ 2 片叶**（`two_le_card_sideLeaves` 的计数形式）——
这正是「路径旁子树叶数」单调性论证的**起飞点**。 -/
theorem two_le_sideLeafCount (T : Cladogram X) {u v : T.V} (huv : T.graph.Adj u v)
    (hnd : T.graph.degree u ≠ 1) : 2 ≤ T.sideLeafCount s(u, v) u :=
  T.two_le_card_sideLeaves huv hnd

/-! ### ★B 显式数值见证 -/

/-- ★B **叶边的两侧叶数**：一边 `1`、另一边 `|X| − 1`（`sideLeafCount_leaf_edge` ＋
`sideLeafCount_add_of_adj`；与 `sideLeaves_leaf_edge` 的既有结论（`= {x}`）对照一致）。 -/
example (T : Cladogram X) {x : X} {b : T.V} (h : T.graph.Adj (T.leaf x) b) :
    T.sideLeafCount s(T.leaf x, b) (T.leaf x) = 1 ∧
      T.sideLeafCount s(T.leaf x, b) (T.leaf x)
        + T.sideLeafCount s(T.leaf x, b) b = Fintype.card X :=
  ⟨T.sideLeafCount_leaf_edge h, T.sideLeafCount_add_of_adj h⟩

/-- ★B **反空真**：上面的两条性质在「至少 2 片叶」的树上互不空真。 -/
example (T : Cladogram X) {x : X} {b : T.V} (h : T.graph.Adj (T.leaf x) b) :
    0 < T.sideLeafCount s(T.leaf x, b) b :=
  T.sideLeafCount_pos_of_adj h

end Cladogram


/-! ## 13. ★★★ 等价桥：`e ∈ P_ij` ⟺ `i,j` 分属 `e` 两侧（W12e6）

Atteson Lemma 10（`:1774–1804`）把「路径经过 `e`」与「一侧叶数」互换使用，
本节把这个互换**证出来** —— 于是 §12 的 `sideLeafCount` 能真正接上权重 `w_e`。

器材（全部是库内/Mathlib 既有，★A 扫过）：
`Cladogram.inSide`（`Phylo/Split.lean:633`，就是 `T - e` 上的可达性）、
`Cladogram.mem_sideLeaves_iff_inSide`（`:648`）、
`SimpleGraph.Walk.toDeleteEdge`（`Walk/Maps.lean:275`）、
`SimpleGraph.Walk.transfer` / `edges_transfer`（`Maps.lean:183`）、
`SimpleGraph.Walk.bypass` / `bypass_isPath` / `darts_bypass_sublist_darts`（`CherryQuartet.lean:108` 已在用）、
`SimpleGraph.edgeSet_deleteEdges`（`DeleteEdges.lean:94`）、`Cladogram.existsUnique_path`（`Core.lean:83`）。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **唯一路径**（`existsUnique_path` 的见证；`Cladogram` 版，`Phylogram` 版见 `Phylo.PauplinFormula`）。 -/
noncomputable def pathOf (T : Cladogram X) (u v : T.V) : T.graph.Walk u v :=
  (T.existsUnique_path u v).choose

omit [Fintype X] [DecidableEq X] in
/-- 唯一路径确实是**路径**。 -/
theorem pathOf_isPath (T : Cladogram X) (u v : T.V) : (T.pathOf u v).IsPath :=
  (T.existsUnique_path u v).choose_spec.1

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **避开 `e` 的走法 ⟹ 同侧**（`Walk.toDeleteEdge` 把走法落到 `T - e` 里）。 -/
theorem inSide_of_walk_notMem (T : Cladogram X) {e : Sym2 T.V} {u v : T.V}
    (p : T.graph.Walk u v) (h : e ∉ p.edges) : T.inSide e u v :=
  (p.toDeleteEdge e h).reachable

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **异侧 ⟹ 每条走法都走过 `e`**（上一条的逆否；这就是 `e ∈ P_ij` 的「切割」含义）。 -/
theorem forall_mem_edges_of_not_inSide (T : Cladogram X) {e : Sym2 T.V} {u v : T.V}
    (h : ¬ T.inSide e u v) (p : T.graph.Walk u v) : e ∈ p.edges := by
  by_contra hne
  exact h (T.inSide_of_walk_notMem p hne)

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **同侧 ⟹ 存在避开 `e` 的走法**（把 `T - e` 里的走法沿 `transfer` **抬回** `T`，边表不变）。 -/
theorem exists_walk_notMem_of_inSide (T : Cladogram X) {e : Sym2 T.V} {u v : T.V}
    (h : T.inSide e u v) : ∃ p : T.graph.Walk u v, e ∉ p.edges := by
  obtain ⟨q⟩ := h
  have hq : e ∉ q.edges := by
    intro hmem
    have hset : e ∈ (T.graph.deleteEdges {e}).edgeSet :=
      SimpleGraph.Walk.edges_subset_edgeSet q hmem
    rw [SimpleGraph.edgeSet_deleteEdges] at hset
    exact hset.2 rfl
  exact ⟨q.transfer T.graph (fun f hf => by
      have h1 : f ∈ (T.graph.deleteEdges {e}).edgeSet :=
        SimpleGraph.Walk.edges_subset_edgeSet q hf
      rw [SimpleGraph.edgeSet_deleteEdges] at h1
      exact h1.1),
    by rw [SimpleGraph.Walk.edges_transfer]; exact hq⟩

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **桥（走法版）**：「每条 `u → v` 走法都走过 `e`」⟺「`u,v` 分属 `e` 两侧」。 -/
theorem forall_mem_edges_iff_not_inSide (T : Cladogram X) {e : Sym2 T.V} {u v : T.V} :
    (∀ p : T.graph.Walk u v, e ∈ p.edges) ↔ ¬ T.inSide e u v := by
  constructor
  · intro h hin
    obtain ⟨p, hp⟩ := T.exists_walk_notMem_of_inSide hin
    exact hp (h p)
  · intro h p
    exact T.forall_mem_edges_of_not_inSide h p

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **等价桥（唯一路径版）**：`e ∈ P_uv` ⟺ `u,v` 分属 `e` 两侧。

证明：`⟸` 用 ★★★ `forall_mem_edges_of_not_inSide`；`⟹` 反设同侧，则存在避开 `e` 的走法，
其 `bypass` 是**路径**且边表是子表（故仍避开 `e`），由 `existsUnique_path` 的**唯一性**它必是
`pathOf u v` —— 与 `e ∈ P_uv` 矛盾。

（对**任意** `e : Sym2 T.V` 成立：`e` 不是树边时两边都是 `False`；树边 `e = s(a,b)` 是有意义的情形。） -/
theorem mem_pathOf_edges_iff_not_inSide (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) :
    e ∈ (T.pathOf u v).edges ↔ ¬ T.inSide e u v := by
  constructor
  · intro hmem hin
    obtain ⟨p, hp⟩ := T.exists_walk_notMem_of_inSide hin
    have hsub : List.Sublist p.bypass.edges p.edges := by
      rw [SimpleGraph.Walk.edges_eq_map_darts, SimpleGraph.Walk.edges_eq_map_darts]
      exact (SimpleGraph.Walk.darts_bypass_sublist_darts p).map SimpleGraph.Dart.edge
    have hp' : e ∉ p.bypass.edges := fun hc => hp (hsub.subset hc)
    have hpath : p.bypass.IsPath := SimpleGraph.Walk.bypass_isPath p
    have huniq : p.bypass = T.pathOf u v :=
      (T.existsUnique_path u v).choose_spec.2 p.bypass hpath
    exact hp' (huniq ▸ hmem)
  · intro h
    exact T.forall_mem_edges_of_not_inSide h (T.pathOf u v)

/-- ★★★ **`sideLeaves` 形式**：`y ∉ L_x(e)` ⟺ 唯一路径 `P_{xy}` 走过 `e`
（Atteson 把 `e ∈ P_ij` 与一侧叶集互换使用的正式依据）。 -/
theorem mem_pathOf_edges_iff_notMem_sideLeaves (T : Cladogram X) (e : Sym2 T.V) (x y : X) :
    e ∈ (T.pathOf (T.leaf x) (T.leaf y)).edges ↔ y ∉ T.sideLeaves e (T.leaf x) := by
  rw [T.mem_pathOf_edges_iff_not_inSide]
  constructor
  · intro h hmem
    exact h ((T.mem_sideLeaves_iff_inSide).mp hmem)
  · intro h hcon
    exact h ((T.mem_sideLeaves_iff_inSide).mpr hcon)

/-- ★★ **两侧叶数互补**：`|L_b(e)| = |X| − |L_a(e)|`（`sideLeafCount_add_of_adj` 的直接推论）。 -/
theorem sideLeafCount_compl (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b) :
    T.sideLeafCount s(a, b) b = Fintype.card X - T.sideLeafCount s(a, b) a := by
  have h := T.sideLeafCount_add_of_adj hab
  omega

/-- ★★★ **Atteson Lemma 10 的权重 `w_e(i,j)`**（`:1774–1804`）：
　　路径经过 `e` 时 `−2`，否则 `−2·(|X| − |L_i(e)|)`（`|L_i(e)|` 见 §12 的 `sideLeafCount`）。 -/
noncomputable def attesonW (T : Cladogram X) (i j : T.V) (e : Sym2 T.V) : ℤ :=
  if e ∈ (T.pathOf i j).edges then -2
  else -2 * ((Fintype.card X : ℤ) - (T.sideLeafCount e i : ℤ))

omit [DecidableEq X] in
/-- ★★★ **权重第一支**：异侧（路径走过 `e`）⟹ `w_e = −2`。 -/
theorem attesonW_eq_neg_two_of_not_inSide (T : Cladogram X) {i j : T.V} {e : Sym2 T.V}
    (h : ¬ T.inSide e i j) : T.attesonW i j e = -2 := by
  rw [attesonW, ite_eq_left (T.forall_mem_edges_of_not_inSide h (T.pathOf i j))]

omit [DecidableEq X] in
/-- ★★★ **权重第二支**：同侧 ⟹ `w_e = −2·(|X| − |L_i(e)|)`
（由 `sideLeafCount_compl`，这就是 `−2·|L_j(e)|`，Atteson 的「否则」分支）。 -/
theorem attesonW_eq_sideCount_of_inSide (T : Cladogram X) {i j : T.V} {e : Sym2 T.V}
    (h : T.inSide e i j) :
    T.attesonW i j e = -2 * ((Fintype.card X : ℤ) - (T.sideLeafCount e i : ℤ)) := by
  rw [attesonW, ite_eq_right]
  intro hmem
  exact (T.mem_pathOf_edges_iff_not_inSide e i j).mp hmem h

end Cladogram


/-! ## 14. ★★★ 逐边分解与逐边计数（W12e8）

Atteson Lemma 10（`:1774–1804`）的两步：

1. **`Q(i,j) = Σ_{e} w_e(i,j)·l(e)`** —— 权重沿边的**加权和**（本节 `attesonQ`）；
2. 于是 `Q(k,l) − Q(i,j) = Σ_e (w_e(k,l) − w_e(i,j))·l(e)` —— **逐边分解**（本节 `attesonQ_sub`），
   再对每个 `e` 比较括号里的量（`:2023–2056` 的单调性）。

本节把 (2) 与其中**唯一用到拓扑的一步** ——「走过 `e` 的路径条数 = 另一侧叶数」——
证出来（后者正是 §13 的桥 ＋ §12 的 `sideLeafCount` 的接口）。
⚠️ 完整的 (1)（即 `attesonQ l = NJ 的 Q` 判据）还需要「可加性」`δ(i,k) = Σ_e S_ik(e)·l(e)`
（库内 `Phylo.PauplinFormula` 的 `dist_eq_sum_incidence`，在 `AttesonRadius` 的 import 锥之外）——
**未做**，见本轮报告；`def atteson_lemma11_gap_order_form`（:833）逐字未动。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **`w_e` 的加权和**（Atteson `:1774–1804` 的 `Q(i,j) = Σ_e w_e(i,j)·l(e)` 的左边写法；
`w_e` 见 §13 的 `attesonW`）。 -/
noncomputable def attesonQ (T : Cladogram X) (l : Sym2 T.V → ℝ) (i j : T.V) : ℝ :=
  ∑ e : Sym2 T.V, T.attesonW i j e * l e

omit [DecidableEq X] in
/-- ★★★ **逐边分解**：`Q(k,m) − Q(i,j) = Σ_e (w_e(k,m) − w_e(i,j))·l(e)`。

这就是 Atteson Lemma 10 之后「**逐边比较**」的起点：左边差一个 `Q` 值，右边是逐边贡献之差。 -/
theorem attesonQ_sub (T : Cladogram X) (l : Sym2 T.V → ℝ) (i j k m : T.V) :
    T.attesonQ l k m - T.attesonQ l i j
      = ∑ e : Sym2 T.V, (T.attesonW k m e - T.attesonW i j e) * l e := by
  rw [attesonQ, attesonQ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- ★★★ **逐边计数（集合版）**：叶 `x` 在 `s(a,b)` 的 `a` 侧时，
「`x` 到各叶的路径中走过 `s(a,b)` 的那些叶」**恰好**是 `b` 侧的叶集。

证明 = §13 的桥（`e ∈ P_xk ⟺ 异侧`）＋ `inSide_or_inSide`（每点只在一侧）＋「边是桥」。 -/
theorem filter_pathOf_edges_eq_sideLeaves (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {x : X} (hx : T.inSide s(a, b) a (T.leaf x)) :
    Finset.univ.filter (fun k : X => s(a, b) ∈ (T.pathOf (T.leaf x) (T.leaf k)).edges)
      = T.sideLeaves s(a, b) b := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [T.mem_pathOf_edges_iff_not_inSide, T.mem_sideLeaves_iff_inSide]
  have hxa : T.inSide s(a, b) (T.leaf x) a := (T.inSide_comm (s(a, b)) a (T.leaf x)).mp hx
  constructor
  · intro h
    rcases T.inSide_or_inSide (x := T.leaf k) hab with hk | hk
    · exact absurd (hxa.trans ((T.inSide_comm (s(a, b)) (T.leaf k) a).mp hk)) h
    · exact (T.inSide_comm (s(a, b)) (T.leaf k) b).mp hk
  · intro hk hcon
    exact T.not_reachable_deleteEdges_of_adj hab (hx.trans hcon |>.trans hk.symm)

/-- ★★★ **逐边计数（数值版）**：`#{k : 路径 x→k 走过 s(a,b)} = |L_b(s(a,b))|`
—— Atteson 权重里 `|L − L_i(e)|` 的**路径侧**含义（与 §12 的 `sideLeafCount` 接口对接）。 -/
theorem card_filter_pathOf_edges (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {x : X} (hx : T.inSide s(a, b) a (T.leaf x)) :
    (Finset.univ.filter (fun k : X => s(a, b) ∈ (T.pathOf (T.leaf x) (T.leaf k)).edges)).card
      = T.sideLeafCount s(a, b) b := by
  rw [filter_pathOf_edges_eq_sideLeaves T hab hx]
  rfl

end Cladogram


/-! ## 15. ★★★ 可加性（路径版，W12e9 · 路线 ①）

Atteson Lemma 10 的第一步 `Q(i,j) = Σ_e w_e(i,j)·l(e)` 需要把 `δ(i,j)` 写成**沿路径的加权和**：

　　`d(u,v) = Σ_e [e ∈ P_uv]·w_e`（`[·]` 为指示函数，`w_e = T.wExt e`）。

库内同一条等式是 `Phylo.PauplinFormula.dist_eq_sum_incidence`（用那里的 `pathWalk`/`incidence`），
但 `PauplinFormula → BMELastSquares → AttesonRadius` **方向相反**，本文件引用不到 ⇒ 按 W12e9 派单
**在本文件内自证一份**（与其证明同构：`dist = walkDist` ＋ `walkDist = 边表和` ＋
「边表 → `toFinset` 指示函数」）。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- 唯一路径的边表无重复（`IsPath` 的直接推论）。 -/
theorem pathOf_edges_nodup (T : Cladogram X) (u v : T.V) : (T.pathOf u v).edges.Nodup :=
  SimpleGraph.Walk.edges_nodup_of_support_nodup
    ((SimpleGraph.Walk.isPath_def _).mp (T.pathOf_isPath u v))

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **可加性（路径版）**：`d(u,v) = Σ_e [e ∈ P_uv]·w_e` —— 即 Atteson Lemma 10 里
`δ` 与「边权 + 路径关联」之间的桥（也是 §13 的 `pathOf` 与 §14 的 `attesonQ` 之间的接口）。 -/
theorem dist_eq_sum_pathOf (T : Phylogram X) (u v : T.V) :
    T.dist u v
      = ∑ e : Sym2 T.V, (if e ∈ (T.pathOf u v).edges then T.wExt e else (0 : ℝ)) := by
  have hl : (T.pathOf u v).edges.Nodup := pathOf_edges_nodup T.toCladogram u v
  have h1 : T.dist u v = (T.pathOf u v).edges.toFinset.sum T.wExt := by
    show T.walkDist (T.pathOf u v) = _
    rw [Phylogram.walkDist, List.sum_toFinset T.wExt hl]
  have h2 : (∑ e : Sym2 T.V, (if e ∈ (T.pathOf u v).edges then T.wExt e else (0 : ℝ)))
      = (T.pathOf u v).edges.toFinset.sum T.wExt := by
    have h3 : ∀ e : Sym2 T.V,
        (if e ∈ (T.pathOf u v).edges then T.wExt e else (0 : ℝ))
          = if e ∈ (T.pathOf u v).edges.toFinset then T.wExt e else 0 := by
      intro e
      by_cases h : e ∈ (T.pathOf u v).edges <;> simp [h]
    rw [Finset.sum_congr rfl fun e _ => h3 e, Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h2]

end Cladogram


/-! ## 16. ★★★ 逐边比较：`w_e` = `(n−2)·[异侧] − S_i(e) − S_j(e)`（W12e10）

Atteson Lemma 10 的第 3 步（`:1774–1804` 的核心）：把 `Q(i,j) = (n−2)δ(i,j) − S_i − S_j` 与
`Σ_e w_e(i,j)·l(e)` 逐边对照。对真边 `e = s(a,b)`（`i` 在 `a` 侧，§14 的计数给出
`S_x(e) = Σ_k [e ∈ P_xk] = `**异侧**叶数）：

* **同侧**（`j` 也在 `a` 侧）：`[异侧] = 0`、`S_i = S_j = |L_b(e)|` ⟹ `w_e = −2·|L_b(e)|`；
* **异侧**（`j` 在 `b` 侧）：`[异侧] = 1`、`S_i = |L_b(e)|`、`S_j = |L_a(e)|`
　⟹ `w_e = (n−2) − |L_a| − |L_b| = −2`（用 §12 的 `sideLeafCount_add_of_adj`：`|L_a| + |L_b| = n`）。

两条都是 §13 分支定理（`attesonW_eq_neg_two_of_not_inSide` / `…_of_inSide`）的**直接推论**
（`ℤ → ℝ` cast ＋ `linarith`），为下一轮「`attesonQ T.wExt = (n−2)·d − S_i − S_j` 的求和装配」备好接口。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **逐边比较（同侧）**：`i,j` 同在 `s(a,b)` 的 `a` 侧时 `w_e = −2·|L_b(e)|`
（即 `(n−2)·0 − S_i(e) − S_j(e)`，因 `S_i = S_j = |L_b|`）。 -/
theorem attesonW_cast_eq_Q_same (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b) {i j : X}
    (hi : T.inSide s(a, b) a (T.leaf i)) (hj : T.inSide s(a, b) a (T.leaf j)) :
    (T.attesonW (T.leaf i) (T.leaf j) s(a, b) : ℝ)
      = -2 * (T.sideLeafCount s(a, b) b : ℝ) := by
  have hIn : T.inSide s(a, b) (T.leaf i) (T.leaf j) :=
    ((T.inSide_comm (s(a, b)) a (T.leaf i)).mp hi).trans hj
  have hside : T.sideLeafCount s(a, b) (T.leaf i) = T.sideLeafCount s(a, b) a :=
    T.sideLeafCount_eq_of_inSide ((T.inSide_comm (s(a, b)) a (T.leaf i)).mp hi)
  have hsumR : (T.sideLeafCount s(a, b) a : ℝ) + (T.sideLeafCount s(a, b) b : ℝ)
      = (Fintype.card X : ℝ) := by
    rw [← Nat.cast_add, T.sideLeafCount_add_of_adj hab]
  rw [T.attesonW_eq_sideCount_of_inSide hIn, hside]
  push_cast
  linarith

/-- ★★★ **逐边比较（异侧）**：`i` 在 `a` 侧、`j` 在 `b` 侧时 `w_e = −2`
（即 `(n−2)·1 − S_i(e) − S_j(e)`，因 `S_i = |L_b|`、`S_j = |L_a|` 且 `|L_a| + |L_b| = n`）。 -/
theorem attesonW_cast_eq_Q_opposite (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j : X} (hi : T.inSide s(a, b) a (T.leaf i)) (hj : T.inSide s(a, b) b (T.leaf j)) :
    (T.attesonW (T.leaf i) (T.leaf j) s(a, b) : ℝ)
      = (Fintype.card X : ℝ) - 2
        - (T.sideLeafCount s(a, b) b : ℝ) - (T.sideLeafCount s(a, b) a : ℝ) := by
  have hNot : ¬ T.inSide s(a, b) (T.leaf i) (T.leaf j) := by
    intro hcon
    have hia : T.inSide s(a, b) (T.leaf i) a := (T.inSide_comm (s(a, b)) a (T.leaf i)).mp hi
    have hjb : T.inSide s(a, b) (T.leaf j) b := (T.inSide_comm (s(a, b)) b (T.leaf j)).mp hj
    exact T.not_reachable_deleteEdges_of_adj hab (hia.symm.trans (hcon.trans hjb))
  have hsumR : (T.sideLeafCount s(a, b) a : ℝ) + (T.sideLeafCount s(a, b) b : ℝ)
      = (Fintype.card X : ℝ) := by
    rw [← Nat.cast_add, T.sideLeafCount_add_of_adj hab]
  rw [T.attesonW_eq_neg_two_of_not_inSide hNot]
  push_cast
  linarith

end Cladogram


/-! ## 17. ★★★ 求和装配 ①②③：Fubini 与内层计数（W12e11）

Atteson Lemma 10 的收口 `Q(i,j) = (n−2)δ(i,j) − S_i − S_j = Σ_e w_e(i,j)·l(e)` 需要把
`S_x = Σ_k d(x,k)` 也写成**沿边**的和：

* ① §15 可加性逐项展开 `d(x,k) = Σ_e [e ∈ P_xk]·w_e`；
* ② `Finset.sum_comm`（Fubini）交换两层和；
* ③ `Finset.sum_mul` 把 `w_e` 提出内层和（指示函数归一），再用 §14 的 ★★★
　`card_filter_pathOf_edges`（配 `inSide_or_inSide` 定侧）把内层和换成 `sideLeafCount`：

　　`Σ_k d(i,k) = Σ_e |L_{x_i}(e)|·w_e`，其中 `x_i` 是与叶 `i` **异侧**的 `e` 的端点。

（收口的最后一步 —— 把 `attesonQ` 与上式逐边对照 —— 用 §16 的两条逐边比较即可，
留下轮；本轮把 ①②③ 落成可复用的定理。） -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- ★★★ **Fubini（步骤 ①②③ 的因子部分）**：`Σ_k d(i,k) = Σ_e (Σ_k [e ∈ P_ik])·w_e`。 -/
theorem sum_dist_eq_sum_card (T : Phylogram X) (i : X) :
    (∑ k : X, T.dist (T.leaf i) (T.leaf k))
      = ∑ e : Sym2 T.V,
          (∑ k : X, (if e ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges then (1 : ℝ) else 0))
            * T.wExt e := by
  have h1 : ∀ k : X, T.dist (T.leaf i) (T.leaf k)
      = ∑ e : Sym2 T.V,
          (if e ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges then T.wExt e else (0 : ℝ)) :=
    fun k => dist_eq_sum_pathOf T (T.leaf i) (T.leaf k)
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : e ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges <;> simp [h]

/-- ★★★ **内层计数（步骤 ③）**：叶 `i` 在 `s(a,b)` 的 `a` 侧时 `Σ_k [e ∈ P_ik] = |L_b(e)|`。 -/
theorem sum_ite_pathOf_eq_sideLeafCount (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i : X} (hi : T.inSide s(a, b) a (T.leaf i)) :
    (∑ k : X, (if s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges then (1 : ℝ) else 0))
      = (T.sideLeafCount s(a, b) b : ℝ) := by
  have hcard := card_filter_pathOf_edges T hab hi
  have h := Finset.card_filter (fun k : X => s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges)
      (s := (Finset.univ : Finset X))
  rw [← hcard, h]
  push_cast
  rfl

end Cladogram


/-! ## 18. ★★★ 收口：`attesonQ T.wExt = (n−2)·δ(i,j) − S_i − S_j`（W12e12 · Atteson Lemma 10）

本节把 §14–§17 的全部器材**收口**成 Atteson Lemma 10（`:1774–1804`）的权重等式：

　　`Σ_e w_e(i,j)·w_e = (n−2)·δ(i,j) − S_i − S_j`，其中 `S_x = Σ_k δ(x,k)`。

四步（(a)(b)(c) + 收口）：
* (a) 三个 `δ` 换成沿边和：`δ(i,j)` 用 §15 `dist_eq_sum_pathOf`，`S_i`、`S_j` 用 §17 `sum_dist_eq_sum_card`；
* (b) `Finset.mul_sum` ＋ 两次 `rw [← Finset.sum_sub_distrib]` 把右边收成**单个** `Σ_e`；
* (c) `Finset.sum_congr` 逐项 ＋ `Sym2.ind` 取出边 `s(a,b)`：
　　**真边**（`T.graph.Adj a b`）按「`i` 在哪侧」定向后（必要时 `Sym2.eq_swap` 换向），
　　再用 §17 的 `sum_ite_pathOf_eq_sideLeafCount`（`'` 为 `b` 侧定向版）把内层和换成 `sideLeafCount`，
　　并代入 §16 的两条逐边比较；
　　**非边**两边都带因子 `wExt = 0`（`Phylo.TreeDist.wExt_eq_zero`）⇒ `simp` 自动相等。

于是 §14 的 `attesonQ` 就是 NJ 判据 `Q` 的「沿边加权和」写法 ✓。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **内层计数（`b` 侧定向版）**：叶 `i` 在 `s(a,b)` 的 `b` 侧时 `Σ_k [e ∈ P_ik] = |L_a(e)|`。 -/
theorem sum_ite_pathOf_eq_sideLeafCount' (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i : X} (hi : T.inSide s(a, b) b (T.leaf i)) :
    (∑ k : X, (if s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges then (1 : ℝ) else 0))
      = (T.sideLeafCount s(a, b) a : ℝ) := by
  have hi' : T.inSide s(b, a) b (T.leaf i) := by rwa [Sym2.eq_swap]
  have h := sum_ite_pathOf_eq_sideLeafCount T hab.symm (i := i) hi'
  rw [Sym2.eq_swap] at h
  exact h

/-- ★★★ **逐边收口（定向版）**：`i` 在 `a` 侧时，乘积项 `w_e·wExt e` 等于收口后 `e = s(a,b)` 的那一项
（真边的「同侧」用 §16 `attesonW_cast_eq_Q_same`、「异侧」用 `attesonW_cast_eq_Q_opposite`）。 -/
theorem attesonW_mul_wExt_edge (T : Phylogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j : X} (hi : T.inSide s(a, b) a (T.leaf i)) :
    T.attesonW (T.leaf i) (T.leaf j) s(a, b) * T.wExt s(a, b)
      = ((Fintype.card X : ℝ) - 2)
          * (if s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then T.wExt s(a, b) else 0)
        - (∑ k : X, (if s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf k)).edges then (1 : ℝ) else 0))
          * T.wExt s(a, b)
        - (∑ k : X, (if s(a, b) ∈ (T.pathOf (T.leaf j) (T.leaf k)).edges then (1 : ℝ) else 0))
          * T.wExt s(a, b) := by
  have hI := sum_ite_pathOf_eq_sideLeafCount T.toCladogram hab hi
  rcases T.inSide_or_inSide (x := T.leaf j) hab with hj | hj
  · -- `j` 也在 `a` 侧（同侧）
    have hj' : T.inSide s(a, b) a (T.leaf j) := (T.inSide_comm (s(a, b)) (T.leaf j) a).mp hj
    have hJ := sum_ite_pathOf_eq_sideLeafCount T.toCladogram hab hj'
    have hnotmem : s(a, b) ∉ (T.pathOf (T.leaf i) (T.leaf j)).edges := by
      intro hmem
      exact ((T.mem_pathOf_edges_iff_not_inSide (s(a, b)) (T.leaf i) (T.leaf j)).mp hmem)
        (hi.symm.trans hj')
    rw [ite_eq_right hnotmem, hI, hJ, T.attesonW_cast_eq_Q_same hab hi hj']
    ring
  · -- `j` 在 `b` 侧（异侧）
    have hj' : T.inSide s(a, b) b (T.leaf j) := (T.inSide_comm (s(a, b)) (T.leaf j) b).mp hj
    have hJ := sum_ite_pathOf_eq_sideLeafCount' T.toCladogram hab hj'
    have hmem : s(a, b) ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges := by
      refine (T.mem_pathOf_edges_iff_not_inSide (s(a, b)) (T.leaf i) (T.leaf j)).mpr ?_
      intro hcon
      have hia : T.inSide s(a, b) (T.leaf i) a := (T.inSide_comm (s(a, b)) a (T.leaf i)).mp hi
      exact T.not_reachable_deleteEdges_of_adj hab (hia.symm.trans (hcon.trans hj'.symm))
    rw [ite_eq_left hmem, hI, hJ, T.attesonW_cast_eq_Q_opposite hab hi hj']
    ring

/-- ★★★ **Atteson Lemma 10 的权重等式（收口）**：
`Σ_e w_e(i,j)·w_e = (n−2)·δ(i,j) − S_i − S_j`（`S_x = Σ_k δ(x,k)`）
—— `attesonQ`（§14）就是 NJ 判据 `Q` 的「沿边加权和」写法。 -/
theorem attesonQ_wExt_eq (T : Phylogram X) (i j : X) :
    T.toCladogram.attesonQ T.wExt (T.leaf i) (T.leaf j)
      = ((Fintype.card X : ℝ) - 2) * T.dist (T.leaf i) (T.leaf j)
        - (∑ k : X, T.dist (T.leaf i) (T.leaf k))
        - (∑ k : X, T.dist (T.leaf j) (T.leaf k)) := by
  rw [attesonQ, dist_eq_sum_pathOf T (T.leaf i) (T.leaf j), sum_dist_eq_sum_card T i,
    sum_dist_eq_sum_card T j, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Sym2.ind (fun a b => ?_) e
  by_cases hab : T.graph.Adj a b
  · rcases T.inSide_or_inSide (x := T.leaf i) hab with hi | hi
    · exact attesonW_mul_wExt_edge T hab ((T.inSide_comm (s(a, b)) a (T.leaf i)).mpr hi)
    · have hi' : T.inSide s(b, a) b (T.leaf i) := by
        rw [Sym2.eq_swap]
        exact hi.symm
      have h := attesonW_mul_wExt_edge (T := T) (a := b) (b := a) (i := i) (j := j) hab.symm hi'
      rw [Sym2.eq_swap] at h
      exact h
  · have hnot : s(a, b) ∉ T.graph.edgeSet :=
      fun h => hab ((SimpleGraph.mem_edgeSet T.graph).mp h)
    rw [Phylo.TreeDist.wExt_eq_zero T hnot]
    simp

end Cladogram


/-! ## 19. ★★★ W49-A-(ii)a：**任意** `(k,l)` 的逐边系数差（四种情形）

Lemma 11 的证明（Atteson `:2008–2070`）的全部内容都在比较**逐边系数**

　　　`c_e := w_e(k,l) − w_e(i,j)`

的符号与总和。关键事实：`w_e` 的两条分支引理（§13 的
`attesonW_eq_neg_two_of_not_inSide` / `attesonW_eq_sideCount_of_inSide`）对**任意顶点对**
`(x,y)` 都成立 ⇒ `c_e` **只由**「`e` 是否分离这两对」决定，四种组合各有一个闭式：

| `e` 分离 `k,l`？ | `e` 分离 `i,j`？ | `c_e` |
|---|---|---|
| 否 | 否 | `0` |
| 否 | 是 | `2·(n − S_i) − 2` |
| 是 | 否 | `2 − 2·(n − S_k)` |
| 是 | 是 | `2·(S_k − S_i)` |

其中 `S_x := sideLeafCount s(a,b) x` 是 `x` 一侧的叶数（`sideLeafCount_eq_of_inSide` 说明它只依赖侧）。

★ **这正是 `(ii)b`（路径单调性）要的接口**：`c_e` 里只剩「侧叶数」这一个几何量，
于是「沿 `k → l` 走、侧叶数递增」的论证可以完全在**侧叶数**上做。

★★ **诚实边界（W49）**：下面四条闭式与「`e` 分离 `k,l` ⇒ `c_e ≥ 0`」**已落**；
把 Atteson 的 `e*` 选法（`e* ∈ E − P_{k,l}` 使 `ℓ_k(e*)` 最小 ⇒ 在 `T − e*` 的 `k,l` 侧
取樱桃 `(i,j)`）接上、并做出 `Σ c_e ≥ 3(n−4)` / `2(n−3)` 的系数和（`(ii)b`/`(ii)c`）**未落**，
路线与卡点见 `W49_A_PLAN.md`。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **（ii)a｜① 两对都**不**被 `e` 分离** ⇒ `c_e = 0`（两边都取 `−2`）。 -/
theorem attesonW_sub_of_not_inSide_not_inSide (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : ¬ T.inSide e k l) (hij : ¬ T.inSide e i j) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ) = 0 := by
  rw [T.attesonW_eq_neg_two_of_not_inSide hkl, T.attesonW_eq_neg_two_of_not_inSide hij]
  norm_num

/-- ★★★ **（ii)a｜② `e` 分离 `k,l` 但不分离 `i,j`** ⇒ `c_e = 2·(n − S_i) − 2`
（`(k,l)` 计 `−2`，`(i,j)` 计 `−2(n − S_i)`）。 -/
theorem attesonW_sub_of_not_inSide_inSide (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : ¬ T.inSide e k l) (hij : T.inSide e i j) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ)
      = 2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e i : ℝ)) - 2 := by
  rw [T.attesonW_eq_neg_two_of_not_inSide hkl, T.attesonW_eq_sideCount_of_inSide hij]
  push_cast
  ring

/-- ★★★ **（ii)a｜③ `e` 不分离 `k,l` 但分离 `i,j`** ⇒ `c_e = 2 − 2·(n − S_k)`。 -/
theorem attesonW_sub_of_inSide_not_inSide (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : T.inSide e k l) (hij : ¬ T.inSide e i j) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ)
      = 2 - 2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e k : ℝ)) := by
  rw [T.attesonW_eq_sideCount_of_inSide hkl, T.attesonW_eq_neg_two_of_not_inSide hij]
  push_cast
  ring

/-- ★★★ **（ii)a｜④ 两对都**被** `e` 分离** ⇒ `c_e = 2·(S_k − S_i)`。 -/
theorem attesonW_sub_of_inSide_inSide (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : T.inSide e k l) (hij : T.inSide e i j) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ)
      = 2 * ((T.sideLeafCount e k : ℝ) - (T.sideLeafCount e i : ℝ)) := by
  rw [T.attesonW_eq_sideCount_of_inSide hkl, T.attesonW_eq_sideCount_of_inSide hij]
  push_cast
  ring

/-- ★★★ **（ii)a-正｜`e` 分离 `k,l` ⇒ `c_e ≥ 0`**（**与 `(i,j)` 在哪侧无关**）：

* `i,j` 也被 `e` 分离 ⇒ 情形 ①，`c_e = 0`；
* 否则情形 ②，`c_e = 2·(n − S_i) − 2 ≥ 0`（边的两侧都含叶 ⇒ `S_i < n`）。

这是 Atteson case 1（`:2008–2020`）的逐边结论，也是 `(ii)b` 里**唯一无条件**成立的那一半
（另外两半要靠 `e*` 的最小性）。 -/
theorem attesonW_sub_nonneg_of_not_inSide (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j k l : T.V} (hkl : ¬ T.inSide s(a, b) k l) :
    0 ≤ (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ) := by
  by_cases hij : T.inSide s(a, b) i j
  · rw [T.attesonW_sub_of_not_inSide_inSide hkl hij]
    have hlt : T.sideLeafCount s(a, b) i < Fintype.card X :=
      T.sideLeafCount_lt_card_of_adj hab
    have hle : (T.sideLeafCount s(a, b) i : ℝ) + 1 ≤ (Fintype.card X : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  · rw [T.attesonW_sub_of_not_inSide_not_inSide hkl hij]

end Cladogram


/-! ## 20. ★★★ W50-A-#5 ／ #3：三情形收口（「其余边」`c_e = 0` ＋ 两条分离支的非负）

§19 给的是**闭式**；本节把 Atteson 情形表里剩下的三格落成**可直接用于求和**的结论：

| `e` 的位置 | 结论 | 本节定理 |
|---|---|---|
| 不分离 `k,l`、也不分离 `i,k`／`j,l`（情形 ④） | `c_e = 0` | `attesonW_sub_eq_zero_of_far` |
| 分离 `i,k`（且 `i,j` 同侧）＝ Atteson case 2 | `c_e = 2(2S_k − n) ≥ 0`（要 `n ≤ 2S_k`） | `attesonW_sub_nonneg_of_sep_ik` |
| 对称的一支（`l = j` 时才出现） | 同上有理 | `attesonW_sub_nonneg_of_sep_ik` 的 `b` 侧版 |

★ **`hbig : n ≤ 2·S_k` 是本节的唯一「外部输入」** —— 它**不是**假设出来的几何事实，而是
`e*` 最小性的**输出**：`e*` 取「不在 `P_{k,l}` 上、且 `k` 侧叶数最小」的边 ⇒
对任意 `e ∉ P_{k,l}` 有 `ℓ_k(e*) ≤ ℓ_k(e)`，再配上「`e*` 在 `T − e` 的 `k` 侧」这条严格包含
即得 `ℓ_k(e) + ℓ_k(e*) < n`，于是 `2ℓ_k(e) ≥ n`。**这一段（`#1` 最小性 → `hbig`）W50 未落**，
故本节三条引理都带 `hbig` 作为参数 —— 见 `W50_A_MATH.md` §3 的施工清单。
-/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **（A）-情形④｜三对都不被 `e` 分离 ⇒ `c_e = 0`**（Atteson case 4，`:2063`）。

即 `e` 不分离 `k,l`、不分离 `i,k`、不分离 `j,l` ⇒ 四片叶同在 `e` 的一侧 ⇒
`c_e = 2(S_k − S_i) = 0`（`sideLeafCount_eq_of_inSide` 把两个侧叶数对齐）。 -/
theorem attesonW_sub_eq_zero_of_far (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : T.inSide e k l) (hik : T.inSide e i k) (hjl : T.inSide e j l) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ) = 0 := by
  -- `i ~ k ~ l ~ j` ⇒ `i ~ j`（同侧关系是等价关系）
  have hij : T.inSide e i j := (hik.trans hkl).trans ((T.inSide_comm e l j).mpr hjl)
  rw [T.attesonW_sub_of_inSide_inSide hkl hij]
  have hS : T.sideLeafCount e i = T.sideLeafCount e k := T.sideLeafCount_eq_of_inSide hik
  rw [hS, sub_self]
  ring

/-- ★★★ **（A）-情形②（`a` 侧定向）｜`i` 与 `k` 分居 `e` 两侧、`i,j` 同侧** ⇒

　　`c_e = 2(2·S_k − n) ≥ 0`（当 `n ≤ 2·S_k`）。

这是 Atteson case 2（`:2042–2057`）的**逐边代数部分**：`w_e(k,l) = −2(n − S_k)`、
`w_e(i,j) = −2S_k`（因 `S_i = n − S_k`），故差为 `2(2S_k − n)`。 -/
theorem attesonW_sub_of_sep_ik_eq (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j k l : T.V} (hkl : T.inSide s(a, b) k l) (hij : T.inSide s(a, b) i j)
    (hik : ¬ T.inSide s(a, b) i k) :
    (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ)
      = 2 * (2 * (T.sideLeafCount s(a, b) k : ℝ) - (Fintype.card X : ℝ)) := by
  -- 先定 `k` 在哪侧、`i` 必在另一侧，于是 `S_i + S_k = n`
  have hsum : (T.sideLeafCount s(a, b) i : ℝ) + (T.sideLeafCount s(a, b) k : ℝ)
      = (Fintype.card X : ℝ) := by
    rcases T.inSide_or_inSide (x := k) hab with hk | hk
    · -- `k` 在 `a` 侧 ⇒ `i` 在 `b` 侧
      have hi : T.inSide s(a, b) i b := by
        rcases T.inSide_or_inSide (x := i) hab with hi' | hi'
        · exact absurd (hi'.trans ((T.inSide_comm s(a, b) k a).mp hk)) hik
        · exact hi'
      rw [T.sideLeafCount_eq_of_inSide hi, T.sideLeafCount_eq_of_inSide hk,
        ← Nat.cast_add, Nat.add_comm, T.sideLeafCount_add_of_adj hab]
    · -- `k` 在 `b` 侧 ⇒ `i` 在 `a` 侧
      have hi : T.inSide s(a, b) i a := by
        rcases T.inSide_or_inSide (x := i) hab with hi' | hi'
        · exact hi'
        · exact absurd (hi'.trans ((T.inSide_comm s(a, b) k b).mp hk)) hik
      rw [T.sideLeafCount_eq_of_inSide hi, T.sideLeafCount_eq_of_inSide hk,
        ← Nat.cast_add, T.sideLeafCount_add_of_adj hab]
  rw [T.attesonW_sub_of_inSide_inSide hkl hij]
  linarith

/-- ★★★ **（A）-情形②的非负版**：把上一条与 `hbig : n ≤ 2·S_k` 拼起来。 -/
theorem attesonW_sub_nonneg_of_sep_ik (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j k l : T.V} (hkl : T.inSide s(a, b) k l) (hij : T.inSide s(a, b) i j)
    (hik : ¬ T.inSide s(a, b) i k)
    (hbig : (Fintype.card X : ℝ) ≤ 2 * (T.sideLeafCount s(a, b) k : ℝ)) :
    0 ≤ (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ) := by
  rw [T.attesonW_sub_of_sep_ik_eq hab hkl hij hik]
  linarith

/-! ### 20′｜`(ii)b` 的第一块：**离路径边存在** ＋ **`ℓ_k` 的最小者**

Atteson 的选法是「`e* ∈ E − P_{k,l}` 使 `ℓ_k(e*)`（`k` 一侧的叶数）**最小**」。本节落两件：

* ★★ `exists_offPath_edge`：只要 `3 ≤ card X`，就有离路径边 —— 取**第三片叶** `x ∉ {k,l}`，
  它的唯一关联边 `s(leaf x, u)` 不可能在 `k → l` 的路径上（路径是简单的，而叶的度是 1，
  不可能成为路径的**内部**点）；用 `sideLeaves` 说更省事：`x` 一侧恰是 `{x}`，故 `k,l` 都在 `u` 一侧。
* ★★★ `exists_min_sideLeafCount_offPath`：`Finset.exists_min_image` 把「最小」取成一条边的见证。

★ **诚实边界 ＋ ★D（W50 机械核）**：Atteson 还要给自己的 `e*` 配两条界 ——

* **下界 `3 ≤ ℓ_k(e*)`：成立**，且在最终证明里**免费**（由樱桃的位置给出）：
  `(i,j) ⊆ C`、`k,l ∈ C`，`DisjointPairs` 支 `C` 有 4 片互异叶（`ℓ_k(e*) ≥ 4`）、
  `SharesOneLabel` 支有 3 片（`ℓ_k(e*) ≥ 3`）—— 这正是 `3(n−4)` / `2(n−3)` 两个常数的来源。
* **上界 `ℓ_k(e*) ≤ n − 2`：不成立**。`n = 5` 时 `ℓ_k(e*) = n − 1 = 4` 完全可能（`e*` 的远侧只挂
  1 片叶）；机械核 `scripts/msc/w50_lemma11_case2_check.py`（2 737 个非樱桃对）给出 **412 个反例**。
  正确的界是平凡的 `ℓ_k(e*) ≤ n − 1`，而**证明根本不需要**它 —— 需要的是**逐边**不变量
  `hbig : n ≤ 2·ℓ_k(e)`（`e ∈ P_{i,k} − P_{k,l}`），同一脚本 562 条情形②边**0 反例**。

★ 这两条（下界、`hbig`）W50 均**未形式化**；施工细节与 OCR 的坑见项目根 `W50_A_MATH.md` §3.1。 -/

/-- ★★ **离路径边存在**（Atteson `:2016–2022` 的 `e*` 候选）：取第三片叶 `x ∉ {k,l}`，
它的唯一关联边 `s(leaf x, u)` 就是一条**不在** `k → l` 路径上的边。 -/
theorem exists_offPath_edge (T : Cladogram X) {k l : X} (hkl : k ≠ l)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ e : Sym2 T.V, e ∈ T.graph.edgeSet ∧ T.inSide e (T.leaf k) (T.leaf l) := by
  -- 取第三片叶
  have hx : ∃ x : X, x ≠ k ∧ x ≠ l := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset X) ⊆ ({k, l} : Finset X) := by
      intro y _
      by_cases hy : y = k
      · exact Finset.mem_insert.mpr (Or.inl hy)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hcon y hy)))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Finset.card_pair hkl] at hcard
    omega
  obtain ⟨x, hxk, hxl⟩ := hx
  -- `x` 的唯一邻居 `u`
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨u, hu, -⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine ⟨s(T.leaf x, u), (SimpleGraph.mem_edgeSet T.graph).mpr hu, ?_⟩
  -- `x` 一侧恰是 `{x}` ⇒ `k,l` 都在 `u` 一侧
  have hside : T.sideLeaves s(T.leaf x, u) u = (T.sideLeaves s(T.leaf x, u) (T.leaf x))ᶜ :=
    T.sideLeaves_compl_adj hu
  have hxs : T.sideLeaves s(T.leaf x, u) (T.leaf x) = {x} := T.sideLeaves_leaf_edge hu
  have hk_mem : k ∈ T.sideLeaves s(T.leaf x, u) u := by
    rw [hside, hxs, Finset.mem_compl, Finset.mem_singleton]
    exact fun h => hxk h.symm
  have hl_mem : l ∈ T.sideLeaves s(T.leaf x, u) u := by
    rw [hside, hxs, Finset.mem_compl, Finset.mem_singleton]
    exact fun h => hxl h.symm
  have hin_k : T.inSide s(T.leaf x, u) u (T.leaf k) := (T.mem_sideLeaves_iff_inSide).mp hk_mem
  have hin_l : T.inSide s(T.leaf x, u) u (T.leaf l) := (T.mem_sideLeaves_iff_inSide).mp hl_mem
  exact ((T.inSide_comm s(T.leaf x, u) (T.leaf k) u).mpr hin_k).trans hin_l

/-- ★★★ **（A）`#1`｜离路径边中 `ℓ_k` 最小者存在**（Atteson 的 `e*`）。

`ℓ_k(e) := sideLeafCount e (leaf k)` 是 `e` 的 `k` 一侧叶数；最小性对**每条**离路径边成立
（这正是后面 `hbig : n ≤ 2·S_k` 的唯一输入）。 -/
theorem exists_min_sideLeafCount_offPath (T : Cladogram X) {k l : X} (hkl : k ≠ l)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ eStar : Sym2 T.V, eStar ∈ T.graph.edgeSet ∧ T.inSide eStar (T.leaf k) (T.leaf l) ∧
      ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
        T.sideLeafCount eStar (T.leaf k) ≤ T.sideLeafCount e (T.leaf k) := by
  classical
  obtain ⟨e₀, he₀, hin₀⟩ := T.exists_offPath_edge hkl h3
  have hne : ((Finset.univ : Finset (Sym2 T.V)).filter
      (fun e => e ∈ T.graph.edgeSet ∧ T.inSide e (T.leaf k) (T.leaf l))).Nonempty :=
    ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀, hin₀⟩⟩
  obtain ⟨eStar, heStar, hmin⟩ :=
    Finset.exists_min_image _ (fun e => T.sideLeafCount e (T.leaf k)) hne
  obtain ⟨-, heStarE, heStarI⟩ := Finset.mem_filter.mp heStar
  exact ⟨eStar, heStarE, heStarI, fun e heE heI => hmin e (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, heE, heI⟩)⟩

end Cladogram


/-! ## 21. ★★★ W50-A-#2：`hbig` 的几何来源（`e*` 最小性 ⇒ `n ≤ 2·ℓ_k(e)`）

§20 的三条引理把 `hbig : n ≤ 2·S_k` 当作**外部输入**。本节把它**证出来** —— 它是
`e*`（离路径边中 `ℓ_k` 最小者，§20′ 的 `exists_min_sideLeafCount_offPath`）的**输出**，
不是几何假设。

**数学**。设 `e = s(a,b)` 分离 `i` 与 `k`（`hik`），`e* = s(c,d)` 是「不在 `P_{k,l}` 上、
且 `k` 一侧叶数最小」的边，`C := T − e*` 中含 `k` 的那一侧（`i ∈ C`，即 `hCin`）。则

* **情形 ①（`e*` 的端点都不在 `e` 的 `i` 一侧）**：`T − e` 的 `i` 侧整块落在 `C` 里
  （`Cladogram.inSide_deleteEdges_of_inSide`，`Phylo/Split.lean:685`）⇒ `L_i(e) ⊆ L_k(e*)`
  ⇒ `ℓ_i(e) ≤ ℓ_k(e*) ≤ ℓ_k(e)`，末步是 `e*` 的最小性（`e ∈ E − P_{k,l}`）；
* **情形 ②（`e*` 的端点都在 `e` 的 `i` 一侧）**：对称地 `L_k(e) ⊆ L_k(e*)`，与最小性合成
  **计数相等**，即 `L_k(e) = L_k(e*)`；但 `i ∈ L_k(e*)`（`hCin`，注意 `i ∉ L_k(e)`）—— 矛盾。
  故情形 ② **不出现**。

再由 `ℓ_i(e) + ℓ_k(e) = n`（`sideLeafCount_add_of_adj` ＋ 同侧不变性）得 `n ≤ 2·ℓ_k(e)`。

★ 这里**没有**用到 `ℓ_k(e*) ≤ n − 2`（该上界是错的：`W50_A_MATH.md` §3.1 给出 412 个反例，
`n = 5` 时 `ℓ_k(e*) = n−1` 即可发生）。走的是「`L_i(e) ⊆ L_k(e*)` ＋ 最小性」这条
**正确且更强**的路子 —— 它只用 `e*` 的**最小性**，不碰任何 `e*` 的数值上界。

★ 注意 `hCin`（`i` 与 `k` 在 `e*` 同侧）**不是**额外假设：它正是「樱桃 `(i,j)` 取在 `C` 里」
的定义式内容（`C` = `e*` 的 `k` 一侧），由 `cherry_in_component` 的选法供给。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **（A）`#2` 主引理**：`e* = s(c,d)` 是离路径边中 `ℓ_k` 最小者、且 `i` 与 `k` 在
`e*` 同侧（即 `i` 落在 `C` 里），则对**任意**分离 `i,k` 的真边 `e = s(a,b)` 有
`ℓ_i(e) ≤ ℓ_k(e)`。

这是 Atteson `:2042–2057` 那段的正确形态（OCR 里 `L − L_k(e*) ⊋ L_k(e)` 与
`k ∉ L − L_k(e*)` 自相矛盾，已按「两侧叶集的包含关系 ＋ 最小性」重写）。 -/
theorem sideLeafCount_leaf_le_of_eStar_min (T : Cladogram X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {i k l : X}
    (hkl : T.inSide s(a, b) (T.leaf k) (T.leaf l))
    (hik : ¬ T.inSide s(a, b) (T.leaf i) (T.leaf k))
    (hCin : T.inSide s(c, d) (T.leaf i) (T.leaf k))
    (hmin : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
      T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount e (T.leaf k)) :
    T.sideLeafCount s(a, b) (T.leaf i) ≤ T.sideLeafCount s(a, b) (T.leaf k) := by
  classical
  have heE : s(a, b) ∈ T.graph.edgeSet := (SimpleGraph.mem_edgeSet T.graph).mpr hab
  -- `e* ≠ e`：否则 `i,k` 在 `e*` 同侧与 `hik` 冲突
  have hne : s(c, d) ≠ s(a, b) := fun h => hik (h ▸ hCin)
  -- `c,d` 必在 `e` 的同侧（`e* ≠ e` 且相邻）
  have hcongr := T.inSide_congr_of_adj (u₁ := T.leaf i) hcd hne
  by_cases hci : T.inSide s(a, b) (T.leaf i) c
  · -- 情形 ②：`e*` 两端都在 `e` 的 `i` 一侧 ⇒ 与最小性 + `hCin` 矛盾
    exfalso
    have hdi : T.inSide s(a, b) (T.leaf i) d := hcongr.mp hci
    have hck : ¬ T.inSide s(a, b) (T.leaf k) c := fun h => hik (hci.trans h.symm)
    have hdk : ¬ T.inSide s(a, b) (T.leaf k) d := fun h => hik (hdi.trans h.symm)
    -- `L_k(e) ⊆ L_k(e*)`
    have hsub : T.sideLeaves s(a, b) (T.leaf k) ⊆ T.sideLeaves s(c, d) (T.leaf k) := by
      intro x hx
      rw [T.mem_sideLeaves_iff_inSide] at hx ⊢
      exact T.inSide_deleteEdges_of_inSide rfl hx hck hdk
    -- 与最小性合成计数相等 ⇒ 叶集相等 ⇒ `i ∈ L_k(e)`，与 `hik` 冲突
    have hminE : T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount s(a, b) (T.leaf k) :=
      hmin s(a, b) heE hkl
    rw [sideLeafCount, sideLeafCount] at hminE
    have heq := Finset.eq_of_subset_of_card_le hsub hminE
    have hiMem : i ∈ T.sideLeaves s(c, d) (T.leaf k) := by
      rw [T.mem_sideLeaves_iff_inSide]
      exact (T.inSide_comm s(c, d) (T.leaf i) (T.leaf k)).mp hCin
    rw [← heq] at hiMem
    rw [T.mem_sideLeaves_iff_inSide] at hiMem
    exact hik ((T.inSide_comm s(a, b) (T.leaf k) (T.leaf i)).mp hiMem)
  · -- 情形 ①：`e*` 两端都不在 `e` 的 `i` 一侧 ⇒ `L_i(e) ⊆ L_k(e*)` ＋ 最小性
    have hdi : ¬ T.inSide s(a, b) (T.leaf i) d := fun h => hci (hcongr.mpr h)
    have hcard : T.sideLeafCount s(a, b) (T.leaf i) ≤ T.sideLeafCount s(c, d) (T.leaf k) := by
      rw [sideLeafCount, sideLeafCount]
      refine Finset.card_le_card ?_
      intro x hx
      rw [T.mem_sideLeaves_iff_inSide] at hx ⊢
      have h1 : T.inSide s(c, d) (T.leaf i) (T.leaf x) :=
        T.inSide_deleteEdges_of_inSide rfl hx hci hdi
      exact (T.inSide_comm s(c, d) (T.leaf k) (T.leaf x)).mpr (h1.symm.trans hCin)
    exact le_trans hcard (hmin s(a, b) heE hkl)

/-- ★★★ **（A）`#2` 收口：`hbig`**（`n ≤ 2·ℓ_k(e)`，`e` 分离 `i,k` 且两者与 `k,l` 分居）。

由主引理 `ℓ_i(e) ≤ ℓ_k(e)` 与两侧叶数之和 `ℓ_i(e) + ℓ_k(e) = n` 直接得。 -/
theorem card_le_two_mul_sideLeafCount_of_sep_ik (T : Cladogram X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {i k l : X}
    (hkl : T.inSide s(a, b) (T.leaf k) (T.leaf l))
    (hik : ¬ T.inSide s(a, b) (T.leaf i) (T.leaf k))
    (hCin : T.inSide s(c, d) (T.leaf i) (T.leaf k))
    (hmin : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
      T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount e (T.leaf k)) :
    Fintype.card X ≤ 2 * T.sideLeafCount s(a, b) (T.leaf k) := by
  classical
  have h1 := T.sideLeafCount_leaf_le_of_eStar_min hab hcd hkl hik hCin hmin
  -- 分离 `i,k` ⇒ 两侧叶数之和为 `n`
  have h2 : T.sideLeafCount s(a, b) (T.leaf i) + T.sideLeafCount s(a, b) (T.leaf k)
      = Fintype.card X := by
    rcases T.inSide_or_inSide (x := T.leaf k) hab with hk | hk
    · have hi : T.inSide s(a, b) (T.leaf i) b := by
        rcases T.inSide_or_inSide (x := T.leaf i) hab with h | h
        · exact absurd (h.trans ((T.inSide_comm s(a, b) (T.leaf k) a).mp hk)) hik
        · exact h
      rw [T.sideLeafCount_eq_of_inSide hi, T.sideLeafCount_eq_of_inSide hk,
        Nat.add_comm, T.sideLeafCount_add_of_adj hab]
    · have hi : T.inSide s(a, b) (T.leaf i) a := by
        rcases T.inSide_or_inSide (x := T.leaf i) hab with h | h
        · exact h
        · exact absurd (h.trans ((T.inSide_comm s(a, b) (T.leaf k) b).mp hk)) hik
      rw [T.sideLeafCount_eq_of_inSide hi, T.sideLeafCount_eq_of_inSide hk,
        T.sideLeafCount_add_of_adj hab]
  omega

/-- ★★★ **（A）`#2` 的非负版（无额外假设）**：§20 的 `attesonW_sub_nonneg_of_sep_ik` 里
那个 `hbig` 参数，这里由 `e*` 的最小性**供给**。

⇒ Atteson case 2 的逐边非负性 `w_e(k,l) − w_e(i,j) = 2(2S_k − n) ≥ 0` 现在**只**依赖
「`e*` 离路径且 `ℓ_k` 最小」＋「`(i,j)` 取在 `C` 里」，不再有任何数值假设。 -/
theorem attesonW_sub_nonneg_of_sep_ik_of_eStar (T : Cladogram X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {i j k l : X}
    (hkl : T.inSide s(a, b) (T.leaf k) (T.leaf l))
    (hij : T.inSide s(a, b) (T.leaf i) (T.leaf j))
    (hik : ¬ T.inSide s(a, b) (T.leaf i) (T.leaf k))
    (hCin : T.inSide s(c, d) (T.leaf i) (T.leaf k))
    (hmin : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
      T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount e (T.leaf k)) :
    0 ≤ (T.attesonW (T.leaf k) (T.leaf l) s(a, b) : ℝ)
      - (T.attesonW (T.leaf i) (T.leaf j) s(a, b) : ℝ) := by
  refine T.attesonW_sub_nonneg_of_sep_ik hab hkl hij hik ?_
  have h := T.card_le_two_mul_sideLeafCount_of_sep_ik hab hcd hkl hik hCin hmin
  exact_mod_cast h

/-! ### 21′｜`w_e` 的对称性 ＋ **四情形逐边非负的无条件版**

`attesonW i j e` 的「否则」分支里出现的是 `S_i`（**第一**个顶点那侧），所以
`w_e(i,j) = w_e(j,i)` **不是**定义式 —— 但 `e ∉ P_{i,j}` 时 `i,j` 同侧，
`S_i = S_j`（`sideLeafCount_eq_of_inSide`），故仍对称。这条对称性使「情形 3（`e ∈ P_{j,l}`）」
成为情形 2 的**镜像**（不必重写一遍证明）。 -/

/-- 唯一路径**反向**（`pathOf` 的无序性；`Phylo.PauplinFormula` 有同名结论但不在本文件 import 锥内）。 -/
theorem pathOf_eq_reverse (T : Cladogram X) (a b : T.V) :
    T.pathOf a b = (T.pathOf b a).reverse :=
  ((T.existsUnique_path a b).choose_spec.2 _ (T.pathOf_isPath b a).reverse).symm

/-- `e` 在 `P_{a,b}` 上 ⟺ 在 `P_{b,a}` 上。 -/
theorem mem_pathOf_edges_comm (T : Cladogram X) (e : Sym2 T.V) (a b : T.V) :
    e ∈ (T.pathOf a b).edges ↔ e ∈ (T.pathOf b a).edges := by
  rw [T.pathOf_eq_reverse, SimpleGraph.Walk.edges_reverse, List.mem_reverse]

/-- ★★ **`w_e` 关于顶点对对称**：`w_e(i,j) = w_e(j,i)`。 -/
theorem attesonW_comm (T : Cladogram X) (i j : T.V) (e : Sym2 T.V) :
    T.attesonW i j e = T.attesonW j i e := by
  have hmem := T.mem_pathOf_edges_comm e i j
  by_cases h : e ∈ (T.pathOf i j).edges
  · rw [attesonW, ite_eq_left h, attesonW, ite_eq_left (hmem.mp h)]
  · -- `e ∉ P_{i,j} ⇒ i,j` 同侧 ⇒ `S_i = S_j`
    have hin : T.inSide e i j := by
      by_contra hc
      exact h ((T.mem_pathOf_edges_iff_not_inSide e i j).mpr hc)
    rw [attesonW, ite_eq_right h, attesonW, ite_eq_right (fun hc => h (hmem.mpr hc)),
      T.sideLeafCount_eq_of_inSide hin]

/-- ★★★ **（A）四情形**逐边非负，**无条件版**（`Atteson :2008–2070` 的 case 1–4 全集）：

对**任意**真边 `e = s(a,b)`，只要 `e* = s(c,d)` 是离路径边中 `ℓ_k` 最小者（`hmin`）且
樱桃 `(i,j)` 取在 `C` 里（`hCin`、`hCjn`），就有

　　　`c_e = w_e(k,l) − w_e(i,j) ≥ 0`。

分情形（穷尽且互斥）：`e ∈ P_{k,l}`（W49 ★★ `attesonW_sub_nonneg_of_not_inSide`）／
`e ∈ P_{i,j}`（§19 ③）／`e ∈ P_{i,k} − P_{k,l}`（§21 情形 ②）／
`e ∈ P_{j,l} − P_{k,l}`（§21 的**镜像**，靠 `attesonW_comm`）／其余（§20 `c_e = 0`）。
★ 本定理**没有**任何数值假设（`hbig` 已由 §21 供给）。
★ **W50-#11 修正**：原签名多带一条 `hkl : T.inSide s(a,b) (leaf k) (leaf l)`，它在证明里
**从未被用过**（第一个 `by_cases h1` 又重新判了一次），却把 `e ∈ P_{k,l}` 的真边**排除在外** ——
那样本定理就无法用于路径边，是**签名 bug**（不是数学错误）。已删除。 -/
theorem attesonW_sub_nonneg_of_all (T : Cladogram X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {i j k l : X}
    (hcher : T.IsCherry i j) (hklne : k ≠ l)
    (heStarI : T.inSide s(c, d) (T.leaf k) (T.leaf l))
    (hCin : T.inSide s(c, d) (T.leaf i) (T.leaf k))
    (hCjn : T.inSide s(c, d) (T.leaf j) (T.leaf l))
    (hmin : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
      T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount e (T.leaf k)) :
    0 ≤ (T.attesonW (T.leaf k) (T.leaf l) s(a, b) : ℝ)
      - (T.attesonW (T.leaf i) (T.leaf j) s(a, b) : ℝ) := by
  classical
  -- `e*` 离路径 ⇒ `k,l` 在 `e*` 同侧 ⇒ 用 `ℓ_l` 写的镜像最小性也一样（供情形 ③ 用）
  have hmin' : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf l) (T.leaf k) →
      T.sideLeafCount s(c, d) (T.leaf l) ≤ T.sideLeafCount e (T.leaf l) := by
    intro e he H
    have H' : T.inSide e (T.leaf k) (T.leaf l) :=
      (T.inSide_comm e (T.leaf l) (T.leaf k)).mp H
    have h := hmin e he H'
    rw [(T.sideLeafCount_eq_of_inSide heStarI).symm, (T.sideLeafCount_eq_of_inSide H').symm]
    exact h
  by_cases h1 : T.inSide s(a, b) (T.leaf k) (T.leaf l)
  · by_cases h2 : T.inSide s(a, b) (T.leaf i) (T.leaf j)
    · by_cases h3 : T.inSide s(a, b) (T.leaf i) (T.leaf k)
      · by_cases h4 : T.inSide s(a, b) (T.leaf j) (T.leaf l)
        · -- 情形 ④：四叶同在 `e` 一侧 ⇒ `c_e = 0`
          have hz := T.attesonW_sub_eq_zero_of_far (e := s(a, b)) h1 h3 h4
          rw [hz]
        · -- 情形 ③：`e ∈ P_{j,l} − P_{k,l}`（情形 ② 的镜像）
          have hm := T.attesonW_sub_nonneg_of_sep_ik_of_eStar (a := a) (b := b)
            (c := c) (d := d) (i := j) (j := i) (k := l) (l := k) hab hcd
            ((T.inSide_comm s(a, b) (T.leaf k) (T.leaf l)).mp h1)
            ((T.inSide_comm s(a, b) (T.leaf i) (T.leaf j)).mp h2) h4 hCjn hmin'
          rw [attesonW_comm T (T.leaf l) (T.leaf k) s(a, b),
            attesonW_comm T (T.leaf j) (T.leaf i) s(a, b)] at hm
          exact hm
      · -- 情形 ②：`e ∈ P_{i,k} − P_{k,l}`
        exact T.attesonW_sub_nonneg_of_sep_ik_of_eStar hab hcd h1 h2 h3 hCin hmin
    · -- `e ∈ P_{i,j}`：`(i,j)` 是樱桃 ⇒ `e` 必是其一条**悬挂边** ⇒ `c_e = 0`
      obtain ⟨v, hvi, hvj⟩ := hcher.2
      have hother : ∀ x : X, x ≠ i → T.inSide s(T.leaf i, v) v (T.leaf x) := by
        intro x hx
        rcases T.inSide_or_inSide hvi (x := T.leaf x) with hc | hc
        · exfalso
          have hxi : x = i := by
            have hmem : x ∈ T.sideLeaves s(T.leaf i, v) (T.leaf i) :=
              (T.mem_sideLeaves_iff_inSide).mpr hc.symm
            rw [T.sideLeaves_leaf_edge hvi] at hmem
            simpa using hmem
          exact hx hxi
        · exact hc.symm
      have hother' : ∀ x : X, x ≠ j → T.inSide s(T.leaf j, v) v (T.leaf x) := by
        intro x hx
        rcases T.inSide_or_inSide hvj (x := T.leaf x) with hc | hc
        · exfalso
          have hxj : x = j := by
            have hmem : x ∈ T.sideLeaves s(T.leaf j, v) (T.leaf j) :=
              (T.mem_sideLeaves_iff_inSide).mpr hc.symm
            rw [T.sideLeaves_leaf_edge hvj] at hmem
            simpa using hmem
          exact hx hxj
        · exact hc.symm
      have hwalk : s(a, b) ∈ (SimpleGraph.Walk.cons hvi
          (SimpleGraph.Walk.cons hvj.symm SimpleGraph.Walk.nil) :
            T.graph.Walk (T.leaf i) (T.leaf j)).edges :=
        T.forall_mem_edges_of_not_inSide h2 _
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hwalk
      rw [T.attesonW_sub_of_inSide_not_inSide (e := s(a, b)) h1 h2]
      have hcard : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨k⟩
      rcases hwalk with h | h
      · -- `e = s(leaf i, v)`：除 `leaf i` 外的叶都在 `v` 一侧
        have hki : k ≠ i := by
          intro hc
          have h1' : T.inSide s(T.leaf i, v) (T.leaf i) (T.leaf l) := h ▸ (hc ▸ h1)
          exact T.not_inSide_both hvi ⟨h1', hother l (fun hl => hklne (hc.trans hl.symm))⟩
        rw [h]
        have hSR : (T.sideLeafCount s(T.leaf i, v) (T.leaf k) : ℝ)
            = (Fintype.card X : ℝ) - 1 := by
          rw [(T.sideLeafCount_eq_of_inSide (hother k hki)).symm, T.sideLeafCount_compl hvi,
            T.sideLeafCount_leaf_edge hvi, Nat.cast_sub hcard]
          norm_num
        rw [hSR]
        ring_nf
        norm_num
      · -- `e = s(v, leaf j)`（对称支）
        rw [h, Sym2.eq_swap] at h1 ⊢
        have hkj : k ≠ j := by
          intro hc
          exact T.not_inSide_both hvj ⟨hc ▸ h1, hother' l (fun hl => hklne (hc.trans hl.symm))⟩
        have hSR : (T.sideLeafCount s(T.leaf j, v) (T.leaf k) : ℝ)
            = (Fintype.card X : ℝ) - 1 := by
          rw [(T.sideLeafCount_eq_of_inSide (hother' k hkj)).symm, T.sideLeafCount_compl hvj,
            T.sideLeafCount_leaf_edge hvj, Nat.cast_sub hcard]
          norm_num
        rw [hSR]
        ring_nf
        norm_num
  · -- `e ∈ P_{k,l}`：W49 的无条件非负
    exact T.attesonW_sub_nonneg_of_not_inSide hab h1

end Cladogram


/-! ## 22. ★★★ W50-A-#6：`cherry_in_component` —— `e*` 的 `k` 一侧必有樱桃

`W49_A_PLAN.md` §4 的第 6 项。派单验收标准 #4 对它的要求是「**不许**变成假设且**单独一个
commit**」—— 因为 §21 的三条引理都以 `hCin`（樱桃取在 `C` 里）为前提，而 `hCin` 正是本节的
**输出**。

**数学**。设 `e* = s(c,d)`，`U := T − e*` 中含 `k` 的那一侧（`k,l` 同在 `U` 里）。设 `ℓ`、`i`
分别是 `U` 中「`T`-叶」与「非叶」顶点的个数。则

* **`ℓ ≤ i`（若无樱桃）**：「叶 ↦ 其唯一邻居」是**单射**（两片叶共邻居就是樱桃），
  落点是 `U` 中的**非叶**点（`not_isLeaf_of_adj_of_isLeaf`），且仍在 `U` 内 —— 否则那条边
  跨越 `U`，只能是 `e*` 自己，于是该叶只能是端点 `c`，与「`c` 非叶」冲突
  （`c` 若是叶则 `U = {c}`，与 `k,l ∈ U` 互异矛盾）；
* **`i + 1 ≤ ℓ`（**无条件**）**：`U` 的诱导子图是树（`isTree_induce_sideVertices`）、
  握手引理 `Σ deg = 2·#边`、`#边 = |U| − 1`（`card_edgeFinset_induce_sideVertices`）、
  「非 `c` 的非叶点在 `T[U]` 里度 = `T` 中的度 ≥ 3」、「`c` 在 `T[U]` 里度 ≥ 2」
  ⇒ `ℓ + 3(i−1) + 2 ≤ 2(ℓ+i−1)` ⇒ `ℓ ≥ i + 1`。

两者矛盾 ⇒ `U` 必有樱桃，且樱桃的两片叶与中心都在 `U` 里。∎

★ 第二块与 `Phylo/InternalEdge.lean` 的 `two_le_card_degree_one_of_side` **共用全部器材**，
只是把结论从「`≥ 2` 片叶」收紧成「非叶数 + 1 ≤ 叶数」—— 后者才是与「无樱桃 ⇒ 叶数 ≤ 非叶数」
相撞的那一半（`W50_A_MATH.md` §6 的计数路线，直径路线已评估否决：需要 ℕ 值路径长度与
「路径过某点」的分解，成本高且依赖多）。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### 22.1 侧顶点集与侧叶集、孤立叶 -/

/-- 侧**顶点**集与侧**叶**集一致（两者展开后都是 `(T − e).Reachable (leaf x) u`）。 -/
theorem mem_sideVertices_leaf_iff (T : Cladogram X) (e : Sym2 T.V) (u : T.V) (x : X) :
    T.leaf x ∈ T.sideVertices e u ↔ x ∈ T.sideLeaves e u := by
  rw [T.mem_sideVertices, T.mem_sideLeaves]

open scoped Classical in
/-- ★ **侧叶数 = 侧顶点集中叶顶点的个数**（沿 `x ↦ T.leaf x` 的一一对应）。 -/
theorem card_sideLeaves_eq_card_filter_isLeaf (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    (T.sideLeaves e u).card = ((T.sideVertices e u).filter T.IsLeaf).card := by
  classical
  refine (Finset.card_bij (fun x (_ : x ∈ T.sideLeaves e u) => T.leaf x) ?_ ?_ ?_)
  · intro x hx
    rw [Finset.mem_filter]
    exact ⟨(T.mem_sideVertices_leaf_iff e u x).mpr hx, ⟨x, rfl⟩⟩
  · intro a _ b _ h
    exact T.leaf.injective h
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzU, ⟨x, hx⟩⟩ := hz
    exact ⟨x, (T.mem_sideVertices_leaf_iff e u x).mp (hx ▸ hzU), hx⟩

/-- ★★ **度为 1 的顶点的侧集是单点集**：叶 `u` 的唯一关联边 `s(u,v)` 删掉后 `u` 在
`T − s(u,v)` 中孤立，故 `u` 一侧只有 `u` 自己。 -/
theorem eq_of_degree_eq_one_of_inSide (T : Cladogram X) {u v w : T.V}
    (huv : T.graph.Adj u v) (h1 : T.graph.degree u = 1)
    (h : T.inSide s(u, v) u w) : w = u := by
  classical
  obtain ⟨w₀, -, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h1
  have hzero : (T.graph.deleteEdges {s(u, v)}).degree u = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro y hy
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hy
    obtain ⟨hyadj, hydel⟩ := hy
    have hyv : y = v := (huniq y hyadj).trans (huniq v huv).symm
    exact hydel (by rw [hyv]; simp)
  by_contra hne
  exact SimpleGraph.not_reachable_of_left_degree_zero (fun h => hne h.symm) hzero h

/-! ### 22.2 计数：`非叶数 + 1 ≤ 叶数` -/

open scoped Classical in
/-- ★★★ **侧顶点集中「非叶数 + 1 ≤ 叶数」**。

`U` 是被割边 `s(u,v)` 分出的一侧：`hcross` 编码「只有 `e` 跨越 `U`」、`hE` 编码
「`#E(T[U]) + 1 = |U|`」（`T[U]` 是树）、`hnd` 说明 `u` 不是叶。

与 `Phylo/InternalEdge.lean` 的 `two_le_card_degree_one_of_side` 是**同一个论证**，只把结论
收紧成 `叶数 ≥ 非叶数 + 1`（那里的 `2 ≤ 叶数` 只是它的弱推论：`u` 自己就是非叶点）。 -/
theorem internal_card_add_one_le_leaf_card (T : Cladogram X) (U : Finset T.V) {u v : T.V}
    (huv : T.graph.Adj u v) (hu : u ∈ U) (hv : v ∉ U)
    (hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v))
    (hE : (T.graph.induce (↑U : Set T.V)).edgeFinset.card + 1 = U.card)
    (hnd : T.graph.degree u ≠ 1) :
    (U.filter (fun x => ¬ T.IsLeaf x)).card + 1 ≤ (U.filter T.IsLeaf).card := by
  classical
  have hnl : ¬ T.IsLeaf u := fun h => hnd ((T.isLeaf_iff_degree_eq_one u).mp h)
  -- ### 1. 非 `u` 顶点的邻居全在 `U` 内
  have hnb : ∀ x ∈ U, x ≠ u → T.graph.neighborSet x ⊆ (↑U : Set T.V) := by
    intro x hx hxu y hy
    by_contra hyn
    have hpair : s(x, y) = s(u, v) := hcross x hx y hy hyn
    have hmem : x ∈ s(u, v) := hpair ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : x ∈ s(x, y))
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact hxu h
    · exact hv (h ▸ hx)
  -- ### 2. `x ≠ u` 时诱导子图的度 = `T` 中的度
  have hdeg : ∀ x (hx : x ∈ U), x ≠ u →
      (T.graph.induce (↑U : Set T.V)).degree ⟨x, hx⟩ = T.graph.degree x := by
    intro x hx hxu
    rw [T.degree_induce_eq_card_inter U x hx]
    have hsub : T.graph.neighborFinset x ⊆ U := fun y hy =>
      hnb x hx hxu ((SimpleGraph.mem_neighborFinset T.graph x y).mp hy)
    rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
  -- ### 3. `u` 在诱导子图中的度 ≥ 2
  have hNsub : T.graph.neighborFinset u ⊆ insert v U := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    by_cases hyU : y ∈ U
    · exact Finset.mem_insert.mpr (Or.inr hyU)
    · have hpair : s(u, y) = s(u, v) := hcross u hu y hy hyU
      have hmem : y ∈ s(u, v) := hpair ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : y ∈ s(u, y))
      rcases Sym2.mem_iff.mp hmem with h | h
      · exact absurd h hy.ne'
      · exact Finset.mem_insert.mpr (Or.inl h)
  have hdu : 2 ≤ (T.graph.induce (↑U : Set T.V)).degree ⟨u, hu⟩ := by
    rw [T.degree_induce_eq_card_inter U u hu]
    have hsp := Finset.card_inter_add_card_sdiff (T.graph.neighborFinset u) U
    have hle1 : (T.graph.neighborFinset u \ U).card ≤ 1 := by
      calc (T.graph.neighborFinset u \ U).card ≤ ({v} : Finset T.V).card :=
            Finset.card_le_card (fun y hy => by
              rw [Finset.mem_sdiff] at hy
              rcases Finset.mem_insert.mp (hNsub hy.1) with h | h
              · exact Finset.mem_singleton.mpr h
              · exact absurd h hy.2)
        _ = 1 := Finset.card_singleton v
    have h3 : 3 ≤ T.graph.degree u :=
      T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj huv) hnl
    have hdegc : T.graph.degree u = (T.graph.neighborFinset u).card :=
      (SimpleGraph.card_neighborFinset_eq_degree T.graph u).symm
    omega
  -- ### 4. 把 `∑ deg_{T[U]}` 按「叶 / 非叶」分块
  set Ls : Finset ↥(↑U : Set T.V) :=
    (Finset.univ : Finset ↥(↑U : Set T.V)).filter (fun x => T.graph.degree (x : T.V) = 1)
    with hLs
  set Is : Finset ↥(↑U : Set T.V) :=
    (Finset.univ : Finset ↥(↑U : Set T.V)).filter (fun x => ¬ T.graph.degree (x : T.V) = 1)
    with hIs
  have huIs : (⟨u, hu⟩ : ↥(↑U : Set T.V)) ∈ Is := by
    rw [hIs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hnd⟩
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (T.graph.induce (↑U : Set T.V))
  have hsplit : (∑ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x)
      + (∑ x ∈ Is, (T.graph.induce (↑U : Set T.V)).degree x)
      = ∑ x : ↥(↑U : Set T.V), (T.graph.induce (↑U : Set T.V)).degree x := by
    rw [hLs, hIs, Finset.sum_filter_add_sum_filter_not]
  have hLsum : (∑ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x) = Ls.card := by
    have h : ∀ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x = 1 := by
      intro x hx
      rw [hLs, Finset.mem_filter] at hx
      have hxu : (x : T.V) ≠ u := fun h => hnd (h ▸ hx.2)
      rw [hdeg x x.2 hxu]
      exact hx.2
    rw [Finset.sum_congr rfl h]
    simp
  have hIsum : (T.graph.induce (↑U : Set T.V)).degree ⟨u, hu⟩
      + 3 * (Is.erase ⟨u, hu⟩).card
      ≤ ∑ x ∈ Is, (T.graph.induce (↑U : Set T.V)).degree x := by
    have h1 : 3 * (Is.erase ⟨u, hu⟩).card
        ≤ ∑ x ∈ Is.erase ⟨u, hu⟩, (T.graph.induce (↑U : Set T.V)).degree x := by
      rw [mul_comm]
      refine Finset.card_nsmul_le_sum _ _ 3 (fun x hx => ?_)
      rw [Finset.mem_erase, hIs, Finset.mem_filter] at hx
      have hxu : (x : T.V) ≠ u := fun h => hx.1 (Subtype.ext h)
      rw [hdeg x x.2 hxu]
      exact T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj huv)
        (fun h => hx.2.2 ((T.isLeaf_iff_degree_eq_one (x : T.V)).mp h))
    have h2 := Finset.sum_erase_add Is
      (fun x => (T.graph.induce (↑U : Set T.V)).degree x) huIs
    omega
  -- ### 5. 把子类型上的计数搬回 `U`
  have hcardLs : (U.filter T.IsLeaf).card = Ls.card := by
    rw [hLs]
    have h1 : (U.filter T.IsLeaf)
        = U.filter (fun x => T.graph.degree x = 1) := by
      refine Finset.filter_congr ?_
      intro x _
      exact T.isLeaf_iff_degree_eq_one x
    rw [h1]
    refine (Finset.card_bij (fun (x : ↥(↑U : Set T.V)) _ => (x : T.V)) ?_ ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨a.2, ha.2⟩
    · intro a₁ _ a₂ _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b, hb.1⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
  have hcardIs : (U.filter (fun x => ¬ T.IsLeaf x)).card = Is.card := by
    rw [hIs]
    have h1 : (U.filter (fun x => ¬ T.IsLeaf x))
        = U.filter (fun x => ¬ T.graph.degree x = 1) := by
      refine Finset.filter_congr ?_
      intro x _
      rw [T.isLeaf_iff_degree_eq_one x]
    rw [h1]
    refine (Finset.card_bij (fun (x : ↥(↑U : Set T.V)) _ => (x : T.V)) ?_ ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨a.2, ha.2⟩
    · intro a₁ _ a₂ _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b, hb.1⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
  have hcardU :=
    Finset.card_filter_add_card_filter_not (s := U) (p := T.IsLeaf)
  have hErase : Is.card = (Is.erase ⟨u, hu⟩).card + 1 :=
    (Finset.card_erase_add_one huIs).symm
  rw [hcardLs, hcardIs]
  omega

/-! ### 22.3 计数：无樱桃 ⇒ `叶数 ≤ 非叶数` -/

open scoped Classical in
/-- ★★★ **无樱桃 ⇒ 侧内的叶数 ≤ 非叶数**。

`叶 ↦ 其唯一邻居`（`Cladogram.leafNb`）在侧的叶集上是**单射**且落进**非叶**点：
* 落点在侧内：否则那条边跨越侧，只能是 `s(u,v)` 自己，于是该叶只能是 `u`，与 `u` 非叶冲突；
* 落点非叶：`not_isLeaf_of_adj_of_isLeaf`；
* 单射：两片叶共邻居即樱桃，与 `hnocherry` 冲突。 -/
theorem leaf_card_le_internal_card_of_no_cherry (T : Cladogram X) (U : Finset T.V) {u v : T.V}
    (huv : T.graph.Adj u v) (hu : u ∈ U) (hv : v ∉ U)
    (hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v))
    (hnd : T.graph.degree u ≠ 1)
    (hnocherry : ∀ x y : X, x ≠ y → T.leaf x ∈ U → T.leaf y ∈ U →
      ¬ ∃ w ∈ U, T.graph.Adj (T.leaf x) w ∧ T.graph.Adj (T.leaf y) w) :
    (U.filter T.IsLeaf).card ≤ (U.filter (fun x => ¬ T.IsLeaf x)).card := by
  classical
  have hnl : ¬ T.IsLeaf u := fun h => hnd ((T.isLeaf_iff_degree_eq_one u).mp h)
  have hV3 : 3 ≤ Fintype.card T.V := by
    have h3 := T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj huv) hnl
    have hlt := SimpleGraph.degree_lt_card_verts (G := T.graph) u
    omega
  -- ### 叶的唯一邻居仍在侧内
  have hnbU : ∀ z ∈ U, T.IsLeaf z → T.leafNb z ∈ U := by
    intro z hzU hzl
    by_contra hnot
    have hzdeg : T.graph.degree z = 1 := (T.isLeaf_iff_degree_eq_one z).mp hzl
    have hadj : T.graph.Adj z (T.leafNb z) := T.adj_leafNb hzdeg
    have hp : s(z, T.leafNb z) = s(u, v) := hcross z hzU _ hadj hnot
    have hzmem : z ∈ s(u, v) := hp ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : z ∈ s(z, T.leafNb z))
    rcases Sym2.mem_iff.mp hzmem with h | h
    · exact hnl (h ▸ hzl)
    · exact hv (h ▸ hzU)
  refine Finset.card_le_card_of_injOn (fun z : T.V => T.leafNb z) ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    obtain ⟨hzU, hzl⟩ := hz
    have hzdeg : T.graph.degree z = 1 := (T.isLeaf_iff_degree_eq_one z).mp hzl
    exact ⟨hnbU z hzU hzl, T.not_isLeaf_of_adj_of_isLeaf hV3 hzl (T.adj_leafNb hzdeg)⟩
  · intro z hz z' hz' heq
    simp only [Finset.mem_coe, Finset.mem_filter] at hz hz'
    obtain ⟨hzU, hzl⟩ := hz
    obtain ⟨hz'U, hz'l⟩ := hz'
    have heq' : T.leafNb z = T.leafNb z' := heq
    by_contra hne
    obtain ⟨x, hx⟩ := hzl
    obtain ⟨x', hx'⟩ := hz'l
    have hxx' : x ≠ x' := fun h => hne (by rw [← hx, ← hx', h])
    have hzdeg : T.graph.degree z = 1 := (T.isLeaf_iff_degree_eq_one z).mp ⟨x, hx⟩
    refine hnocherry x x' hxx' (by rw [hx]; exact hzU) (by rw [hx']; exact hz'U)
      ⟨T.leafNb z, hnbU z hzU ⟨x, hx⟩, ?_, ?_⟩
    · rw [hx]; exact T.adj_leafNb hzdeg
    · rw [hx', heq']
      exact T.adj_leafNb ((T.isLeaf_iff_degree_eq_one z').mp ⟨x', hx'⟩)

/-! ### 22.4 收口：侧内有 ≥ 2 叶 ⇒ 侧内有樱桃 -/

open scoped Classical in
/-- ★★★ **侧内有 ≥ 2 片叶 ⇒ 侧内有樱桃**（两片叶共邻居，中心也在侧内）。

`22.2`（`非叶数 + 1 ≤ 叶数`）与 `22.3`（`无樱桃 ⇒ 叶数 ≤ 非叶数`）**相撞**即得。 -/
theorem exists_cherry_of_side (T : Cladogram X) (U : Finset T.V) {u v : T.V}
    (huv : T.graph.Adj u v) (hu : u ∈ U) (hv : v ∉ U)
    (hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v))
    (hE : (T.graph.induce (↑U : Set T.V)).edgeFinset.card + 1 = U.card)
    (hnd : T.graph.degree u ≠ 1)
    (h2 : 2 ≤ (U.filter T.IsLeaf).card) :
    ∃ x y : X, ∃ w : T.V, x ≠ y ∧ T.leaf x ∈ U ∧ T.leaf y ∈ U ∧ w ∈ U ∧
      T.graph.Adj (T.leaf x) w ∧ T.graph.Adj (T.leaf y) w := by
  classical
  by_contra hcon
  push_neg at hcon
  have hno : ∀ x y : X, x ≠ y → T.leaf x ∈ U → T.leaf y ∈ U →
      ¬ ∃ w ∈ U, T.graph.Adj (T.leaf x) w ∧ T.graph.Adj (T.leaf y) w := by
    intro x y hxy hx hy hex
    obtain ⟨w, hwU, ha, hb⟩ := hex
    exact hcon x y w hxy hx hy hwU ha hb
  have h1 := T.leaf_card_le_internal_card_of_no_cherry U huv hu hv hcross hnd hno
  have h2' := T.internal_card_add_one_le_leaf_card U huv hu hv hcross hE hnd
  omega

/-! ### 22.5 ★★★ `cherry_in_component` -/

open scoped Classical in
/-- ★★ **侧内有樱桃（基准点显式版）**：`u` 是割边 `s(u,v)` 的**本侧**端点、`u` 非叶、
`k,l` 都在本侧 ⇒ 本侧有樱桃，且两片叶与中心都在本侧。 -/
theorem cherry_in_side (T : Cladogram X) {u v : T.V} (huv : T.graph.Adj u v) {k l : X}
    (hklne : k ≠ l) (hk : T.inSide s(u, v) (T.leaf k) u)
    (hl : T.inSide s(u, v) (T.leaf k) (T.leaf l)) :
    ∃ i j : X, ∃ w : T.V, i ≠ j ∧ T.graph.Adj (T.leaf i) w ∧ T.graph.Adj (T.leaf j) w ∧
      T.inSide s(u, v) (T.leaf k) w ∧
      T.inSide s(u, v) (T.leaf k) (T.leaf i) ∧ T.inSide s(u, v) (T.leaf k) (T.leaf j) := by
  classical
  set U := T.sideVertices s(u, v) (T.leaf k) with hU
  have hE : (T.graph.induce (↑U : Set T.V)).edgeFinset.card + 1 = U.card := by
    rw [T.card_edgeFinset_induce_sideVertices, ← Set.toFinset_card]
    congr 1
    ext x
    rw [hU]
    simp
  have hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v) :=
    fun x hx y hy hyU => T.eq_edge_of_adj_of_mem_sideVertices_of_notMem hy hx hyU
  have huU : u ∈ U := by
    rw [hU]
    exact (T.mem_sideVertices).mpr hk.symm
  have hvU : v ∉ U := by
    rw [hU, T.mem_sideVertices]
    intro hd
    exact T.not_reachable_deleteEdges_of_adj huv (hk.symm.trans hd.symm)
  -- `u` 非叶：否则本侧只剩 `u` 自己，而 `k,l` 都在本侧且互异
  have hnd : T.graph.degree u ≠ 1 := by
    intro h1
    have huk : T.leaf k = u := T.eq_of_degree_eq_one_of_inSide huv h1 hk.symm
    have hul : T.leaf l = u :=
      T.eq_of_degree_eq_one_of_inSide huv h1 (hk.symm.trans hl)
    exact hklne (T.leaf.injective (huk.trans hul.symm))
  -- 本侧有 ≥ 2 片叶（`k,l`）
  have h2 : 2 ≤ (U.filter T.IsLeaf).card := by
    have hsub : ({k, l} : Finset X) ⊆ T.sideLeaves s(u, v) (T.leaf k) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (T.mem_sideLeaves_iff_inSide).mpr (T.inSide_self _ _)
      · exact (T.mem_sideLeaves_iff_inSide).mpr hl
    have h3 : 2 ≤ (T.sideLeaves s(u, v) (T.leaf k)).card := by
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hklne] at hc
    calc 2 ≤ (T.sideLeaves s(u, v) (T.leaf k)).card := h3
      _ = ((T.sideVertices s(u, v) (T.leaf k)).filter T.IsLeaf).card :=
          T.card_sideLeaves_eq_card_filter_isLeaf (e := s(u, v)) (u := T.leaf k)
      _ = (U.filter T.IsLeaf).card := by rw [hU]
  obtain ⟨i, j, w, hij, hiU, hjU, hwU, hadj_i, hadj_j⟩ :=
    T.exists_cherry_of_side U huv huU hvU hcross hE hnd h2
  rw [hU, T.mem_sideVertices] at hwU hiU hjU
  exact ⟨i, j, w, hij, hadj_i, hadj_j, hwU.symm, hiU.symm, hjU.symm⟩

/-- ★★★ **`cherry_in_component`**（`W49_A_PLAN.md` §4 第 6 项 / 验收标准 #4）：
`e* = s(c,d)` 的 `k` 一侧（`k,l` 同在的那一侧）**必含一颗樱桃**，且两片叶与中心都留在那一侧。

这就是 §21 三条引理里 `hCin` / `hCjn` 的**来源** —— 它把「樱桃取在 `C` 里」从**假设**变成
**结论**（派单验收标准 #4 点名要求的那一条）。 -/
theorem cherry_in_component (T : Cladogram X) {c d : T.V} (hcd : T.graph.Adj c d) {k l : X}
    (hklne : k ≠ l) (hkl : T.inSide s(c, d) (T.leaf k) (T.leaf l)) :
    ∃ i j : X, ∃ w : T.V, i ≠ j ∧ T.graph.Adj (T.leaf i) w ∧ T.graph.Adj (T.leaf j) w ∧
      T.inSide s(c, d) (T.leaf k) w ∧
      T.inSide s(c, d) (T.leaf k) (T.leaf i) ∧ T.inSide s(c, d) (T.leaf k) (T.leaf j) := by
  classical
  rcases T.inSide_or_inSide hcd (x := T.leaf k) with hk | hk
  · exact T.cherry_in_side hcd hklne hk hkl
  · have h := T.cherry_in_side hcd.symm hklne (by rw [Sym2.eq_swap]; exact hk)
      (by rw [Sym2.eq_swap]; exact hkl)
    rw [Sym2.eq_swap] at h
    exact h

end Cladogram


/-! ## 23. ★★★ W50-A-#7：F 的第一块 —— `deg v = 3` 的顶点**覆盖**叶集

F（两条系数和）的几何核心是：在 `P_{k,l}` 的挂点 `v` 处，「三条邻边各自的叶侧」合起来盖住全部叶。
这样 `|L_k(e')| + |L_l(e'')| ≥ n − |L_i(e_{p*})|`，再配 §21 给的 `|L_i(e_{p*})| ≤ n/2`
（`e*` 最小性 ⇒ `ℓ_i ≤ ℓ_k`）即得 `≥ n/2`——这正是 Atteson `:2040` 那句
`|L_k(e_{p*})| ≥ n/2`（`W50_A_MATH.md` §7.1）。

★ **只要「覆盖」，不要「两两不交」**：`W50_A_MATH.md` §7.4 原计划 F1/F2 做「划分」，
需要「路径上恰有一条边贴着终点」这类论证；而 F 的算术只需要 `|L_a| + |L_c| ≥ n − |L_b|`，
**覆盖 ＋ `|L_b| ≤ n/2` 就够** ⇒ 省掉整套不交性论证（F1/F2 合并并弱化，见 §7.4 的修订）。
★ 本节**不用** `IsBinary`，只需要「`v` 的邻居就是 `a,b,c`」这一个等式（二叉时由 `deg = 3` 造出）。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★ **`v` 的三条邻边侧覆盖全部叶**。

取路径 `P_{v, leaf x}`：它的**第一条**边是 `s(v,y)`，`y` 是 `v` 的邻居，故 `y ∈ {a,b,c}`（`hnb`）；
路径的其余部分 `rest` 从 `y` 到 `leaf x`，而路径边表**无重复**（`pathOf_edges_nodup`）
⇒ `s(v,y) ∉ rest.edges` ⇒ `leaf x` 与 `y` 在 `T − s(v,y)` 中可达
（`inSide_of_walk_edges_notMem`）⇒ `x ∈ L_y`。 -/
theorem leaf_mem_sideLeaves_three (T : Cladogram X) {v a b c : T.V}
    (hnb : T.graph.neighborFinset v = {a, b, c})
    (hdeg : T.graph.degree v ≠ 1) :
    ∀ x : X, x ∈ T.sideLeaves s(v, a) a ∨ x ∈ T.sideLeaves s(v, b) b ∨
      x ∈ T.sideLeaves s(v, c) c := by
  classical
  have hnl : ¬ T.IsLeaf v := fun h => hdeg ((T.isLeaf_iff_degree_eq_one v).mp h)
  intro x
  have hnodup := pathOf_edges_nodup T v (T.leaf x)
  have hne : v ≠ T.leaf x := fun h => hnl ⟨x, h.symm⟩
  -- 路径非空 ⇒ 拆成「第一条边 `s(v,y)`」＋「其余 `rest`」（`exists_eq_cons_of_ne` 把中点显式给出）
  obtain ⟨y, hadj, rest, hEq⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (G := T.graph) hne (T.pathOf v (T.leaf x))
  rw [hEq, SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
  obtain ⟨hnotmem, -⟩ := hnodup
  have hmem : y ∈ T.graph.neighborFinset v := (SimpleGraph.mem_neighborFinset _ v y).mpr hadj
  rw [hnb, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hside : T.inSide s(v, y) y (T.leaf x) := T.inSide_of_walk_notMem rest hnotmem
  rcases hmem with rfl | rfl | rfl
  · exact Or.inl ((T.mem_sideLeaves_iff_inSide).mpr hside)
  · exact Or.inr (Or.inl ((T.mem_sideLeaves_iff_inSide).mpr hside))
  · exact Or.inr (Or.inr ((T.mem_sideLeaves_iff_inSide).mpr hside))

/-- ★★★ **三条邻边侧的叶数之和 ≥ n**（覆盖的计数形式）。 -/
theorem card_le_sum_three_sideLeaves (T : Cladogram X) {v a b c : T.V}
    (hnb : T.graph.neighborFinset v = {a, b, c})
    (hdeg : T.graph.degree v ≠ 1) :
    Fintype.card X ≤ (T.sideLeaves s(v, a) a).card + (T.sideLeaves s(v, b) b).card
      + (T.sideLeaves s(v, c) c).card := by
  classical
  have hcov := T.leaf_mem_sideLeaves_three hnb hdeg
  have hsub : (Finset.univ : Finset X)
      ⊆ T.sideLeaves s(v, a) a ∪ T.sideLeaves s(v, b) b ∪ T.sideLeaves s(v, c) c := by
    intro z _
    rcases hcov z with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  have h1 : Fintype.card X
      ≤ (T.sideLeaves s(v, a) a ∪ T.sideLeaves s(v, b) b ∪ T.sideLeaves s(v, c) c).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsub
  have h2 := Finset.card_union_le (T.sideLeaves s(v, a) a ∪ T.sideLeaves s(v, b) b)
    (T.sideLeaves s(v, c) c)
  have h3 := Finset.card_union_le (T.sideLeaves s(v, a) a) (T.sideLeaves s(v, b) b)
  omega

/-- ★★★ **`deg v = 3` 版**：三条具体邻边（互异）即可，`neighborFinset` 的等式自动造出。 -/
theorem card_le_sum_three_sideLeaves_of_degree (T : Cladogram X) {v a b c : T.V}
    (ha : T.graph.Adj v a) (hb : T.graph.Adj v b) (hc : T.graph.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hdeg : T.graph.degree v = 3) :
    Fintype.card X ≤ (T.sideLeaves s(v, a) a).card + (T.sideLeaves s(v, b) b).card
      + (T.sideLeaves s(v, c) c).card := by
  classical
  have hsub : ({a, b, c} : Finset T.V) ⊆ T.graph.neighborFinset v := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hza | hzb | hzc
    · rw [hza]; exact (SimpleGraph.mem_neighborFinset _ v a).mpr ha
    · rw [hzb]; exact (SimpleGraph.mem_neighborFinset _ v b).mpr hb
    · rw [hzc]; exact (SimpleGraph.mem_neighborFinset _ v c).mpr hc
  have hcard : ({a, b, c} : Finset T.V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hnb' : ({a, b, c} : Finset T.V) = T.graph.neighborFinset v := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hcard]
  exact T.card_le_sum_three_sideLeaves (by rw [hnb']) (by rw [hdeg]; norm_num)

/-! ### 23.1 挂点处的 `n/2` 界（Atteson `:2040`） -/

/-- ★★★ **`|L_a| + |L_b| ≥ n/2`**（挂点 `v` 的第三条支 `c` 只占 ≤ `n/2`）。

`c` 支就是 §21 里的 `e_{p*}`（往樱桃去的分支边）：`ℓ_i(e_{p*}) ≤ ℓ_k(e_{p*})`（`e*` 最小性）
＋ `ℓ_i + ℓ_k = n` 给出 `2·|L_c| ≤ n`，再拼上 §23 的覆盖
`n ≤ |L_a| + |L_b| + |L_c|` 即得。 -/
theorem card_le_two_mul_card_add_card_sideLeaves (T : Cladogram X) {v a b c : T.V}
    (ha : T.graph.Adj v a) (hb : T.graph.Adj v b) (hc : T.graph.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hdeg : T.graph.degree v = 3)
    (hmid : 2 * (T.sideLeaves s(v, c) c).card ≤ Fintype.card X) :
    Fintype.card X
      ≤ 2 * ((T.sideLeaves s(v, a) a).card + (T.sideLeaves s(v, b) b).card) := by
  have hcov := T.card_le_sum_three_sideLeaves_of_degree ha hb hc hab hac hbc hdeg
  omega

/-! ### 23.2 配对估计：`c_{e'} + c_{e''} ≥ n − 4` -/

/-- ★★★ **分离 ⇒ 两侧叶数之和 `= n`**（`sideLeafCount_add_of_adj` ＋ 同侧不变性）。 -/
theorem sideLeafCount_add_of_sep (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {x y : T.V} (h : ¬ T.inSide s(a, b) x y) :
    T.sideLeafCount s(a, b) x + T.sideLeafCount s(a, b) y = Fintype.card X := by
  rcases T.inSide_or_inSide hab (x := x) with hx | hx
  · have hy : T.inSide s(a, b) y b := by
      rcases T.inSide_or_inSide hab (x := y) with hy' | hy'
      · exact absurd (hx.trans hy'.symm) h
      · exact hy'
    have e1 := T.sideLeafCount_eq_of_inSide hy
    have e2 := T.sideLeafCount_eq_of_inSide hx
    have e3 := T.sideLeafCount_add_of_adj hab
    omega
  · have hy : T.inSide s(a, b) y a := by
      rcases T.inSide_or_inSide hab (x := y) with hy' | hy'
      · exact hy'
      · exact absurd (hx.trans hy'.symm) h
    have e1 := T.sideLeafCount_eq_of_inSide hy
    have e2 := T.sideLeafCount_eq_of_inSide hx
    have e3 := T.sideLeafCount_add_of_adj hab
    omega

/-- ★★★ **F 的配对估计（Atteson `:2038–2042`）**：两条都分离 `k,l`、都不分离 `i,j`、
都分离 `i,k` 的真边，系数和 `≥ n − 4`。

推导：§19 情形② 给 `c_e = 2(n − S_i(e)) − 2`；`e` 分离 `i,k` ⇒ `S_i(e) = n − S_k(e)`
⇒ `c_e = 2·S_k(e) − 2`；两条相加 `= 2(S_k(e') + S_k(e'')) − 4 ≥ n − 4`（用 `hhalf`）。 -/
theorem attesonW_sub_pair_ge (T : Cladogram X) {a1 b1 a2 b2 : T.V}
    (h1 : T.graph.Adj a1 b1) (h2 : T.graph.Adj a2 b2) {i j k l : X}
    (hkl1 : ¬ T.inSide s(a1, b1) (T.leaf k) (T.leaf l))
    (hkl2 : ¬ T.inSide s(a2, b2) (T.leaf k) (T.leaf l))
    (hij1 : T.inSide s(a1, b1) (T.leaf i) (T.leaf j))
    (hij2 : T.inSide s(a2, b2) (T.leaf i) (T.leaf j))
    (hik1 : ¬ T.inSide s(a1, b1) (T.leaf i) (T.leaf k))
    (hik2 : ¬ T.inSide s(a2, b2) (T.leaf i) (T.leaf k))
    (hhalf : Fintype.card X
      ≤ 2 * (T.sideLeafCount s(a1, b1) (T.leaf k) + T.sideLeafCount s(a2, b2) (T.leaf k))) :
    (Fintype.card X : ℝ) - 4
      ≤ ((T.attesonW (T.leaf k) (T.leaf l) s(a1, b1) : ℝ)
          - (T.attesonW (T.leaf i) (T.leaf j) s(a1, b1) : ℝ))
        + ((T.attesonW (T.leaf k) (T.leaf l) s(a2, b2) : ℝ)
          - (T.attesonW (T.leaf i) (T.leaf j) s(a2, b2) : ℝ)) := by
  rw [T.attesonW_sub_of_not_inSide_inSide hkl1 hij1,
    T.attesonW_sub_of_not_inSide_inSide hkl2 hij2]
  have hs1 := T.sideLeafCount_add_of_sep h1 hik1
  have hs2 := T.sideLeafCount_add_of_sep h2 hik2
  have hhalf' : (Fintype.card X : ℝ)
      ≤ 2 * ((T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ)
        + (T.sideLeafCount s(a2, b2) (T.leaf k) : ℝ)) := by exact_mod_cast hhalf
  have hs1' : (T.sideLeafCount s(a1, b1) (T.leaf i) : ℝ)
      = (Fintype.card X : ℝ) - (T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ) := by
    have h := hs1
    have h' : (T.sideLeafCount s(a1, b1) (T.leaf i) : ℝ)
        + (T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ) = (Fintype.card X : ℝ) := by
      rw [← Nat.cast_add, h]
    linarith
  have hs2' : (T.sideLeafCount s(a2, b2) (T.leaf i) : ℝ)
      = (Fintype.card X : ℝ) - (T.sideLeafCount s(a2, b2) (T.leaf k) : ℝ) := by
    have h' : (T.sideLeafCount s(a2, b2) (T.leaf i) : ℝ)
        + (T.sideLeafCount s(a2, b2) (T.leaf k) : ℝ) = (Fintype.card X : ℝ) := by
      rw [← Nat.cast_add, hs2]
    linarith
  rw [hs1', hs2']
  linarith

end Cladogram


/-! ## 24. ★★★ W50-A-#9：F 的附着边 —— `c_{e'''} = 2(n−4)`／`2(n−3)`

`3(n−4)` 的另一半 `2(n−4)`（Atteson `:2058–2062`）。设 `(i,j)` 是樱桃、中心 `w`，`T` 二叉
⇒ `deg w = 3`，第三条边 `e = s(w,u)`。关键几何事实是**樱桃那一侧恰含两片叶** `{i,j}`：
`deg w = 3` ⇒ `w` 在 `T − e` 里的邻居只有 `leaf i`、`leaf j`，而它们度 1、走不出去
⇒ 该分量恰是 `{w, leaf i, leaf j}`（本节 §24.1 对走法归纳）。

于是 `S_i(e) = 2`、`S_k(e) = n − 2`（`k` 在 `u` 一侧），§19 情形④ 给
`c_e = 2(S_k − S_i) = 2(n−4)`（`DisjointPairs`）；若 `l` 在樱桃一侧（`SharesOneLabel`），
则 §19 情形② 给 `c_e = 2(n − S_i) − 2 = 2(n−3)`。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### 24.1 `deg w = 3` 时删边一侧只剩 `{w, a, b}` -/

/-- ★★ **走法走不出 `{w,a,b}`**：`w` 在 `T − s(w,u)` 中的邻居只有 `a`、`b`（`hne` 排掉 `u`），
而 `a`、`b` 的度是 1（唯一邻居是 `w`）⇒ 从 `{w,a,b}` 里出发的走法整条支持集都在 `{w,a,b}` 里。 -/
theorem support_subset_of_deleteEdges_three (T : Cladogram X) {w a b u : T.V}
    (ha : T.graph.Adj w a) (hb : T.graph.Adj w b)
    (hadeg : T.graph.degree a = 1) (hbdeg : T.graph.degree b = 1)
    (hne : ∀ y, T.graph.Adj w y → y = a ∨ y = b ∨ y = u) :
    ∀ {x z : T.V} (p : (T.graph.deleteEdges {s(w, u)}).Walk x z),
      x = w ∨ x = a ∨ x = b → ∀ y ∈ p.support, y = w ∨ y = a ∨ y = b := by
  intro x z p
  induction p with
  | nil =>
    intro hx y hy
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
    exact hy ▸ hx
  | @cons x' y' z' hadj rest ih =>
    intro hx y hy
    obtain ⟨hadjG, hadjne⟩ := SimpleGraph.deleteEdges_adj.mp hadj
    have hyS : y' = w ∨ y' = a ∨ y' = b := by
      rcases hx with hxw | hxa | hxb
      · -- `x' = w`：`y'` 是 `w` 的邻居且不是 `u`
        rcases hne y' (hxw ▸ hadjG) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exfalso
          rw [hxw, h] at hadjne
          exact hadjne (by simp)
      · -- `x' = a`：`a` 的度是 1
        obtain ⟨w₀, -, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hadeg
        exact Or.inl ((huniq y' (hxa ▸ hadjG)).trans (huniq w ha.symm).symm)
      · -- `x' = b`
        obtain ⟨w₀, -, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hbdeg
        exact Or.inl ((huniq y' (hxb ▸ hadjG)).trans (huniq w hb.symm).symm)
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with hyx | hy
    · rw [hyx]; exact hx
    · exact ih hyS y hy

/-! ### 24.2 樱桃那一侧恰含两片叶 -/

/-- ★★★ **樱桃那一侧恰含两片叶**：`i,j` 是 `w` 的两个叶邻居、`u` 是第三条边、`deg w = 3`
⇒ `sideLeafCount s(w,u) (leaf i) = 2`。

`⊆`：`w` 一侧的任一片叶 `leaf x`，由 `support_subset_of_deleteEdges_three` 落在 `{w, leaf i, leaf j}`
里；`w` 不是叶 ⇒ `x = i` 或 `x = j`。`⊇`：`i`（`mem_sideLeaves_self`）与 `j`（`leaf i → w → leaf j`
两跳，都避开 `s(w,u)`）。 -/
theorem sideLeafCount_cherry_side_eq_two (T : Cladogram X) {i j : X} {w u : T.V}
    (hi : T.graph.Adj (T.leaf i) w) (hj : T.graph.Adj (T.leaf j) w)
    (hij : i ≠ j) (hu : T.graph.Adj w u) (hdeg : T.graph.degree w = 3)
    (hne : ∀ y, T.graph.Adj w y → y = T.leaf i ∨ y = T.leaf j ∨ y = u)
    (hui : u ≠ T.leaf i) (huj : u ≠ T.leaf j) :
    T.sideLeafCount s(w, u) (T.leaf i) = 2 := by
  classical
  have hdi : T.graph.degree (T.leaf i) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf i)).mp ⟨i, rfl⟩
  have hdj : T.graph.degree (T.leaf j) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf j)).mp ⟨j, rfl⟩
  have hnw : ¬ T.IsLeaf w := by
    intro h
    have h1 := (T.isLeaf_iff_degree_eq_one w).mp h
    omega
  -- `w` 与两个叶邻居在 `T − s(w,u)` 中同侧
  have hwi : T.inSide s(w, u) w (T.leaf i) := by
    refine (SimpleGraph.deleteEdges_adj.mpr ⟨hi.symm, ?_⟩).reachable
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    have hmem1 : T.leaf i ∈ s(w, T.leaf i) := Sym2.mem_iff.mpr (Or.inr rfl)
    rw [hmem] at hmem1
    rcases Sym2.mem_iff.mp hmem1 with h | h
    · exact hi.ne h
    · exact hui h.symm
  have hwj : T.inSide s(w, u) w (T.leaf j) := by
    refine (SimpleGraph.deleteEdges_adj.mpr ⟨hj.symm, ?_⟩).reachable
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    have hmem1 : T.leaf j ∈ s(w, T.leaf j) := Sym2.mem_iff.mpr (Or.inr rfl)
    rw [hmem] at hmem1
    rcases Sym2.mem_iff.mp hmem1 with h | h
    · exact hj.ne h
    · exact huj h.symm
  have h2le : 2 ≤ (T.sideLeaves s(w, u) (T.leaf i)).card := by
    have hsub : ({i, j} : Finset X) ⊆ T.sideLeaves s(w, u) (T.leaf i) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact T.mem_sideLeaves_self _ i
      · rw [h]; exact (T.mem_sideLeaves_iff_inSide).mpr (hwi.symm.trans hwj)
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair hij] at hc
  have hle2 : (T.sideLeaves s(w, u) (T.leaf i)).card ≤ 2 := by
    have hsub : T.sideLeaves s(w, u) (T.leaf i) ⊆ ({i, j} : Finset X) := by
      intro x hx
      rw [T.mem_sideLeaves_iff_inSide] at hx
      obtain ⟨p⟩ := hwi.trans hx
      have hsupp := support_subset_of_deleteEdges_three T hi.symm hj.symm hdi hdj hne
        p (Or.inl rfl) (T.leaf x) (SimpleGraph.Walk.end_mem_support p)
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hsupp with h | h | h
      · exact absurd ⟨x, h⟩ hnw
      · exact Or.inl (T.leaf.injective h)
      · exact Or.inr (T.leaf.injective h)
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair hij] at hc
  have := T.sideLeafCount_eq_card_sideLeaves s(w, u) (T.leaf i)
  omega

/-! ### 24.3 附着边的系数：`2(n−4)`（`DisjointPairs`）／`2(n−3)`（`SharesOneLabel`） -/

/-- ★ `w` 与其叶邻居 `leaf i` 在 `T − s(w,u)` 中同侧（只要 `leaf i ≠ u`）。 -/
theorem inSide_leaf_of_adj_ne (T : Cladogram X) {w u : T.V} {i : X}
    (hi : T.graph.Adj (T.leaf i) w) (hne : T.leaf i ≠ u) :
    T.inSide s(w, u) w (T.leaf i) := by
  refine (SimpleGraph.deleteEdges_adj.mpr ⟨hi.symm, ?_⟩).reachable
  intro hmem
  rw [Set.mem_singleton_iff] at hmem
  have hmem1 : T.leaf i ∈ s(w, T.leaf i) := Sym2.mem_iff.mpr (Or.inr rfl)
  rw [hmem] at hmem1
  rcases Sym2.mem_iff.mp hmem1 with h | h
  · exact hi.ne h
  · exact hne h

/-- ★★★ **F 的附着边（`DisjointPairs` 支）**：`k,l` 都在 `u` 一侧 ⇒ `c_{s(w,u)} = 2(n−4)`。

§19 情形④ 给 `c = 2(S_k − S_i)`；`S_i = 2`（§24.2 樱桃侧恰两片叶）、`S_k = n − 2`
（`w` 侧 2 片叶、`k` 在另一侧）⇒ `2((n−2) − 2) = 2(n−4)`。 -/
theorem attesonW_sub_cherry_edge_of_disjoint (T : Cladogram X) {i j k l : X} {w u : T.V}
    (hi : T.graph.Adj (T.leaf i) w) (hj : T.graph.Adj (T.leaf j) w)
    (hij : i ≠ j) (hu : T.graph.Adj w u) (hdeg : T.graph.degree w = 3)
    (hne : ∀ y, T.graph.Adj w y → y = T.leaf i ∨ y = T.leaf j ∨ y = u)
    (hui : u ≠ T.leaf i) (huj : u ≠ T.leaf j)
    (hk : T.inSide s(w, u) u (T.leaf k)) (hl : T.inSide s(w, u) u (T.leaf l)) :
    (T.attesonW (T.leaf k) (T.leaf l) s(w, u) : ℝ)
      - (T.attesonW (T.leaf i) (T.leaf j) s(w, u) : ℝ) = 2 * ((Fintype.card X : ℝ) - 4) := by
  classical
  have hwi : T.inSide s(w, u) w (T.leaf i) := T.inSide_leaf_of_adj_ne (u := u) hi hui.symm
  have hwj : T.inSide s(w, u) w (T.leaf j) := T.inSide_leaf_of_adj_ne (u := u) hj huj.symm
  have hkl : T.inSide s(w, u) (T.leaf k) (T.leaf l) := hk.symm.trans hl
  have hij' : T.inSide s(w, u) (T.leaf i) (T.leaf j) := hwi.symm.trans hwj
  have hSi : T.sideLeafCount s(w, u) (T.leaf i) = 2 :=
    T.sideLeafCount_cherry_side_eq_two hi hj hij hu hdeg hne hui huj
  have hSw : T.sideLeafCount s(w, u) w = 2 := by
    rw [T.sideLeafCount_eq_of_inSide hwi]; exact hSi
  have hSk : T.sideLeafCount s(w, u) (T.leaf k) = T.sideLeafCount s(w, u) u :=
    (T.sideLeafCount_eq_of_inSide hk).symm
  have hsum := T.sideLeafCount_add_of_adj hu
  have hSu : T.sideLeafCount s(w, u) u = Fintype.card X - 2 := by omega
  have h2n : 2 ≤ Fintype.card X := by
    have hc := Finset.card_le_card (Finset.subset_univ ({i, j} : Finset X))
    rwa [Finset.card_pair hij, Finset.card_univ] at hc
  rw [T.attesonW_sub_of_inSide_inSide hkl hij', hSi, hSk, hSu, Nat.cast_sub h2n]
  push_cast
  ring

/-- ★★★ **F 的附着边（`SharesOneLabel` 支）**：`l` 在樱桃一侧 ⇒ `c_{s(w,u)} = 2(n−3)`。

此时 `e` 分离 `k,l`（§19 情形②）而 `i,j` 同侧 ⇒ `c = 2(n − S_i) − 2 = 2(n−2) − 2 = 2(n−3)`。 -/
theorem attesonW_sub_cherry_edge_of_share (T : Cladogram X) {i j k l : X} {w u : T.V}
    (hi : T.graph.Adj (T.leaf i) w) (hj : T.graph.Adj (T.leaf j) w)
    (hij : i ≠ j) (hu : T.graph.Adj w u) (hdeg : T.graph.degree w = 3)
    (hne : ∀ y, T.graph.Adj w y → y = T.leaf i ∨ y = T.leaf j ∨ y = u)
    (hui : u ≠ T.leaf i) (huj : u ≠ T.leaf j)
    (hk : T.inSide s(w, u) u (T.leaf k)) (hl : T.inSide s(w, u) (T.leaf l) w) :
    (T.attesonW (T.leaf k) (T.leaf l) s(w, u) : ℝ)
      - (T.attesonW (T.leaf i) (T.leaf j) s(w, u) : ℝ) = 2 * ((Fintype.card X : ℝ) - 3) := by
  classical
  have hwi : T.inSide s(w, u) w (T.leaf i) := T.inSide_leaf_of_adj_ne (u := u) hi hui.symm
  have hwj : T.inSide s(w, u) w (T.leaf j) := T.inSide_leaf_of_adj_ne (u := u) hj huj.symm
  have hij' : T.inSide s(w, u) (T.leaf i) (T.leaf j) := hwi.symm.trans hwj
  have hSi : T.sideLeafCount s(w, u) (T.leaf i) = 2 :=
    T.sideLeafCount_cherry_side_eq_two hi hj hij hu hdeg hne hui huj
  -- `e` 分离 `k,l`：`k` 在 `u` 侧、`l` 在 `w` 侧
  have hkl : ¬ T.inSide s(w, u) (T.leaf k) (T.leaf l) := by
    intro h
    have huw : T.inSide s(w, u) u w := hk.trans (h.trans hl)
    exact T.not_reachable_deleteEdges_of_adj hu ((T.inSide_comm s(w, u) u w).mp huw)
  rw [T.attesonW_sub_of_not_inSide_inSide hkl hij', hSi]
  push_cast
  ring

end Cladogram


/-! ## 25. ★★★ W50-A-#10：F 的求和层 —— 三条边的贡献 ⇒ 全边之和

F 的两条系数和（§23.2 的 `n−4`、§24.3 的 `2(n−4)`／`2(n−3)`）都是**逐条边**的等式／不等式；
装配要用的是**全部边之和**。本节把两者接起来：其余边由 §21′ 逐边非负，
**直接丢弃**（`Finset.sum_le_sum_of_subset_of_nonneg`）。 -/

/-- ★★★ **求和层**：三条**互异**元素的函数值之和 `≥ K` ⇒ 整个 `Finset` 上的和 `≥ K`
（前提：集合内每项非负）。 -/
theorem le_sum_of_three_mem {α : Type*} [DecidableEq α] (f : α → ℝ) (s : Finset α) {K : ℝ}
    {e1 e2 e3 : α} (h1 : e1 ∈ s) (h2 : e2 ∈ s) (h3 : e3 ∈ s)
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (h0 : ∀ e ∈ s, 0 ≤ f e) (hb : K ≤ f e1 + f e2 + f e3) :
    K ≤ ∑ e ∈ s, f e := by
  classical
  have hsub : ({e1, e2, e3} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · rw [h]; exact h1
    · rw [h]; exact h2
    · rw [h]; exact h3
  have hsum3 : ∑ e ∈ ({e1, e2, e3} : Finset α), f e = f e1 + f e2 + f e3 := by
    rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
    ring
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => h0 x hx)
  calc K ≤ f e1 + f e2 + f e3 := hb
    _ = ∑ e ∈ ({e1, e2, e3} : Finset α), f e := hsum3.symm
    _ ≤ ∑ e ∈ s, f e := hmono


/-! ## 26. ★★★ W50-A-#11：F3／F4 的**算术半边** ＋ 路线的第二次简化

`W50_A_MATH.md` §7.4 原计划用「挂点处**两条**路径边（`e'`、`e''`）配对」得 `n − 4`，并要求
**两条都**分离 `i,k`（§23.2 的 `attesonW_sub_pair_ge` 的 `hik1`/`hik2`）。**这个要求在
Atteson 的选法下不成立**：`e'' = (v_{p*}, v_{p*+1})` 在 `v_{p*}` 的 `l` 侧，`i` 与 `k` 都在它的
同一侧，故 `¬ hik2`。本节把配对估计改成**不对称形**（`e'` 分离 `i,k`、`e''` 分离 `i,l`），
这才是 `W50_A_MATH.md` §7.1 表格里 `|L−L_i(e')| + |L−L_i(e'')| = |L_k(e_{p*})|` 的真正含义。

★ **第二次简化（本轮新得）**：`|L_k(e_{p*})| ≥ n/2` 这一条**不必再证**
—— 它就是 §21 的 `card_le_two_mul_sideLeafCount_of_sep_ik` 作用在**分支边** `e_{p*}` 上
（`hkl` 成立：`k,l` 同在路径侧；`hik` 成立：樱桃在分支侧）。本节的
`two_mul_sideLeafCount_le_card_of_branch` 把它整理成 `2·|L_i(e_{p*})| ≤ n` 的形态。
⇒ F 的算术层到此**全部落地**，剩下的只有 `W50_A_MATH.md` §7.6 记的几何一件：
**在 `P_{k,l}` 上定位樱桃分支的挂点 `v_{p*}` 及其三条邻边**。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **`2·|L_i(e)| ≤ n`**（`Atteson :2040` 的 `|L_k(e_{p*})| ≥ n/2` 的**分支侧形式**）。

`e = s(a,b)` 是**分支边**（`k,l` 在 `a` 侧的路径上、樱桃在 `b` 侧），`e* = s(c,d)` 是离路径边中
`ℓ_k` 最小者、`i` 与 `k` 在 `e*` 同侧。则 `n ≤ 2·S_k(e)`（§21）与 `S_a + S_b = n` 合成
`2·S_b(e) ≤ n`，其中 `S_b(e) = S_i(e)`（`i` 在 `b` 侧）。 -/
theorem two_mul_sideLeafCount_le_card_of_branch (T : Cladogram X) {a b c d : T.V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) {i k l : X}
    (hkl : T.inSide s(a, b) (T.leaf k) (T.leaf l))
    (hik : ¬ T.inSide s(a, b) (T.leaf i) (T.leaf k))
    (hb : T.inSide s(a, b) b (T.leaf i))
    (hCin : T.inSide s(c, d) (T.leaf i) (T.leaf k))
    (hmin : ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet → T.inSide e (T.leaf k) (T.leaf l) →
      T.sideLeafCount s(c, d) (T.leaf k) ≤ T.sideLeafCount e (T.leaf k)) :
    2 * T.sideLeafCount s(a, b) b ≤ Fintype.card X := by
  have hbig := T.card_le_two_mul_sideLeafCount_of_sep_ik hab hcd hkl hik hCin hmin
  -- `k` 在 `a` 侧（否则与 `hik` 冲突）
  have hka : T.sideLeafCount s(a, b) (T.leaf k) = T.sideLeafCount s(a, b) a := by
    rcases T.inSide_or_inSide hab (x := T.leaf k) with h' | h'
    · exact T.sideLeafCount_eq_of_inSide h'
    · exact absurd (h'.trans hb).symm hik
  have hib : T.sideLeafCount s(a, b) (T.leaf i) = T.sideLeafCount s(a, b) b :=
    T.sideLeafCount_eq_of_inSide hb.symm
  have hsum := T.sideLeafCount_add_of_adj hab
  omega

/-- ★★★ **F 的配对估计（不对称版）**：`e'` 分离 `i,k`、`e''` 分离 `i,l`，两者都在 `P_{k,l}` 上
（故都不分离 `k,l`）、都不在 `P_{i,j}` 上，且 `S_k(e') + S_l(e'') ≥ n/2`（`hhalf`）
⇒ `c_{e'} + c_{e''} ≥ n − 4`。

推导：§19 情形② 给两条边各 `c = 2(n − S_i) − 2`；`S_i(e') = n − S_k(e')`、`S_i(e'') = n − S_l(e'')`
⇒ 和 `= 2(S_k(e') + S_l(e'')) − 4 ≥ n − 4`。这正是 `W50_A_MATH.md` §7.1 的
`|L − L_i(e')| + |L − L_i(e'')| = |L_k(e_{p*})| = n − |L_i(e_{p*})|`。 -/
theorem attesonW_sub_pair_ge_of_path (T : Cladogram X) {a1 b1 a2 b2 : T.V}
    (h1 : T.graph.Adj a1 b1) (h2 : T.graph.Adj a2 b2) {i j k l : X}
    (hkl1 : ¬ T.inSide s(a1, b1) (T.leaf k) (T.leaf l))
    (hkl2 : ¬ T.inSide s(a2, b2) (T.leaf k) (T.leaf l))
    (hij1 : T.inSide s(a1, b1) (T.leaf i) (T.leaf j))
    (hij2 : T.inSide s(a2, b2) (T.leaf i) (T.leaf j))
    (hik1 : ¬ T.inSide s(a1, b1) (T.leaf i) (T.leaf k))
    (hil2 : ¬ T.inSide s(a2, b2) (T.leaf i) (T.leaf l))
    (hhalf : Fintype.card X
      ≤ 2 * (T.sideLeafCount s(a1, b1) (T.leaf k) + T.sideLeafCount s(a2, b2) (T.leaf l))) :
    (Fintype.card X : ℝ) - 4
      ≤ ((T.attesonW (T.leaf k) (T.leaf l) s(a1, b1) : ℝ)
          - (T.attesonW (T.leaf i) (T.leaf j) s(a1, b1) : ℝ))
        + ((T.attesonW (T.leaf k) (T.leaf l) s(a2, b2) : ℝ)
          - (T.attesonW (T.leaf i) (T.leaf j) s(a2, b2) : ℝ)) := by
  rw [T.attesonW_sub_of_not_inSide_inSide hkl1 hij1,
    T.attesonW_sub_of_not_inSide_inSide hkl2 hij2]
  have hs1 : (T.sideLeafCount s(a1, b1) (T.leaf i) : ℝ)
      = (Fintype.card X : ℝ) - (T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ) := by
    have h := T.sideLeafCount_add_of_sep h1 hik1
    have h' : (T.sideLeafCount s(a1, b1) (T.leaf i) : ℝ)
        + (T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ) = (Fintype.card X : ℝ) := by
      rw [← Nat.cast_add, h]
    linarith
  have hs2 : (T.sideLeafCount s(a2, b2) (T.leaf i) : ℝ)
      = (Fintype.card X : ℝ) - (T.sideLeafCount s(a2, b2) (T.leaf l) : ℝ) := by
    have h := T.sideLeafCount_add_of_sep h2 hil2
    have h' : (T.sideLeafCount s(a2, b2) (T.leaf i) : ℝ)
        + (T.sideLeafCount s(a2, b2) (T.leaf l) : ℝ) = (Fintype.card X : ℝ) := by
      rw [← Nat.cast_add, h]
    linarith
  have hh : (Fintype.card X : ℝ)
      ≤ 2 * ((T.sideLeafCount s(a1, b1) (T.leaf k) : ℝ)
        + (T.sideLeafCount s(a2, b2) (T.leaf l) : ℝ)) := by exact_mod_cast hhalf
  rw [hs1, hs2]
  linarith

/-- ★★ **单边版**：`e ∈ P_{k,l}`、`i,j` 同侧、`i` 一侧叶数 `≤ (n+2)/2` ⇒ `c_e ≥ n − 4`。

用途：樱桃分支恰好挂在 `P_{k,l}` 的**端点侧**（`v₁` 或 `v_m`）时，一条路径边就够，不必配对。 -/
theorem attesonW_sub_ge_of_path_edge (T : Cladogram X) {e : Sym2 T.V} {i j k l : X}
    (hkl : ¬ T.inSide e (T.leaf k) (T.leaf l))
    (hij : T.inSide e (T.leaf i) (T.leaf j))
    (hS : 2 * T.sideLeafCount e (T.leaf i) ≤ Fintype.card X + 2) :
    (Fintype.card X : ℝ) - 4
      ≤ (T.attesonW (T.leaf k) (T.leaf l) e : ℝ)
        - (T.attesonW (T.leaf i) (T.leaf j) e : ℝ) := by
  rw [T.attesonW_sub_of_not_inSide_inSide hkl hij]
  have hS' : (T.sideLeafCount e (T.leaf i) : ℝ)
      ≤ ((Fintype.card X : ℝ) + 2) / 2 := by
    have h : (2 * T.sideLeafCount e (T.leaf i) : ℝ) ≤ (Fintype.card X : ℝ) + 2 := by
      exact_mod_cast hS
    linarith
  linarith

end Cladogram


/-! ## 27. ★★★ W50-A-#12：`P_{k,l}` **起点处的三条边** —— F 剩余几何的全部起点

F 的两条系数和只需要**一个**挂点：`P_{k,l}` 的**起点侧**（`leaf k` 的邻居 `v`）。
本轮的关键观察（`W50_A_MATH.md` §7.6）是：**不必**去找「樱桃分支与 `P_{k,l}` 的交点 `v_{p*}`」，
因为 `4 ≤ n` ＋ `¬ IsCherry k l` 保证「`P_{k,l}` 的第一条边之后还有边」，于是 `v := leaf k`
的邻居天然带三条互异邻边 `leaf k`、`z`（路径方向）、`c`（分支方向），并且

* `¬ T.inSide s(v,z) (leaf k) (leaf l)` —— `s(v,z)` 是路径边（本节直接给出）；
* `c` 一侧若有两片叶就有樱桃（§22 的 `exists_cherry_of_side`），挂在 `v` 上；
* `c` 一侧若只有一片叶，则 `(k, that leaf)` 本身就是一颗樱桃（`SharesOneLabel`）。

本节落第一件：**存在性与「路径方向」的路径归属**。 -/

namespace Cladogram

open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★★ **`P_{k,l}` 起点处的三条边**：`4 ≤ n` 时，`leaf k` 的邻居 `v` 非叶（度 3），它的
另两条邻边是 `s(v,z)`（**路径方向**，`¬inSide`）与 `s(v,c)`（**分支方向**），且 `z ≠ c`、
两者都不回到 `leaf k`。

技法：`Walk.exists_eq_cons_of_ne` 连拆两次 `pathOf (leaf k) (leaf l)` 的头两步 ⇒ `v`、`z`；
`z ≠ leaf k` 靠路径边表**无重复**（`pathOf_edges_nodup`）；`c` 由「度 3 ⇒ 邻居集基数为 3、
连删两点后剩一点」（`Finset.card_erase_of_mem`）取出。 -/
theorem exists_first_three_of_path (T : Cladogram X) (hbin : T.IsBinary) {k l : X}
    (hklne : k ≠ l) (h4 : 4 ≤ Fintype.card X) :
    ∃ v z c : T.V, T.graph.Adj (T.leaf k) v ∧ T.graph.Adj v z ∧ T.graph.Adj v c ∧
      T.graph.degree v = 3 ∧ v ≠ T.leaf l ∧ z ≠ T.leaf k ∧ c ≠ T.leaf k ∧ z ≠ c ∧
      ¬ T.inSide s(v, z) (T.leaf k) (T.leaf l) := by
  classical
  have hkl' : T.leaf k ≠ T.leaf l := fun h => hklne (T.leaf.injective h)
  obtain ⟨v, hadj_kv, rest, hEq⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (G := T.graph) hkl' (T.pathOf (T.leaf k) (T.leaf l))
  -- ### `v ≠ leaf l`：否则 `k,l` 相邻且都是叶 ⇒ `n = 2`
  have hvl : v ≠ T.leaf l := by
    intro h
    have hadj : T.graph.Adj (T.leaf k) (T.leaf l) := h ▸ hadj_kv
    have e1 := T.sideLeafCount_leaf_edge hadj
    have e2 : T.sideLeafCount s(T.leaf k, T.leaf l) (T.leaf l) = 1 := by
      rw [Sym2.eq_swap]; exact T.sideLeafCount_leaf_edge hadj.symm
    have e3 := T.sideLeafCount_add_of_adj hadj
    omega
  -- ### 第二步：`z`（路径从 `v` 走出的那条边）
  obtain ⟨z, hadj_vz, rest2, hEq2⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (G := T.graph) hvl rest
  -- ### 路径边表无重复 ⇒ `s(v,z) ≠ s(leaf k, v)`
  have hnodup := T.pathOf_edges_nodup (T.leaf k) (T.leaf l)
  rw [hEq, SimpleGraph.Walk.edges_cons, hEq2, SimpleGraph.Walk.edges_cons] at hnodup
  have hsvz : s(v, z) ≠ s(T.leaf k, v) := fun h =>
    (List.nodup_cons.mp hnodup).1 (h ▸ List.mem_cons_self)
  have hzk : z ≠ T.leaf k := fun h => hsvz (by rw [h, Sym2.eq_swap])
  -- ### `v` 非叶 ⇒ 度 3
  have hnleaf : ¬ T.IsLeaf v := by
    intro hleaf
    have hd1 : T.graph.degree v = 1 := (T.isLeaf_iff_degree_eq_one v).mp hleaf
    have hsub : ({z, T.leaf k} : Finset T.V) ⊆ T.graph.neighborFinset v := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v z).mpr hadj_vz
      · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v (T.leaf k)).mpr hadj_kv.symm
    have h2 : 2 ≤ (T.graph.neighborFinset v).card := by
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hzk] at hc
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd1] at h2
    omega
  have hdeg3 : T.graph.degree v = 3 := hbin v hnleaf
  -- ### 取第三条邻边 `c`
  have hcard3 : (T.graph.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg3]
  have hmk : T.leaf k ∈ T.graph.neighborFinset v :=
    (SimpleGraph.mem_neighborFinset _ v (T.leaf k)).mpr hadj_kv.symm
  have hmz : z ∈ T.graph.neighborFinset v :=
    (SimpleGraph.mem_neighborFinset _ v z).mpr hadj_vz
  have hc1 : ((T.graph.neighborFinset v).erase (T.leaf k)).card = 2 := by
    rw [Finset.card_erase_of_mem hmk, hcard3]
  have hzmem : z ∈ (T.graph.neighborFinset v).erase (T.leaf k) :=
    Finset.mem_erase.mpr ⟨hzk, hmz⟩
  have hc2 : (((T.graph.neighborFinset v).erase (T.leaf k)).erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hzmem, hc1]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc2
  have hcmem : c ∈ ((T.graph.neighborFinset v).erase (T.leaf k)).erase z := by
    rw [hc]; exact Finset.mem_singleton_self c
  rw [Finset.mem_erase, Finset.mem_erase] at hcmem
  obtain ⟨hcz, hck, hcnb⟩ := hcmem
  have hadj_vc : T.graph.Adj v c := (SimpleGraph.mem_neighborFinset _ v c).mp hcnb
  -- ### `s(v,z)` 是路径边 ⇒ `¬inSide`
  have hmem : s(v, z) ∈ (T.pathOf (T.leaf k) (T.leaf l)).edges := by
    rw [hEq, SimpleGraph.Walk.edges_cons, hEq2, SimpleGraph.Walk.edges_cons]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact ⟨v, z, c, hadj_kv, hadj_vz, hadj_vc, hdeg3, hvl, hzk, hck, hcz.symm,
    (T.mem_pathOf_edges_iff_not_inSide _ _ _).mp hmem⟩

/-! ### 27.2 `v` 的三个邻居就是 `leaf k`、`z`、`c` -/

/-- ★★ **`neighborFinset v = {leaf k, z, c}`**（三条互异邻边 ＋ 度 3）—— §23 的覆盖定理所需的形式。 -/
theorem neighborFinset_eq_three (T : Cladogram X) {k : X} {v z c : T.V}
    (hkv : T.graph.Adj (T.leaf k) v) (hvz : T.graph.Adj v z) (hvc : T.graph.Adj v c)
    (hdeg : T.graph.degree v = 3)
    (hzk : z ≠ T.leaf k) (hck : c ≠ T.leaf k) (hcz : c ≠ z) :
    T.graph.neighborFinset v = {T.leaf k, z, c} := by
  classical
  have hsub : ({T.leaf k, z, c} : Finset T.V) ⊆ T.graph.neighborFinset v := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h
    · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v (T.leaf k)).mpr hkv.symm
    · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v z).mpr hvz
    · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v c).mpr hvc
  have hcard : ({T.leaf k, z, c} : Finset T.V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hzk.symm, hck.symm]),
      Finset.card_insert_of_notMem (by simp [hcz.symm]), Finset.card_singleton]
  have hle : (T.graph.neighborFinset v).card ≤ ({T.leaf k, z, c} : Finset T.V).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hcard]
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

/-! ### 27.3 起点处的叶数界：`S_v(s(v,z)) ≤ 1 + |B_c|` -/

/-- ★★★ **`v` 一侧的叶数 `≤ 1 + |B_c|`**：`v` 的邻居是 `leaf k`、`z`、`c`，于是 `s(v,z)` 的
`v` 一侧只可能装 `leaf k` 与 `c` 一侧的叶（覆盖 §23 ＋ 补集 `sideLeaves_compl_adj`）。

这正是 `W50_A_MATH.md` §7.6 里 `S_i(s(v,z)) = 1 + |B_c|` 的「`≤`」半边 —— 配对／单边估计
只需要这个方向。 -/
theorem sideLeafCount_start_le (T : Cladogram X) {k : X} {v z c : T.V}
    (hkv : T.graph.Adj (T.leaf k) v) (hvz : T.graph.Adj v z) (hvc : T.graph.Adj v c)
    (hnb : T.graph.neighborFinset v = {T.leaf k, z, c})
    (hdeg : T.graph.degree v ≠ 1) :
    T.sideLeafCount s(v, z) v ≤ 1 + T.sideLeafCount s(v, c) c := by
  classical
  have hle_k : T.sideLeaves s(v, T.leaf k) (T.leaf k) = {k} := by
    rw [Sym2.eq_swap]; exact T.sideLeaves_leaf_edge hkv
  have hsub : T.sideLeaves s(v, z) v ⊆ insert k (T.sideLeaves s(v, c) c) := by
    intro x hx
    rcases T.leaf_mem_sideLeaves_three hnb hdeg x with h | h | h
    · rw [hle_k, Finset.mem_singleton] at h
      rw [h]; exact Finset.mem_insert_self _ _
    · exfalso
      rw [T.sideLeaves_compl_adj hvz, Finset.mem_compl] at h
      exact h hx
    · exact Finset.mem_insert_of_mem h
  have h1 : (T.sideLeaves s(v, z) v).card ≤ (insert k (T.sideLeaves s(v, c) c)).card :=
    Finset.card_le_card hsub
  have h2 : (insert k (T.sideLeaves s(v, c) c)).card ≤ (T.sideLeaves s(v, c) c).card + 1 :=
    Finset.card_insert_le _ _
  show (T.sideLeaves s(v, z) v).card ≤ 1 + (T.sideLeaves s(v, c) c).card
  omega

/-! ### 27.4 起点的第二支：`c` 侧只有一片叶 ⇒ 樱桃 `(k, x)`

`W50_A_MATH.md` §7.6.3 的 ②B 支。`S_c = 1` 时 `c` 必须是叶（`two_le_sideLeafCount` 的
**逆否**：非叶点的每侧至少两片叶），于是 `c = leaf x`，而 `(k,x)` 就是挂在 `v` 上的樱桃 ——
它与目标对 `(k,l)` **恰交一个标签**（`SharesOneLabel k x k l` 由 `k = k` 立即成立）。

★ 为什么这条能把 `c` 一侧「一片叶」的坏情形变好：`v` 的第三条边 `s(v,c)` **不再是路径边**
（它是挂边），于是 `S_k(s(v,z)) = 1 + |B_c| = 2` 达到 §23 覆盖界的最小值，起点边 `s(v,z)`
单独就能给出整整 `2(n−3)`。 -/

/-- ★★★ **`S_c = 1` ⇒ `c` 是叶且 `(k, x)` 是挂在 `v` 上的樱桃**（`x ≠ k`、`x ≠ l`）。

`x ≠ l` 是**非樱桃假设**的关键用处：否则 `v` 同时邻接 `leaf k` 与 `leaf l`，`(k,l)` 本身就是
樱桃，与本支的前提矛盾。 -/
theorem exists_cherry_of_start_side_card_one (T : Cladogram X) {k l : X} (hklne : k ≠ l)
    (hncher : ¬ T.IsCherry k l) {v c : T.V}
    (hkv : T.graph.Adj (T.leaf k) v) (hvc : T.graph.Adj v c) (hck : c ≠ T.leaf k)
    (hS : T.sideLeafCount s(v, c) c = 1) :
    ∃ x : X, T.leaf x = c ∧ x ≠ k ∧ x ≠ l ∧ T.IsCherry k x ∧ T.graph.Adj (T.leaf x) v := by
  classical
  -- ### `c` 是叶：非叶点的每侧 ≥ 2 片叶
  have hdc1 : T.graph.degree c = 1 := by
    by_contra hd
    have h2 := T.two_le_sideLeafCount hvc.symm hd
    rw [Sym2.eq_swap] at h2
    omega
  obtain ⟨x, hx⟩ := (T.isLeaf_iff_degree_eq_one c).mpr hdc1
  have hxk : x ≠ k := by
    intro h
    exact hck (by rw [← h, hx])
  have hxl : x ≠ l := by
    intro h
    exact hncher ⟨hklne, v, hkv, by rw [← h, hx]; exact hvc.symm⟩
  exact ⟨x, hx, hxk, hxl, ⟨hxk.symm, v, hkv, by rw [hx]; exact hvc.symm⟩,
    by rw [hx]; exact hvc.symm⟩

/-- ★★★ **第二支的系数下界**：`S_c = 1` 时起点边 `s(v,z)` 给出 `c_e ≥ 2(n−3)`。

`leaf k → v → c = leaf x` 是 `T − s(v,z)` 中的一条 **2-步 walk**（其余两条边都不是 `e`），
故 `e` **分离** `(k,x)` 而**不分离** `(k,l)` ⇒ `c_e = 2(n − S_k) − 2`，而 §27.3 ＋ `S_c = 1`
给 `S_k ≤ 2`，于是 `c_e ≥ 2(n−2) − 2 = 2(n−3)`。 -/
theorem attesonW_sub_start_of_side_card_one (T : Cladogram X) {k l x : X} {v z c : T.V}
    (hkv : T.graph.Adj (T.leaf k) v) (hvz : T.graph.Adj v z) (hvc : T.graph.Adj v c)
    (hnb : T.graph.neighborFinset v = {T.leaf k, z, c}) (hdeg : T.graph.degree v ≠ 1)
    (hzk : z ≠ T.leaf k) (hcz : z ≠ c) (hx : T.leaf x = c)
    (hS : T.sideLeafCount s(v, c) c = 1)
    (hpath : ¬ T.inSide s(v, z) (T.leaf k) (T.leaf l)) :
    2 * ((Fintype.card X : ℝ) - 3)
      ≤ (T.attesonW (T.leaf k) (T.leaf l) s(v, z) : ℝ)
        - (T.attesonW (T.leaf k) (T.leaf x) s(v, z) : ℝ) := by
  classical
  -- ### 两条边都不等于 `e = s(v,z)`
  have hne1 : s(T.leaf k, v) ≠ s(v, z) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hvz.ne h2
    · exact hzk h1.symm
  have hne2 : s(v, c) ≠ s(v, z) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hcz h2.symm
    · exact hvz.ne h1
  -- ### `T − e` 中的 2-步 walk `leaf k → v → c`
  have a1 : (T.graph.deleteEdges {s(v, z)}).Adj (T.leaf k) v :=
    deleteEdges_adj.mpr ⟨hkv, hne1⟩
  have a2 : (T.graph.deleteEdges {s(v, z)}).Adj v c :=
    deleteEdges_adj.mpr ⟨hvc, hne2⟩
  have hkv' : T.inSide s(v, z) (T.leaf k) v := a1.reachable
  have hxside : T.inSide s(v, z) (T.leaf k) (T.leaf x) := by
    rw [hx]
    exact hkv'.trans a2.reachable
  -- ### `S_k ≤ 2`：§27.3 ＋ `S_c = 1`
  have hSv : T.sideLeafCount s(v, z) v ≤ 1 + T.sideLeafCount s(v, c) c :=
    T.sideLeafCount_start_le hkv hvz hvc hnb hdeg
  have hS2 : T.sideLeafCount s(v, z) (T.leaf k) ≤ 2 := by
    rw [T.sideLeafCount_eq_of_inSide hkv']
    omega
  -- ### `c_e = 2(n − S_k) − 2`
  rw [T.attesonW_sub_of_not_inSide_inSide (i := T.leaf k) (j := T.leaf x) hpath hxside]
  have hS2' : (T.sideLeafCount s(v, z) (T.leaf k) : ℝ) ≤ 2 := by exact_mod_cast hS2
  linarith

/-! ### 27.4′ **`l` 端的镜像**（Case S 的另一半，`W50_A_MATH.md` §7.9.1）

Case S（`k` 或 `l` 落在樱桃里）关于 `k ↔ l` **完全对称**：一旦 `l` 落在樱桃 `(l, y)` 里，
§27.4 的整条论证把 `k,l` 互换即可。本节把这件事落成一条**可直接调用**的引理，免得在装配处
手工搬 `attesonW_comm` 的方向（那里极易写反）。

★ 结论的形状要注意：`l` 端给的是 `Q(k,l) − Q(l,y)`，而 §27.4 的 `k` 端给的是
`Q(k,l) − Q(k,x)` —— 两者**不能**互换使用，装配时按「`k` 在樱桃里 ⇒ 用 `_k` 版；
`l` 在樱桃里 ⇒ 用本版」分派。 -/

/-- ★★★ **第二支的系数下界（`l` 端镜像）**：`l` 挂在 `v` 上、`S_c = 1` ⇒ 起点边给出
`c_e ≥ 2(n−3)`，此处 `(i,j) = (l, y)`，`leaf y = c`。

由 §27.4 的 `attesonW_sub_start_of_side_card_one` 以 `(k,l,x) := (l,k,y)` 实例化，
再用 `attesonW_comm` 把两处 `attesonW (leaf l) (leaf k)`／`attesonW (leaf l) (leaf y)`
翻回 `(leaf k, leaf l)`／`(leaf y, leaf l)`。 -/
theorem attesonW_sub_start_of_side_card_one_l (T : Cladogram X) {k l y : X} {v z c : T.V}
    (hlv : T.graph.Adj (T.leaf l) v) (hvz : T.graph.Adj v z) (hvc : T.graph.Adj v c)
    (hnb : T.graph.neighborFinset v = {T.leaf l, z, c}) (hdeg : T.graph.degree v ≠ 1)
    (hzk : z ≠ T.leaf l) (hcz : z ≠ c) (hx : T.leaf y = c)
    (hS : T.sideLeafCount s(v, c) c = 1)
    (hpath : ¬ T.inSide s(v, z) (T.leaf l) (T.leaf k)) :
    2 * ((Fintype.card X : ℝ) - 3)
      ≤ (T.attesonW (T.leaf k) (T.leaf l) s(v, z) : ℝ)
        - (T.attesonW (T.leaf y) (T.leaf l) s(v, z) : ℝ) := by
  have h := T.attesonW_sub_start_of_side_card_one (k := l) (l := k) (x := y)
    hlv hvz hvc hnb hdeg hzk hcz hx hS hpath
  rw [← T.attesonW_comm (T.leaf k) (T.leaf l) s(v, z),
    ← T.attesonW_comm (T.leaf y) (T.leaf l) s(v, z)] at h
  exact h

/-! ### 27.5 樱桃与目标对的形态二分（**树层**，`W50_A_MATH.md` §7.6.2 的装配前提）

`IsCherrySeparated` 的两条分支要求：非樱桃对 `(k,l)` 与樱桃 `(i,j)` 要么**不交**、要么
**恰交一个标签**。度量层已有 ★★ `NJ.Dissimilarity.disjointPairs_or_sharesOneLabel_of_isCherry`
（`:1064`）；本节的**树层**版本供 §27.4／§27.6 的构造直接使用 —— 那里只知道
`T.IsCherry i j`（由 `v` 处的两条邻边造出），并不知道任何距离。

技法：`i,j` 都不在 `{k,l}` 里 ⇒ `DisjointPairs`；否则（如 `i = k`）另一片叶 `j` 必不等于 `l`
（否则 `IsCherry k l`，与非樱桃假设矛盾）⇒ 落入 `SharesOneLabel` 的对应形态。 -/
theorem disjointPairs_or_sharesOneLabel_of_tree_isCherry (T : Cladogram X) {i j k l : X}
    (hch : T.IsCherry i j) (hnc : ¬ T.IsCherry k l) :
    NJ.Dissimilarity.DisjointPairs i j k l ∨
      NJ.Dissimilarity.SharesOneLabel i j k l := by
  have hch' := hch
  obtain ⟨hij, -⟩ := hch
  by_cases hik : i = k
  · exact Or.inr (Or.inl ⟨hik, fun h => hij (hik.trans h.symm),
      fun h => hnc (h ▸ (hik ▸ hch'))⟩)
  by_cases hil : i = l
  · exact Or.inr (Or.inr (Or.inl ⟨hil, fun h => hnc (T.isCherry_symm (h ▸ (hil ▸ hch'))),
      fun h => hij (hil.trans h.symm)⟩))
  by_cases hjk : j = k
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hjk, hik, hil⟩)))
  by_cases hjl : j = l
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hjl, hik, hil⟩)))
  exact Or.inl ⟨hik, hil, hjk, hjl⟩

/-! ### 27.6 起点的第一支：`2 ≤ S_c` ⇒ `c` 侧有樱桃

`W50_A_MATH.md` §7.6.3 的 ②A 支。**不必**重做 §22.4 的枚举：c 侧若有两片叶，§22 的
★★★ `cherry_in_component` 直接给出侧内樱桃（它自带「侧内叶数 ≥ 2 ⇒ 侧内有樱桃」的计数相撞）。

★ 本支真正的算术难点不在几何，而在 **`2|B_c| ≤ n`**：起点边 `s(v,z)` 的 `k` 一侧恰是
`{k} ∪ B_c`，故 `S_k = 1 + |B_c|`，于是 `c_e = 2(n − 1 − |B_c|) − 2 ≥ n − 4` **⟺ `2|B_c| ≤ n`**。
后者要用 §21／§26 的 `e*` 最小性（`two_mul_sideLeafCount_le_card_of_branch`），故留到 §28
与 `e*` 同在的作用域里；本节只落**几何**（樱桃 ＋ 两片叶都在 c 侧 ＋ 叶数相等）。 -/
theorem exists_cherry_of_start_side_two_le (T : Cladogram X) {v c : T.V}
    (hvc : T.graph.Adj v c) (h2 : 2 ≤ T.sideLeafCount s(v, c) c) :
    ∃ i j : X, ∃ w : T.V, i ≠ j ∧ T.IsCherry i j ∧
      T.sideLeafCount s(v, c) (T.leaf i) = T.sideLeafCount s(v, c) c ∧
      T.inSide s(v, c) c (T.leaf i) ∧ T.inSide s(v, c) c (T.leaf j) ∧
      T.inSide s(v, c) c w := by
  classical
  have hlt : 1 < (T.sideLeaves s(v, c) c).card := by
    have h := h2
    rw [T.sideLeafCount_eq_card_sideLeaves] at h
    omega
  obtain ⟨i₀, hi₀, j₀, hj₀, hij₀⟩ := Finset.one_lt_card.mp hlt
  have hi' : T.inSide s(v, c) c (T.leaf i₀) := (T.mem_sideLeaves_iff_inSide).mp hi₀
  have hj' : T.inSide s(v, c) c (T.leaf j₀) := (T.mem_sideLeaves_iff_inSide).mp hj₀
  obtain ⟨i, j, w, hij, hwi, hwj, hw, hii, hjj⟩ :=
    T.cherry_in_component (c := v) (d := c) (k := i₀) (l := j₀) hvc hij₀ (hi'.symm.trans hj')
  exact ⟨i, j, w, hij, ⟨hij, w, hwi, hwj⟩,
    (T.sideLeafCount_eq_of_inSide (hi'.trans hii)).symm, hi'.trans hii, hi'.trans hjj,
    hi'.trans hw⟩

/-! ### 27.7 ★★★ 中间边两侧都 ≥ 2 片叶（`m ≥ 3` 的**计数形式**）

`W50_A_MATH.md` §7.11。装配时两端各出 `2(n−4)`，再加上 `s(v,z)` 这条**中间边**两端的
「同侧形」系数 `2(n − ℓ_k) − 2` 与 `2(n − ℓ_l) − 2`，合计 `2n − 4`，故

　　　`gap_k + gap_l ≥ 4(n−4) + (2n−4) = 6n − 20 ≥ 6(n−4)`

**这一步只需要 `s(v,z)` 两侧各 `≥ 2` 片叶**，不需要路径长度 `m` 的任何计数 ——
上一批以为要数「`m − 2` 条中间边」，其实**一条中间边就够**（每条中间边两端合计 `2n−4`，
而当 `m = 3` 时 `4(n−4) + (2n−4) ≥ 6(n−4)` 仍成立，`n ≥ 4`）。

★ 为什么两侧都 ≥ 2：
* `k` 侧：`v` 是内点（邻 `leaf k` 与 `z` 两点 ⇒ 度 ≠ 1）⇒ 它那一侧 ≥ 2 片叶；
* `l` 侧：`z` 不是叶（否则 `z = leaf l`，则 `v` 同时邻 `leaf k` 与 `leaf l`，
  `(k,l)` 成樱桃，与 `¬IsCherry k l` 矛盾）⇒ `z` 那一侧 ≥ 2 片叶，
  而 `l` 与 `z` 同侧（`inSide_or_inSide` ＋ `¬inSide k l` 排除另一支）。 -/

/-- ★★★ **中间边 `s(v,z)` 两侧各 ≥ 2 片叶**：`v` 是 `leaf k` 的邻居、`z` 是路径方向、
`(k,l)` 不是樱桃 ⇒ `2 ≤ ℓ_k(s(v,z))` 且 `2 ≤ ℓ_l(s(v,z))`。

有了这条，`s(v,z)` 既不是首边（`ℓ_k = 1`）也不是末边（`ℓ_l = 1`），于是两端都能对它用
**同侧形**系数（§28 `attesonW_sub_path_eq_near_k`）。 -/
theorem two_le_sideLeafCount_middle (T : Cladogram X) {k l : X} (hklne : k ≠ l)
    (hncher : ¬ T.IsCherry k l) {v z : T.V}
    (hkv : T.graph.Adj (T.leaf k) v) (hvz : T.graph.Adj v z) (hkz : z ≠ T.leaf k)
    (hpath : ¬ T.inSide s(v, z) (T.leaf k) (T.leaf l)) :
    2 ≤ T.sideLeafCount s(v, z) (T.leaf k) ∧ 2 ≤ T.sideLeafCount s(v, z) (T.leaf l) := by
  classical
  -- ### `s(leaf k, v) ≠ s(v,z)`：否则 `z = leaf k`
  have hne1 : s(T.leaf k, v) ≠ s(v, z) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hvz.ne h2
    · exact hkz h1.symm
  -- ### `k` 与 `v` 同侧
  have hkv' : T.inSide s(v, z) (T.leaf k) v :=
    (SimpleGraph.deleteEdges_adj.mpr ⟨hkv, hne1⟩).reachable
  -- ### `v` 非叶 ⇒ `2 ≤ ℓ_v`
  have hndv : T.graph.degree v ≠ 1 := by
    intro hd
    have hsub : ({T.leaf k, z} : Finset T.V) ⊆ T.graph.neighborFinset v := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v (T.leaf k)).mpr hkv.symm
      · rw [h]; exact (SimpleGraph.mem_neighborFinset _ v z).mpr hvz
    have h2 : 2 ≤ (T.graph.neighborFinset v).card := by
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hkz.symm] at hc
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd] at h2
    omega
  have h2v : 2 ≤ T.sideLeafCount s(v, z) v := T.two_le_sideLeafCount hvz hndv
  constructor
  · rwa [← T.sideLeafCount_eq_of_inSide hkv'] at h2v
  · -- ### `l` 与 `z` 同侧
    have hzvl : T.inSide s(v, z) z (T.leaf l) := by
      rcases T.inSide_or_inSide (x := T.leaf l) hvz with h | h
      · have hkl' : T.inSide s(v, z) (T.leaf k) (T.leaf l) :=
          hkv'.trans ((T.inSide_comm s(v, z) (T.leaf l) v).mp h)
        exact absurd hkl' hpath
      · exact (T.inSide_comm s(v, z) (T.leaf l) z).mp h
    -- ### `z` 不是叶：否则 `z = leaf l`，`(k,l)` 成樱桃
    have hznl : ¬ T.IsLeaf z := by
      intro hleaf
      obtain ⟨x, hx⟩ := hleaf
      have hadj : T.graph.Adj (T.leaf x) v := by rw [hx]; exact hvz.symm
      have hset : T.sideLeaves s(v, z) z = {x} := by
        rw [← hx, Sym2.eq_swap]; exact T.sideLeaves_leaf_edge hadj
      have hmem : l ∈ T.sideLeaves s(v, z) z := (T.mem_sideLeaves_iff_inSide).mpr hzvl
      rw [hset, Finset.mem_singleton] at hmem
      exact hncher ⟨hklne, v, hkv, by rw [hmem, hx]; exact hvz.symm⟩
    have hndz : T.graph.degree z ≠ 1 := fun hd => hznl ((T.isLeaf_iff_degree_eq_one z).mpr hd)
    have h2z : 2 ≤ T.sideLeafCount s(z, v) z := T.two_le_sideLeafCount hvz.symm hndz
    rw [Sym2.eq_swap] at h2z
    rwa [T.sideLeafCount_eq_of_inSide hzvl] at h2z

/-! ### 27.8 ★★★ **跨边的同侧传递**（`W50_A_MATH.md` §7.11.5 第 5 项）

同一个顶点 `a` 的两条邻边 `s(a,b)`、`s(a,c)`：**`b` 侧的顶点在 `s(a,c)` 下仍与 `a` 同侧**。

　　　`inSide s(a,b) b x` ⇒ `inSide s(a,c) a x`　（`s(a,b) ≠ s(a,c)`，即 `b ≠ c`；`b ≠ c` 给 `a ≠ b`）

★ 为什么需要它：§27.6 的樱桃只给 `inSide s(v,c) c (leaf i)`（**分支边**），而装配要的是
`inSide s(v,z) (leaf k) (leaf i)`（**中间边**）。这两条边共用顶点 `v`，本条引理就是那座桥。

证明要点：`x` 在 `b` 侧 ⇒ 存在 `b → x` 的 walk 不走 `s(a,b)`。**该 walk 不可能经过 `a`**
（否则前缀给出 `inSide s(a,b) b a`，与 `not_inSide_both` ＋ `inSide_self` 矛盾），
故它的每一步都不是 `s(a,c)`（`s(a,c)` 的端点是 `a`、`c`，而 `c` 与 `b` 异侧：
`¬inSide s(a,b) b c`）。于是同一条 walk 在 `G − s(a,c)` 里仍然有效，再补上 `a — b` 这条边。 -/

/-- ★★★ **跨边同侧传递**：`a` 的两条邻边 `s(a,b)`／`s(a,c)`（`b ≠ c`），
`b` 侧的 `x` 在 `s(a,c)` 下与 `a` 同侧。 -/
theorem inSide_of_inSide_adj_swap (T : Cladogram X) {a b c x : T.V}
    (hab : T.graph.Adj a b) (hac : T.graph.Adj a c) (hbc : b ≠ c)
    (hbx : T.inSide s(a, b) b x) : T.inSide s(a, c) a x := by
  classical
  -- ### `b`、`c` 都不在 `b` 侧
  have hnab : ¬ T.inSide s(a, b) b a :=
    fun h' => T.not_inSide_both hab (y := a) ⟨T.inSide_self s(a, b) a, h'⟩
  have hneab : s(a, b) ≠ s(a, c) := by
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hbc h2
    · exact hab.ne h2.symm
  have hac_side : T.inSide s(a, b) a c :=
    (SimpleGraph.deleteEdges_adj.mpr ⟨hac, hneab.symm⟩).reachable
  have hncb : ¬ T.inSide s(a, b) b c := by
    intro hcon
    exact hnab ((T.inSide_comm s(a, b) a b).mp
      (hac_side.trans ((T.inSide_comm s(a, b) b c).mp hcon)))
  -- ### 旁侧连通性（`Split.lean:685`）：`b` 侧的 walk 在 `G − s(a,c)` 里仍走得通
  have hside : T.inSide s(a, c) b x :=
    T.inSide_deleteEdges_of_inSide (e₁ := s(a, b)) (e₂ := s(a, c)) (c := a) (d := c)
      rfl hbx hnab hncb
  exact (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hneab⟩).reachable.trans hside

/-! ## 28. ★★★ W50-A-#19：Case D 的**逐边系数**（路径边上的 `c_e` 的显式值）

`W50_A_MATH.md` §7.9.2 的两端求和要求：对 `P_{k,l}` 上的**每一条**边给出 `c_e` 的显式值，
且该值只依赖「`k` 侧叶数 `ℓ_k(e)`」。樱桃 `(i,j)` 在起点分支内（Case D），故 `i,j` 都与 `k`
同侧、或都与 `k` 异侧 —— 恰好两种形状：

| `(i,j)` 相对 `k` | `c_e` | 本节定理 |
|---|---|---|
| **同侧**（`r ≥ 2` 的路径边） | `2(n − ℓ_k(e)) − 2 = 2·ℓ_l(e) − 2` | `attesonW_sub_path_eq_near_k` / `_near_k'` |
| **异侧**（首边 `e₁ = ⟦k,x₁⟧`） | `2·ℓ_k(e) − 2` | `attesonW_sub_path_eq_far_k` |

★ 首边 `ℓ_k(e₁) = 1`、末边 `ℓ_l(e_m) = 1`，两种形状**同时**退化为 `0`（`_zero_of_sideLeafCount_one`）
—— 这就是 §7.9.2 里「两端路径边不贡献、贡献只来自中间 `m − 2` 条边」的 Lean 依据。

★ 与 §19 的区别：§19 的形状用 `S_i(e)` 写（取决于 `(i,j)` 落在哪侧），本节用 `ℓ_k(e)` 写 ——
**同一侧的两条路径边可以有不同的 `ℓ_k`**，但求和号里 `ℓ_k` 是唯一变量，这样才可加。 -/

/-- ★★★ **Case D｜路径边（同侧形）**：`e` 分离 `k,l`、`i,j` 同侧、且 `i` 与 `k` **同侧** ⇒

　　`c_e = 2·(n − ℓ_k(e)) − 2`。

这是 §19 情形②（`2(n − S_i) − 2`）＋「同侧 ⇒ `S_i = ℓ_k`」（`sideLeafCount_eq_of_inSide`）。 -/
theorem attesonW_sub_path_eq_near_k (T : Cladogram X) {e : Sym2 T.V} {i j k l : T.V}
    (hkl : ¬ T.inSide e k l) (hij : T.inSide e i j) (hki : T.inSide e k i) :
    (T.attesonW k l e : ℝ) - (T.attesonW i j e : ℝ)
      = 2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e k : ℝ)) - 2 := by
  rw [T.attesonW_sub_of_not_inSide_inSide hkl hij, T.sideLeafCount_eq_of_inSide hki]

/-- ★★★ **Case D｜路径边（同侧形，按 `ℓ_l` 写）**：同上，再用 `ℓ_k(e) + ℓ_l(e) = n`，

　　`c_e = 2·ℓ_l(e) − 2`。

★ 这个写法正是 §7.9.2 `l` 端求和里出现的项：`Σ_{r=1}^{m-1}(2ℓ_k(e_r) − 2)` 与
`Σ_{r=2}^{m}(2ℓ_l(e_r) − 2)` 把同一条中间边从两端各数一次，两份相加后 `ℓ_k + ℓ_l = n` 才用得上。 -/
theorem attesonW_sub_path_eq_near_k' (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j k l : T.V} (hkl : ¬ T.inSide s(a, b) k l) (hij : T.inSide s(a, b) i j)
    (hki : T.inSide s(a, b) k i) :
    (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ)
      = 2 * (T.sideLeafCount s(a, b) l : ℝ) - 2 := by
  rw [T.attesonW_sub_path_eq_near_k hkl hij hki]
  have hsum : (T.sideLeafCount s(a, b) k : ℝ) + (T.sideLeafCount s(a, b) l : ℝ)
      = (Fintype.card X : ℝ) := by
    exact_mod_cast T.sideLeafCount_add_of_sep hab hkl
  linarith

/-- ★★★ **Case D｜首边（异侧形）**：`e` 分离 `k,l`、`i,j` 同侧、但 `i` 与 `k` **异侧** ⇒

　　`c_e = 2·ℓ_k(e) − 2`。

`S_i = n − ℓ_k(e)`（`sideLeafCount_add_of_sep`）⇒ `2(n − S_i) − 2 = 2ℓ_k(e) − 2`。 -/
theorem attesonW_sub_path_eq_far_k (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b)
    {i j k l : T.V} (hkl : ¬ T.inSide s(a, b) k l) (hij : T.inSide s(a, b) i j)
    (hik : ¬ T.inSide s(a, b) k i) :
    (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ)
      = 2 * (T.sideLeafCount s(a, b) k : ℝ) - 2 := by
  rw [T.attesonW_sub_of_not_inSide_inSide hkl hij]
  have hsum : (T.sideLeafCount s(a, b) k : ℝ) + (T.sideLeafCount s(a, b) i : ℝ)
      = (Fintype.card X : ℝ) := by
    exact_mod_cast T.sideLeafCount_add_of_sep hab hik
  linarith

/-- ★★★ **Case D｜首边不贡献**：异侧形且 `ℓ_k(e) = 1` ⇒ `c_e = 0`。

`e = ⟦k,x₁⟧` 时 `k` 侧只有 `k` 一片叶（`sideLeafCount_leaf_edge`），故 `2·1 − 2 = 0`。
这是 §7.9.2 里 `Σ` 的下限 `m − 2`（而非 `m`）的来源。 -/
theorem attesonW_sub_path_eq_zero_of_sideLeafCount_one (T : Cladogram X) {a b : T.V}
    (hab : T.graph.Adj a b) {i j k l : T.V} (hkl : ¬ T.inSide s(a, b) k l)
    (hij : T.inSide s(a, b) i j) (hik : ¬ T.inSide s(a, b) k i)
    (h1 : T.sideLeafCount s(a, b) k = 1) :
    (T.attesonW k l s(a, b) : ℝ) - (T.attesonW i j s(a, b) : ℝ) = 0 := by
  rw [T.attesonW_sub_path_eq_far_k hab hkl hij hik, h1]
  push_cast
  ring

/-- ★★★★ **Case D｜两端中间和相加 ⇒ 只看边数**：若 `s` 里每条边都分离 `k,l`
（等价地 `ℓ_k(e) + ℓ_l(e) = n`），则两端的逐边贡献之和恒为 `|s|·(2n − 4)`，
**与 `s` 里究竟是哪些边无关**。

★ 关键是**两端各用自己那侧的 `n − ℓ`**（＝对侧叶数）：`k` 端 `2(n − ℓ_k) − 2 = 2ℓ_l − 2`，
`l` 端 `2(n − ℓ_l) − 2 = 2ℓ_k − 2`，逐边相加 `= 2n − 2(ℓ_k + ℓ_l) + ... = 2n − 4`。
⚠️ 若两端都写 `2ℓ_· − 2`（即都用 `_near_k'` 那一形），逐边和会变成 `4ℓ_l − 4`，**不是常数**。

★ 于是 §7.9.2 的 `A + B = 2(m−2)(n−2)` 退化成一条**基数**事实 `|s| = m − 2`
（路径边去掉首末两条）；这正是 §29 `three_mul_le_of_two_end` 的 `hAB` 的唯一来源。 -/
theorem sum_path_coeff_eq (T : Cladogram X) (s : Finset (Sym2 T.V)) (k l : T.V)
    (hsep : ∀ e ∈ s, T.sideLeafCount e k + T.sideLeafCount e l = Fintype.card X) :
    ∑ e ∈ s, ((2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e k : ℝ)) - 2)
        + (2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e l : ℝ)) - 2))
      = (s.card : ℝ) * (2 * (Fintype.card X : ℝ) - 4) := by
  have hterm : ∀ e ∈ s, ((2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e k : ℝ)) - 2)
      + (2 * ((Fintype.card X : ℝ) - (T.sideLeafCount e l : ℝ)) - 2))
      = 2 * (Fintype.card X : ℝ) - 4 := by
    intro e he
    have h : (T.sideLeafCount e k : ℝ) + (T.sideLeafCount e l : ℝ) = (Fintype.card X : ℝ) := by
      exact_mod_cast hsep e he
    linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

end Cladogram

/-! ## 29. ★★★ W50-A-#19：Case D 的**两端算术**（纯数值，与树结构完全无关）

§7.9.2 的收尾是两行实数算术，本节把它们从几何里**彻底剥离**出来，这样剩下的 Lean 工作
（路径枚举 ⇒ `A`／`B` 两个求和）只要产出 `A + B ≥ 2(m−2)(n−2)` 这一条不等式即可。

记 `m` = `P_{k,l}` 的边数，`A` = `k` 端的中间边系数和、`B` = `l` 端的中间边系数和。则

* `m ≥ 3`（否则 `k,l` 在同一顶点的两条邻边上 ⇒ 樱桃，与 Case D 矛盾）；
* `m ≤ n − 1`（路径上的中间顶点各带一「非叶」…见 `W50_A_MATH.md` §7.9.2 (4)）；
* `A + B = 2(m − 2)(n − 2)`（逐边 `c` 的两端和，用 `ℓ_k + ℓ_l = n`）。

于是 `2(n−4) + A + 2(n−4) + B = 4(n−4) + 2(m−2)(n−2) ≥ 6(n−4)`，故**至少一端**
`≥ 3(n−4)` —— 这就是 `DisjointPairs` 支的 `3(n−4)` 的来源，也是 Atteson 原文
`|L_i(e*)| ≤ |L_k(e*)|`（★D③：原文此处不成立）的**替代品**。 -/

/-- ★★★ **两数之和够大 ⇒ 至少一个够大**（`K/2` 版）。 -/
theorem half_le_of_le_add {a b K : ℝ} (h : K ≤ a + b) : K / 2 ≤ a ∨ K / 2 ≤ b := by
  by_contra hc
  rw [not_or] at hc
  have h1 : a < K / 2 := not_le.mp hc.1
  have h2 : b < K / 2 := not_le.mp hc.2
  linarith

/-- ★★★ **Case D｜核心数值不等式**：`3 ≤ m`、`m + 1 ≤ n` ⇒

　　`6(n − 4) ≤ 2(n − 4) + 2(n − 4) + 2(m − 2)(n − 2)`。

等价于 `n − 4 ≤ (m − 2)(n − 2)`：`m ≥ 3` 给 `m − 2 ≥ 1`，`n ≥ 4` 给 `n − 2 ≥ n − 4`。
（`n = 4`、`m = 3` 时取等：`0 ≤ 0`。） -/
theorem two_end_sum_ge (n m : ℕ) (hm : 3 ≤ m) (hmn : m + 1 ≤ n) :
    6 * ((n : ℝ) - 4)
      ≤ 2 * ((n : ℝ) - 4) + 2 * ((n : ℝ) - 4) + 2 * ((m : ℝ) - 2) * ((n : ℝ) - 2) := by
  have hm' : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
  have hm2 : (1 : ℝ) ≤ (m : ℝ) - 2 := by linarith
  have hm2' : (0 : ℝ) ≤ (m : ℝ) - 2 := by linarith
  nlinarith [mul_le_mul hm2 le_rfl hn2 hm2']

/-- ★★★★ **Case D｜`DisjointPairs` 支的收尾（可直接用于装配）**：

若两端的中间边系数和 `A + B ≥ 2(m−2)(n−2)`（`m` = `P_{k,l}` 的边数，`3 ≤ m ≤ n−1`），
则**至少一端**满足 `2(n−4) + (该端中间和) ≥ 3(n−4)`。

这就是 §7.9.2 全部算术的最终形状：剩下的几何任务只剩「证明 `A + B ≥ 2(m−2)(n−2)`」，
即逐边 `c_{e_r} = 2ℓ_l(e_r) − 2`（`attesonW_sub_path_eq_near_k'`）＋ `ℓ_k + ℓ_l = n`
（`sideLeafCount_add_of_sep`）＋ 两端路径边 `c = 0`（`attesonW_sub_path_eq_zero_of_sideLeafCount_one`）。 -/
theorem three_mul_le_of_two_end {n m : ℕ} (hm : 3 ≤ m) (hmn : m + 1 ≤ n) {A B : ℝ}
    (hAB : 2 * ((m : ℝ) - 2) * ((n : ℝ) - 2) ≤ A + B) :
    3 * ((n : ℝ) - 4) ≤ 2 * ((n : ℝ) - 4) + A ∨
      3 * ((n : ℝ) - 4) ≤ 2 * ((n : ℝ) - 4) + B := by
  have hcore := two_end_sum_ge n m hm hmn
  have h2 := half_le_of_le_add (K := 6 * ((n : ℝ) - 4))
    (a := 2 * ((n : ℝ) - 4) + A) (b := 2 * ((n : ℝ) - 4) + B) (by linarith)
  rcases h2 with h2 | h2
  · left; linarith
  · right; linarith

