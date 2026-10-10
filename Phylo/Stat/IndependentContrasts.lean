/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-!
# `Phylo.Stat.IndependentContrasts` —— 系统发生独立对比（PIC；Felsenstein 1985a）

## 文献（逐行核读）

`references/md/Felsenstein1985a_PhylogeniesComparativeMethod.md`
（J. Felsenstein, *Phylogenies and the Comparative Method*, Amer. Nat. **125**(1):1–15 (1985)，
865 行）。**行号均指该 md 文件。**

⚠️ **区分**：同作者的 bootstrap 文
`references/md/Felsenstein1985_ConfidenceLimitsPhylogeniesBootstrap.md` 是**另一篇**
（已由他人实现），本文件只做**对比量（contrasts）**这一层。

### 文献逐行依据

* `:370–374` —— 「differences between pairs of adjacent tips, such as X1 − X2 and X3 − X4,
  must be independent. This is so because the difference X1 − X2 depends only on events in
  branches 1 and 2, while X3 − X4 depends only on events in branches 3 and 4, and these two
  sets of events are independent.」⇒ **姊妹叶（相邻叶）的对比量彼此独立**；
  注意文献只对**枝集合不相交**的两对叶断言独立。
* `:376–385` —— 布朗运动：每条枝上的增量为独立正态，方差 ∝ 枝长（时间）。
* `:387–391` —— 「the contrast X1 − X2 has expectation zero and variance 2vS²V. Since we
  assume that we know the vi, we can scale the contrast by dividing by its standard
  deviation, obtaining a variate that should have expectation zero and unit variance.」
  ⇒ 对比量方差 = 两条叶枝长之和；**除以标准差 ⇒ 单位方差**。
* `:394–400` —— 更内层的对比量 `(X1 + X2)/2 − (X3 + X4)/2`，方差 `s²(v1 + 2v9)`。
* `:478–494` —— ★★ **算法内核（步 1–4）**：
  「(1) Find two tips on the phylogeny that are adjacent (say nodes i and j) and have a common
  ancestor, say node k. (2) Compute the contrast Xi − Xj. This has expectation zero and variance
  proportional to vi + vj. (3) Remove the two tips from the tree, leaving behind only the ancestor
  k, which now becomes a tip. Assign it the character value `Xk = (Xi/vi + Xj/vj)/(1/vi + 1/vj)`
  (3), the weighted average of Xi and Xj, the weights being proportional to the inverses of the
  variances vi and vj. (4) Lengthen the branch below node k by increasing its length from vk to
  `vk + vi vj/(vi + vj)`.」
* `:496–503` —— 「After one pass through steps 1-4, we have found one contrast and reduced the
  number of tips on the tree by one. … This will extract n − 1 contrasts if there were originally
  n species. … this procedure can be used on a phylogeny of any shape whatsoever.」
* `:402`, `:445–449` —— 8 叶例抽出 7 个（= n − 1）互不相关的对比量。

## 本文件的建模选择（与「缺口」的界线）

文献的概率模型是「树上布朗运动」。本文件**不建概率空间**（超范围），而是把布朗运动的
**二阶结构**直接作为**协方差核** `K : ι → ι → ℝ`（`K i j = Cov(X_i, X_j)`）：

```text
K i j = σ² · (根 → LCA(i,j) 的路径长)      （文献 :387–389）
```

文献 `:387` 把这一等式归为 "it is straightforward to show"（并回引 Felsenstein 1973, 1981b）。
本文件把「核 → 概率空间」这一步登记为**显式缺口**（文末 `IsPositiveSemidefinite` 等），
只证**由核出发的有限代数/组合内容** —— 这正是 PIC 的算法内核。

## 本文件证什么（零 `sorry` / `axiom` / `native_decide`）

* 对比量的**显式构造**：`contrast x i j = x i − x j`（`:480` 步 (2)）；
* 方差结构：`contrastVar_sister`（姊妹叶 `⇒ v_i + v_j`，`:481`）、
  `contrastVar_sister_scaled`（除以标准差 ⇒ 单位方差，`:389–391`, `:499–500`）；
* ★★ 独立性：`contrastCov_eq_zero_of_cross_eq`（跨叶核值相同 ⇒ 不相关，`:371–374`）、
  `contrastCov_disjoint_cherries`（两个分离 cherry ⇒ 不相关）；
* ★★ 归约：`picStep`（步 1–4 一步全给：对比量方差 + 合并值方差 `K k k + vi vj/(vi+vj)`
  + 对比量与合并值**不相关**，`:481–494`）；
* ★B 反例：`contrastCov_nonsister_eq_pendant`（非姊妹对的对比量**不**独立，协方差 = `v_i`）、
  `contrastCov_nonsister_ne_zero`、`contrastVar_root_invariant`（未定根 ⇒ 对比量方差不变）；
* ★C 最小例：`K6`（4 叶 + 2 祖先的具体核）上的数值计算
  （`5/6`、`0`、`1 + 1/5 = 6/5`、`1/2 ≠ 0`）。
-/

namespace Phylo

/-- 性状向量：`x i` 是叶（种）`i` 的表型值 `X_i`（文献 `:370`）。 -/
abbrev Trait (ι : Type*) := ι → ℝ

/-- 协方差核：`K i j = Cov(X_i, X_j) = σ² · (根 → LCA(i,j) 的路径长)`（文献 `:387–389`）。 -/
abbrev Kernel (ι : Type*) := ι → ι → ℝ

section Generic

variable {ι : Type*}

/-! ## 1. 对比量的显式构造（文献 `:480` 步 (1)–(2)） -/

/-- ★ **对比量（显式构造）**：`X_i − X_j`。文献 `:480` 步 (2) 「Compute the contrast Xi − Xj」；
图 8 的例子是 `X1 − X2`（`:371`, `:389`）。 -/
def contrast (x : Trait ι) (i j : ι) : ℝ := x i - x j

@[simp] theorem contrast_apply (x : Trait ι) (i j : ι) : contrast x i j = x i - x j := rfl

/-- 对比量反对称：`X_i − X_j = −(X_j − X_i)`。 -/
theorem contrast_antisymm (x : Trait ι) (i j : ι) : contrast x i j = -contrast x j i := by
  simp [contrast]

/-- 同一个体自比为零。 -/
theorem contrast_self (x : Trait ι) (i : ι) : contrast x i i = 0 := by
  simp [contrast]

/-- ★B（未定根 ⇒ **对比量取值**不变）：给所有叶的性状值同时加常数 `c`
（等价于把根移到别处 / 换一个祖先状态基准），对比量 `X_i − X_j` 不变。 -/
theorem contrast_add_const (x : Trait ι) (i j : ι) (c : ℝ) :
    contrast (fun t => x t + c) i j = contrast x i j := by
  simp [contrast]

/-! ## 2. 方差结构（文献 `:387–391`, `:481`） -/

/-- 对比量 `X_i − X_j` 的**方差**（协方差核的二阶展开）：
`Var(X_i − X_j) = K_ii − K_ij − K_ji + K_jj`。 -/
def contrastVar (K : Kernel ι) (i j : ι) : ℝ := K i i - K i j - K j i + K j j

/-- 两个对比量 `X_i − X_j` 与 `X_p − X_q` 的**协方差**：
`K_ip − K_iq − K_jp + K_jq`。 -/
def contrastCov (K : Kernel ι) (i j p q : ι) : ℝ := K i p - K i q - K j p + K j q

/-- 对比量与自己的协方差就是它的方差（定义层面相同）。 -/
theorem contrastCov_self (K : Kernel ι) (i j : ι) : contrastCov K i j i j = contrastVar K i j := rfl

/-- **姊妹叶的核条件**（布朗运动加性 + 独立增量；文献 `:376–385`, `:480–481`）：
`k` 是 `i,j` 的共同祖先，`vi`（`vj`）是 `i`（`j`）下方叶枝的方差增量，则
`K_ii = K_kk + vi`、`K_jj = K_kk + vj`、`K_ij = K_ji = K_kk`
（即 `X_i = X_k + ε_i`、`X_j = X_k + ε_j`，`ε_i ⊥ ε_j`）。 -/
structure IsCherry (K : Kernel ι) (k i j : ι) (vi vj : ℝ) : Prop where
  hii : K i i = K k k + vi
  hjj : K j j = K k k + vj
  hij : K i j = K k k
  hji : K j i = K k k

/-- ★★ **姊妹叶对比量的方差 = 两叶枝长之和**（文献 `:481`
「This has expectation zero and variance proportional to vi + vj」；`:389` 的
`2vS²V` 是 `vi = vj = v` 的特例）。 -/
theorem contrastVar_sister (K : Kernel ι) {k i j : ι} {vi vj : ℝ}
    (h : IsCherry K k i j vi vj) : contrastVar K i j = vi + vj := by
  obtain ⟨hii, hjj, hij, hji⟩ := h
  simp only [contrastVar, hii, hjj, hij, hji]
  ring

/-- ★ **除以标准差 ⇒ 单位方差**（文献 `:389–391`, `:499–500`）。 -/
theorem contrastVar_sister_scaled (K : Kernel ι) {k i j : ι} {vi vj : ℝ}
    (h : IsCherry K k i j vi vj) (hpos : vi + vj ≠ 0) :
    contrastVar K i j / (vi + vj) = 1 := by
  rw [contrastVar_sister K h]
  field_simp

/-- ★B（未定根 ⇒ **对比量方差**不变）：对比量方差只依赖两条**叶枝** `vi + vj`，
**不含**共同祖先的深度 `K k k`（即与根在哪里无关）。 -/
theorem contrastVar_sister_root_independent (K K' : Kernel ι) {k k' i j : ι} {vi vj : ℝ}
    (h : IsCherry K k i j vi vj) (h' : IsCherry K' k' i j vi vj) :
    contrastVar K i j = contrastVar K' i j := by
  rw [contrastVar_sister K h, contrastVar_sister K' h']

/-- 对称核下，对比量方差写成**路径长**形式 `K_ii + K_jj − 2K_ij`
（= 叶 `i` 到叶 `j` 的路径长，与根的位置无关）。 -/
theorem contrastVar_eq_pathLength (K : Kernel ι) (hK : ∀ a b, K a b = K b a) (i j : ι) :
    contrastVar K i j = K i i + K j j - 2 * K i j := by
  simp only [contrastVar, hK j i]
  ring

/-- ★B（未定根 ⇒ 对比量方差**唯一**）：两棵树（可不同根）若给出相同的成对路径长 `d i j`，
则同一个对比量的方差相同。 -/
theorem contrastVar_root_invariant (K K' : Kernel ι) (hK : ∀ a b, K a b = K b a)
    (hK' : ∀ a b, K' a b = K' b a) (i j : ι)
    (hd : K i i + K j j - 2 * K i j = K' i i + K' j j - 2 * K' i j) :
    contrastVar K i j = contrastVar K' i j := by
  rw [contrastVar_eq_pathLength K hK, contrastVar_eq_pathLength K' hK', hd]

/-! ## 3. ★★ 两两不相关：有限组合事实（文献 `:371–374`） -/

/-- ★★ **核心有限组合事实**：若四对跨叶核值相同（`K_ip = K_iq = K_jp = K_jq = c`），
则两个对比量 `X_i − X_j` 与 `X_p − X_q` **不相关**（四项相消）。
树上的典型情形：`{i,j}` 与 `{p,q}` 分处两个枝集合不相交的 clade，
此时四对共享路径长都等于两个 clade 汇合点的深度（文献 `:371–374`）。 -/
theorem contrastCov_eq_zero_of_cross_eq (K : Kernel ι) {i j p q : ι} {c : ℝ}
    (hip : K i p = c) (hiq : K i q = c) (hjp : K j p = c) (hjq : K j q = c) :
    contrastCov K i j p q = 0 := by
  simp only [contrastCov, hip, hiq, hjp, hjq]
  ring

/-- **两个分离的 cherry**：`{i,j}` 的共同祖先是 `k`，`{p,q}` 的共同祖先是 `l`，
且四对跨叶核值都等于同一个常数 `c`（= 两个 cherry 汇合点的深度）。 -/
structure IsSeparatedCherries (K : Kernel ι) (k l i j p q : ι) (c vi vj vp vq : ℝ) : Prop where
  hc1 : IsCherry K k i j vi vj
  hc2 : IsCherry K l p q vp vq
  cross_ip : K i p = c
  cross_iq : K i q = c
  cross_jp : K j p = c
  cross_jq : K j q = c

/-- ★★ **两个分离 cherry 的对比量不相关**（文献 `:371–374`：`X1 − X2` 与 `X3 − X4` 独立）。 -/
theorem contrastCov_disjoint_cherries (K : Kernel ι) {k l i j p q : ι} {c vi vj vp vq : ℝ}
    (h : IsSeparatedCherries K k l i j p q c vi vj vp vq) :
    contrastCov K i j p q = 0 :=
  contrastCov_eq_zero_of_cross_eq K h.cross_ip h.cross_iq h.cross_jp h.cross_jq

/-! ## 4. ★B 反例检查：并非任意两对叶的对比量都独立 -/

/-- ★B **反例（定量）**：取三叶树 `((i,j),p)`（`k` 是 `i,j` 的共同祖先，`p` 在其外），
则对比量 `X_i − X_j`（姊妹对）与 `X_i − X_p`（**非**姊妹对）的协方差 = **叶枝长 `v_i`**。
故「任意两对叶的对比量都独立」**是假的**：文献 `:371–374` 的独立性只对
**枝集合不相交**的两对叶成立。 -/
theorem contrastCov_nonsister_eq_pendant (K : Kernel ι) {i j p : ι} {D vi c : ℝ}
    (hii : K i i = D + vi) (hji : K j i = D) (hip : K i p = c) (hjp : K j p = c) :
    contrastCov K i j i p = vi := by
  simp only [contrastCov, hii, hip, hji, hjp]
  ring

/-- ★B **反例（非零）**：若叶枝长 `v_i ≠ 0`，则上述协方差**不为零** ⇒ 两个对比量**相关**。 -/
theorem contrastCov_nonsister_ne_zero (K : Kernel ι) {i j p : ι} {D vi c : ℝ}
    (hii : K i i = D + vi) (hji : K j i = D) (hip : K i p = c) (hjp : K j p = c)
    (hvi : vi ≠ 0) : contrastCov K i j i p ≠ 0 := by
  rw [contrastCov_nonsister_eq_pendant K hii hji hip hjp]
  exact hvi

/-! ## 5. ★★ 递归/归约：PIC 的算法内核（文献 `:478–494` 步 1–4） -/

/-- 线性组合 `a X_i + b X_j` 的方差（二阶展开）。 -/
def pairVar (K : Kernel ι) (a b : ℝ) (i j : ι) : ℝ :=
  a ^ 2 * K i i + 2 * a * b * K i j + b ^ 2 * K j j

/-- 线性组合 `a X_i + b X_j` 与 `c X_p + d X_q` 的协方差（双线性展开）。 -/
def pairCov (K : Kernel ι) (a b : ℝ) (i j : ι) (c d : ℝ) (p q : ι) : ℝ :=
  a * c * K i p + a * d * K i q + b * c * K j p + b * d * K j q

/-- 对比量是线性组合 `1 · X_i + (−1) · X_j`（对称核下与 `contrastVar` 一致）。 -/
theorem contrastVar_eq_pairVar (K : Kernel ι) (hK : ∀ a b, K a b = K b a) (i j : ι) :
    contrastVar K i j = pairVar K 1 (-1) i j := by
  simp only [contrastVar, pairVar, hK j i]
  ring

/-- 式 (3)（文献 `:485–486`）中 `X_i` 的权：`w_i = (1/vi)/(1/vi + 1/vj) = vj/(vi + vj)`。 -/
noncomputable def picWeightI (vi vj : ℝ) : ℝ := vj / (vi + vj)

/-- 式 (3) 中 `X_j` 的权：`w_j = vi/(vi + vj)`。 -/
noncomputable def picWeightJ (vi vj : ℝ) : ℝ := vi / (vi + vj)

/-- ★ **式 (3)（文献 `:485–486`）**：共同祖先 `k` 的（估计）性状值
`X_k = (v_j X_i + v_i X_j)/(v_i + v_j)`（按方差的**逆**加权）。 -/
noncomputable def picMergeValue (xi xj vi vj : ℝ) : ℝ := (vj * xi + vi * xj) / (vi + vj)

/-- `picMergeValue` 就是式 (3) 的加权平均写法。 -/
theorem picMergeValue_eq_weighted (xi xj vi vj : ℝ) :
    picMergeValue xi xj vi vj = picWeightI vi vj * xi + picWeightJ vi vj * xj := by
  simp only [picMergeValue, picWeightI, picWeightJ]
  ring

/-- 两个权之和为 1（真正的加权平均）。 -/
theorem picWeight_sum (vi vj : ℝ) (h : vi + vj ≠ 0) :
    picWeightI vi vj + picWeightJ vi vj = 1 := by
  simp only [picWeightI, picWeightJ]
  field_simp
  ring

/-- 步 (4)（文献 `:489–494`）：`k` 下方枝长由 `v_k` 加长为 `v_k + v_i v_j/(v_i + v_j)`。 -/
noncomputable def picMergedLength (vk vi vj : ℝ) : ℝ := vk + vi * vj / (vi + vj)

/-- ★★ **步 (3) 的估计误差 = 步 (4) 的枝长增量**（文献 `:489–494`）：
合并值 `X_k`（式 (3)）的方差 = `K_kk + v_i v_j/(v_i + v_j)`
——「the weighted average … does not compute the phenotype of the ancestor but only estimates
it, and does so with an error that is statistically indistinguishable from an extra burst of
evolution after node k」，这正是枝长加长量的来源。 -/
theorem picMergeValue_var (K : Kernel ι) {k i j : ι} {vi vj : ℝ}
    (h : IsCherry K k i j vi vj) (hne : vi + vj ≠ 0) :
    pairVar K (picWeightI vi vj) (picWeightJ vi vj) i j
      = picMergedLength (K k k) vi vj := by
  obtain ⟨hii, hjj, hij, hji⟩ := h
  simp only [pairVar, picMergedLength, picWeightI, picWeightJ, hii, hjj, hij]
  field_simp
  ring

/-- ★★ **归约的不变量**：本次取出的对比量 `X_i − X_j` 与合并出的新叶值 `X_k`（式 (3)）
**不相关**（协方差 `w_i v_i − w_j v_j = 0`）。这是「重复步 1–4 后剩下的对比量仍然彼此独立」
（文献 `:496–503`）的归纳步。 -/
theorem contrast_uncorrelated_picMerge (K : Kernel ι) {k i j : ι} {vi vj : ℝ}
    (h : IsCherry K k i j vi vj) :
    pairCov K 1 (-1) i j (picWeightI vi vj) (picWeightJ vi vj) i j = 0 := by
  obtain ⟨hii, hjj, hij, hji⟩ := h
  simp only [pairCov, picWeightI, picWeightJ, hii, hjj, hij, hji]
  ring

/-- ★★ **PIC 一步（文献 `:478–494` 步 1–4）**：给定姊妹叶 `i,j`（共同祖先 `k`，叶枝长 `vi,vj`），
一步同时给出三件事：
(1) 对比量 `X_i − X_j` 的方差 = `vi + vj`（步 (2)）；
(2) 合并值 `X_k`（式 (3)）的方差 = `K_kk + vi vj/(vi + vj)`（步 (3) + 步 (4) 的枝长加长）；
(3) 对比量与合并值不相关（⇒ 归约后剩下的对比量仍彼此独立）。 -/
theorem picStep (K : Kernel ι) {k i j : ι} {vi vj : ℝ} (h : IsCherry K k i j vi vj)
    (hne : vi + vj ≠ 0) :
    contrastVar K i j = vi + vj ∧
      pairVar K (picWeightI vi vj) (picWeightJ vi vj) i j
        = picMergedLength (K k k) vi vj ∧
      pairCov K 1 (-1) i j (picWeightI vi vj) (picWeightJ vi vj) i j = 0 :=
  ⟨contrastVar_sister K h, picMergeValue_var K h hne, contrast_uncorrelated_picMerge K h⟩

end Generic

/-! ## 6. ★C 最小例（具体数值核）

`K6` 是「4 叶 + 2 个祖先」的具体核（下标 0,1 = 第一个 cherry 的两叶；2,3 = 第二个 cherry
的两叶；4 = 第一个 cherry 的祖先 `k`；5 = 第二个 cherry 的祖先 `l`）：

```text
K6 Dk Dl r vi vj vp vq =
  !![Dk+vi, Dk   , r    , r    , Dk, r ;
     Dk   , Dk+vj, r    , r    , Dk, r ;
     r    , r    , Dl+vp, Dl   , r , Dl;
     r    , r    , Dl   , Dl+vq, r , Dl;
     Dk   , Dk   , r    , r    , Dk, r ;
     r    , r    , Dl   , Dl   , r , Dl]
```

`r` 是两个 cherry 汇合点的深度（跨 cherry 共享路径长）。 -/

/-- 具体 6 元核（4 叶 + 2 祖先），见上方注释。 -/
def K6 (Dk Dl r vi vj vp vq : ℝ) : Kernel (Fin 6) :=
  ![![Dk + vi, Dk, r, r, Dk, r],
    ![Dk, Dk + vj, r, r, Dk, r],
    ![r, r, Dl + vp, Dl, r, Dl],
    ![r, r, Dl, Dl + vq, r, Dl],
    ![Dk, Dk, r, r, Dk, r],
    ![r, r, Dl, Dl, r, Dl]]

/-- `K6` 中 `(0,1)` 是姊妹对，共同祖先 `4`，叶枝长 `vi,vj`。 -/
theorem K6_isCherry (Dk Dl r vi vj vp vq : ℝ) :
    IsCherry (K6 Dk Dl r vi vj vp vq) 4 0 1 vi vj where
  hii := by simp [K6]
  hjj := by simp [K6]
  hij := by simp [K6]
  hji := by simp [K6]

/-- `K6` 中 `(2,3)` 是姊妹对，共同祖先 `5`，叶枝长 `vp,vq`。 -/
theorem K6_isCherry' (Dk Dl r vi vj vp vq : ℝ) :
    IsCherry (K6 Dk Dl r vi vj vp vq) 5 2 3 vp vq where
  hii := by simp [K6]
  hjj := by simp [K6]
  hij := by simp [K6]
  hji := by simp [K6]

/-- `K6` 的两个 cherry 分离（跨叶核值都等于 `r`）。 -/
theorem K6_isSeparatedCherries (Dk Dl r vi vj vp vq : ℝ) :
    IsSeparatedCherries (K6 Dk Dl r vi vj vp vq) 4 5 0 1 2 3 r vi vj vp vq where
  hc1 := K6_isCherry Dk Dl r vi vj vp vq
  hc2 := K6_isCherry' Dk Dl r vi vj vp vq
  cross_ip := by simp [K6]
  cross_iq := by simp [K6]
  cross_jp := by simp [K6]
  cross_jq := by simp [K6]

/-- ★C：`Var(X0 − X1) = vi + vj`（`K6` 上的具体计算）。 -/
theorem K6_contrastVar (Dk Dl r vi vj vp vq : ℝ) :
    contrastVar (K6 Dk Dl r vi vj vp vq) 0 1 = vi + vj :=
  contrastVar_sister _ (K6_isCherry Dk Dl r vi vj vp vq)

/-- ★C：两个分离 cherry 的对比量不相关（`K6` 上的具体计算）。 -/
theorem K6_contrastCov_disjoint (Dk Dl r vi vj vp vq : ℝ) :
    contrastCov (K6 Dk Dl r vi vj vp vq) 0 1 2 3 = 0 :=
  contrastCov_disjoint_cherries _ (K6_isSeparatedCherries Dk Dl r vi vj vp vq)

/-! ### 6.1 ★C 具体数值（`Dk = Dl = 1`, `r = 0`, `vi = 1/2`, `vj = 1/3`, `vp = vq = 1`） -/

/-- ★C **数值最小例**：`Var(X0 − X1) = 1/2 + 1/3 = 5/6`。 -/
theorem K6num_contrastVar :
    contrastVar (K6 1 1 0 (1 / 2) (1 / 3) 1 1) 0 1 = 5 / 6 := by
  norm_num [K6_contrastVar 1 1 0 (1 / 2) (1 / 3) 1 1]

/-- ★C **数值最小例**：`Var(X0 − X1)/(5/6) = 1`（**单位方差**，文献 `:389–391`）。 -/
theorem K6num_contrastVar_unit :
    contrastVar (K6 1 1 0 (1 / 2) (1 / 3) 1 1) 0 1 / (5 / 6) = 1 := by
  norm_num [K6num_contrastVar]

/-- ★C **数值最小例**：两个分离 cherry 的协方差 = 0。 -/
theorem K6num_contrastCov_disjoint :
    contrastCov (K6 1 1 0 (1 / 2) (1 / 3) 1 1) 0 1 2 3 = 0 :=
  K6_contrastCov_disjoint 1 1 0 (1 / 2) (1 / 3) 1 1

/-- ★C **数值最小例（步 (4)）**：`v_i v_j/(v_i + v_j) = (1/2)(1/3)/(5/6) = 1/5`，
故合并值的方差 = `1 + 1/5 = 6/5` —— 与「枝长加长量」一致。 -/
theorem K6num_mergeVar :
    pairVar (K6 1 1 0 (1 / 2) (1 / 3) 1 1)
      (picWeightI (1 / 2) (1 / 3)) (picWeightJ (1 / 2) (1 / 3)) 0 1 = 6 / 5 := by
  rw [picMergeValue_var (K6 1 1 0 (1 / 2) (1 / 3) 1 1)
    (K6_isCherry 1 1 0 (1 / 2) (1 / 3) 1 1) (by norm_num)]
  simp only [picMergedLength, K6]
  norm_num

/-- ★C **数值最小例（枝长加长量）**：`picMergedLength 1 (1/2) (1/3) = 6/5`。 -/
theorem K6num_mergedLength : picMergedLength 1 (1 / 2) (1 / 3) = 6 / 5 := by
  norm_num [picMergedLength]

/-- ★B **数值反例**：非姊妹对的对比量 `X0 − X1` 与 `X0 − X2` 的协方差 = `v_i = 1/2`
（`K_00 = Dk + vi`、`K_10 = Dk`、`K_02 = K_12 = r = 0`）。 -/
theorem K6num_nonsister_eq :
    contrastCov (K6 1 1 0 (1 / 2) (1 / 3) 1 1) 0 1 0 2 = 1 / 2 := by
  rw [contrastCov_nonsister_eq_pendant (K6 1 1 0 (1 / 2) (1 / 3) 1 1)
    (D := 1) (vi := 1 / 2) (c := 0)
    (by simp [K6]) (by simp [K6]) (by simp [K6]) (by simp [K6])]

/-- ★B **数值反例（非零）**：`1/2 ≠ 0` ⇒ 「任意两对叶的对比量都独立」为**假**。 -/
theorem K6num_nonsister_ne_zero :
    contrastCov (K6 1 1 0 (1 / 2) (1 / 3) 1 1) 0 1 0 2 ≠ 0 := by
  rw [K6num_nonsister_eq]
  norm_num

/-- **反空真**：`IsCherry` 的假设集**可满足**（`K6` 是一例）⇒ 上面的定理不是空真。 -/
theorem isCherry_nonempty :
    ∃ (K : Kernel (Fin 6)) (k i j : Fin 6) (vi vj : ℝ), IsCherry K k i j vi vj :=
  ⟨K6 1 1 0 (1 / 2) (1 / 3) 1 1, (4 : Fin 6), (0 : Fin 6), (1 : Fin 6), (1 / 2 : ℝ),
    (1 / 3 : ℝ), K6_isCherry 1 1 0 (1 / 2) (1 / 3) 1 1⟩

/-- **反空真**：`IsSeparatedCherries` 的假设集**可满足**。 -/
theorem isSeparatedCherries_nonempty :
    ∃ (K : Kernel (Fin 6)) (k l i j p q : Fin 6) (c vi vj vp vq : ℝ),
      IsSeparatedCherries K k l i j p q c vi vj vp vq :=
  ⟨K6 1 1 0 (1 / 2) (1 / 3) 1 1, (4 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6),
    (2 : Fin 6), (3 : Fin 6), (0 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ), (1 : ℝ), (1 : ℝ),
    K6_isSeparatedCherries 1 1 0 (1 / 2) (1 / 3) 1 1⟩

/-- **反空真**：存在**方差非零**的对比量 `X0 − X1` 与**和它不相关**的对比量 `X2 − X3`。 -/
theorem contrastCov_disjoint_witness :
    ∃ (K : Kernel (Fin 6)) (i j p q : Fin 6),
      contrastVar K i j ≠ 0 ∧ contrastCov K i j p q = 0 :=
  ⟨K6 1 1 0 (1 / 2) (1 / 3) 1 1, (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (3 : Fin 6),
    (by rw [K6_contrastVar 1 1 0 (1 / 2) (1 / 3) 1 1]; norm_num),
    K6_contrastCov_disjoint 1 1 0 (1 / 2) (1 / 3) 1 1⟩

/-! ## 7. ★ 未证项：显式缺口（**不硬编**，登记为 `def … : Prop`） -/

section Gaps

variable {ι : Type*}

/-- ⊘ **缺口 1（概率桥 / 正半定）**：本文件的核 `K` 必须来自真正的概率模型
（树上布朗运动）。其**可检验的数学后果**是正半定性 ⇒ 一切线性组合的方差 ≥ 0。
文献 `:376–389` 只以 "it is straightforward to show" 带过（并回引 Felsenstein 1973, 1981b），
本文件**不建概率空间**（超范围）⇒ 只登记谓词，不证。 -/
def IsPositiveSemidefinite (K : Kernel ι) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ι) (a : Fin n → ℝ), 0 ≤ ∑ p, ∑ q, a p * a q * K (c p) (c q)

/-- ⊘ **缺口 2（任意树的归纳）**：`n` 叶树逐次归约（步 1–4）抽出的 `n − 1` 个对比量
**两两不相关**（文献 `:402`, `:445–449`, `:496–503`）。本文件已证**单步**内核
（`picStep`）与**两个 cherry** 情形（`contrastCov_disjoint_cherries`），
但把它沿归约序列归纳到任意树形，需要对「有根带权树 + 归约序列」做结构归纳，
本文件未引入该数据结构 ⇒ 登记谓词，不证。 -/
def AllExtractedContrastsUncorrelated (K : Kernel ι) (cs : List (ι × ι)) : Prop :=
  cs.Pairwise (fun c c' => contrastCov K c.1 c.2 c'.1 c'.2 = 0)

/-- ⊘ **缺口 3（对比量计数 = n − 1）**：文献 `:498`
「This will extract n − 1 contrasts if there were originally n species」。
需「`n` 叶有根二叉树的内部节点数 = `n − 1`」以及归约序列长度的归纳，
本文件只做单步代数内核 ⇒ 登记谓词，不证。 -/
def ReductionLengthIsLeafMinusOne (steps : List (ι × ι × ι)) (n : ℕ) : Prop :=
  steps.length = n - 1

end Gaps

end Phylo
