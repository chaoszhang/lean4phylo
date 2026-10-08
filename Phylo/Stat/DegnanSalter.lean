/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent

/-!
# `Phylo.Stat.DegnanSalter` —— Degnan & Salter (2005) 式 (1)：`p_{uv}(T)`

本文件形式化 **Degnan & Salter (2005)** 的 `p_{uv}(T)`：一条枝上 `u` 条谱系
在时间 `T` 内并成 `v` 条的概率。这是那篇论文里「一切基因树概率的母机」，
式 (2) 的每一个因子都是它。

## 文献与原文形状

出处：J. H. Degnan & L. A. Salter, *Gene tree distributions under the coalescent
process*, **Evolution 59(1):24-36 (2005)**，
`references/pdf/DegnanSalter2005_GeneTreeDistributions.pdf` **第 2 页**
（期刊页码 **25**）。

> ⚠️ **`references/md/DegnanSalter2005_GeneTreeDistributions.md` 里的式 (1) 不可判读。**
> 该 md 把公式里的 `−` 映射成了 `(cid:53)` / `5`、`∑` 映射成了 `O`、
> `≥` 映射成了 `(cid:36)`，并且错位了上下标。这不是误读：同一份 md
> 第 393–421 行给出的那条「式 (1)」在数值上根本不满足 `Σ_v p_{uv}(T) = 1`。
> 本文件用的是 `pdftotext -layout -enc UTF-8` 的**重新提取**结果。

重新提取后的式 (1)（`u ≥ v ≥ 1`，`T` 以 `2N` 世代为单位，`λ_k = k(k−1)/2`）：

```text
                    u                                             prod_{y=0}^{k-2} (v-1+y)(u+1-y)
  p_{uv}(T) =  sum      (2k-1)(-1)^{k-v} e^{-k(k-1)T/2}  ----------------------------------------
                                            v!(k-v)!(v+k-1)!        prod_{y=0}^{k-2} (u+y)
             k=v
```

原文紧前的两个口径（第 2 页；md 第 384–386 行）：

> `Here u ≥ v ≥ 1, and if u = v, then p_{uv}(T) is the probability that no`
> `coalescences occur in the length of time T.`
> `In the coalescent model, T = t/(2N), where t is the number of generations and N`
> `is the effective population size.`

「所有 ordering 等概率」的模型口径在第 **5 页**（md 第 **3219–3224** 行）：

> `Assuming that all possible orderings, correct and incorrect, are equally likely`
> `(this follows the model of Yule [1924]), and that u lineages have coalesced into`
> `v lineages, the probability that the ordering of events on the branch is`
> `consistent with the gene tree is the number of correct orderings divided by the`
> `number of possible orderings.`

同一句也在 md 第 **3805–3808** 行。概率质量函数全文在 md 第 **4269 行**起
（`THE PROBABILITY MASS FUNCTION P_{c,l}(G = g)`）。Degnan–Salter 把式 (1) 归给
Rosenberg (2002)，并说明更早由 Tavaré (1984)、Watterson (1984)、
Takahata & Nei (1985) 得到（第 2 页）。

## 本文件形式化的定义

`T` 用 coalescent units，`λ_k = k(k−1)/2`。Kingman 纯死亡链的生成元
`Q`（`Q[k,k] = −λ_k`、`Q[k,k−1] = λ_k`）在 `{1,…,u}` 上是上三角、特征值
`−λ_1,…,−λ_u` 互异，故 `(sI − Q)⁻¹[u][v]` 的**部分分式**给出

```text
  p_{uv}(T) = Σ_{k=v}^{u}  c(u,v,k) · e^{-λ_k T},
  c(u,v,k) = (Π_{m=v+1}^{u} λ_m) / (Π_{m=v, m≠k}^{u} (λ_m − λ_k))
```

这正是式 (1) 的**闭合形式**，等价地写成（脚本 `(C0)` 逐项核对）

```text
  c(u,v,k) = (2k−1)(−1)^{k−v} u!(u−1)!(v+k−2)! / (v!(v−1)!(k−v)!(u−k)!(u+k−1)!)
           = (2k−1)(−1)^{k−v} [Π_{y=0}^{k−2}(v+y)] [Π_{y=0}^{k−1}(u−y)/(u+y)] / (v!(k−v)!)
```

`scripts/msc/degnansalter_puv.py` 用**精确有理数**穷举复核（`u ≤ 9`）：
`(C0)` 两种形状一致；`(C0b)` `u = 2,3,4` 与教科书 Kingman 结果逐项一致；
`(C1)` 与**独立的 Sylvester 公式** `P_k = Π_{i≠k}(Q+λ_i I)/(λ_i−λ_k)`
（并验证 `Σ_k P_k = I`）逐项一致；`(C2)` `p_uu = e^{−λ_u T}`；
`(C3)` `p_{uv}(0) = δ_{uv}`；`(C4)/(C5)` `u ≤ 6` 上非负、`Σ_v p_{uv}(T) = 1`
（300 位 Decimal）；`(C6)` `p_21 = 1 − e^{−T}`、`p_22 = e^{−T}`；
`(C7)` ODE/特征关系 `Σ_w Q[u][w] c(w,v,k) = −λ_k c(u,v,k)`。**没有用 Monte Carlo。**

⚠️ **措辞纪律**：`(C4)/(C5)/(C7)` 等是**脚本**的复核结果，**不是** Lean 定理；
Lean 内只证了下面「诚实边界」表里标 ✅ 的那一栏。

## 接合点（与库内既有溯祖设施）

* `pUV 2 1 t = Coalescent.firstMergeCDF 2 t`（`= 1 − e^{−t}`）；
* `pUV 2 2 t = Coalescent.survival 2 t`（`= e^{−t}`）；
* `1 ≤ u` 时 `pUV u u t = Coalescent.survival u t`；
* `λ_k = Coalescent.kingmanRate k`（同一个数）。

## 诚实边界（逐条，**没做到的**）

| 条目 | Lean 内状态 |
|---|---|
| `pUV` 的准确定义（部分分式/谱分解） | ✅ `pUV`、`pUVCoeff` |
| `pUV u 0 t = 0` | ✅ `pUV_zero_right` |
| `pUV u v t = 0`（`v > u`） | ✅ `pUV_eq_zero_of_gt` |
| `pUV 1 1 t = 1` | ✅ `pUV_one_one` |
| `pUV 2 2 t = Coalescent.survival 2 t` | ✅ `pUV_two_two` |
| `pUV 2 1 t = Coalescent.firstMergeCDF 2 t` | ✅ `pUV_two_one` |
| `1 ≤ u` 时 `pUV u u t = Coalescent.survival u t` | ✅ `pUV_diag` |
| 归一化的**有限情形** `pUV 2 1 t + pUV 2 2 t = 1` | ✅ `pUV_normalization_two` |
| `λ_k = Coalescent.kingmanRate k` | ✅ `lambdaR_eq_kingmanRate` |
| 归一化一般情形 `Σ_{v=1}^{u} pUV u v t = 1`（`u ≥ 3`） | ❌ 缺口 `pUV_normalization` |
| `pUV u v t ≥ 0`（一般 `u,v`） | ❌ 缺口 `pUV_nonneg` |
| `pUV u v 0 = if u = v then 1 else 0` | ❌ 缺口 `pUV_zero_time` |
| 与式 (1)**产品形式**的逐项一致性（Lean 内） | ❌ 缺口 `pUV_eq_formula1` |

### 归一化一般情形缺什么（明确报告）

`Σ_{v=1}^{u} pUV u v t = 1`（`u ≥ 3`）在脚本里已按精确有理数验证
（`(C3)` 先验 `Σ_k c = δ_{vu}`，`(C5)` 再验 `Σ_v p_{uv}(T) = 1`）；
Lean 内未证。缺的是那条**系数恒等式**

```text
  ∀ u k, 1 ≤ k → k ≤ u → Σ_{v=1}^{k} c(u,v,k) = if k = u then 1 else 0
```

即 `Q` 的特征投影算子 `P_k` 沿行求和为 `δ_{ku}`（`Σ_k P_k = I` 的一行）。
把它变成 Lean 定理需要有限线性代数的归纳（或部分分式恒等式的展开），
本批**未做**。本文件**不声称**一般归一化已被证明。
-/

namespace Phylo.Stat.DegnanSalter

/-! ## 基础量 -/

/-- **Kingman 合并率** `λ_k = k(k−1)/2`，以 `ℝ` 表示。

与库内 `Coalescent.kingmanRate` 是同一个数（`lambdaR_eq_kingmanRate`）。 -/
noncomputable def lambdaR (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) - 1) / 2

@[simp] theorem lambdaR_zero : lambdaR 0 = 0 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_one : lambdaR 1 = 0 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_two : lambdaR 2 = 1 := by rw [lambdaR]; norm_num

@[simp] theorem lambdaR_three : lambdaR 3 = 3 := by rw [lambdaR]; norm_num

/-- `λ_k = Coalescent.kingmanRate k`（同一个数，定义相同）。 -/
theorem lambdaR_eq_kingmanRate (k : ℕ) : lambdaR k = Coalescent.kingmanRate k := rfl

/-- `k ≥ 2` 时 `λ_k > 0`。 -/
theorem lambdaR_pos {k : ℕ} (hk : 2 ≤ k) : 0 < lambdaR k := by
  rw [lambdaR_eq_kingmanRate]
  exact Coalescent.kingmanRate_pos hk

/-! ## 式 (1) 的系数与 `p_{uv}(T)` -/

/-- **式 (1) 的系数** `c(u,v,k)`：`p_uv(T)` 里 `e^{−λ_k T}` 的系数。

即 `(sI − Q)⁻¹[u][v]` 的部分分式系数
`(Π_{m=v+1}^{u} λ_m) / (Π_{m=v, m≠k}^{u} (λ_m − λ_k))`。
因子 `(if v = 0 then 0 else 1)` 处理 `v = 0`（不在式 (1) 的范围内：
那时分母里的 `λ_1 − λ_0` 会变成 `0`）。 -/
noncomputable def pUVCoeff (u v k : ℕ) : ℝ :=
  (if v = 0 then 0 else 1)
    * ((∏ m ∈ Finset.Icc (v + 1) u, lambdaR m)
        / ∏ m ∈ (Finset.Icc v u).erase k, (lambdaR m - lambdaR k))

/-- **Degnan–Salter (2005) 式 (1) 的 `p_{uv}(T)`**（谱分解 / 部分分式形式）。

`pUV u v t = Σ_{k=v}^{u} e^{−λ_k t} · c(u,v,k)`；`v = 0` 时系数全为 `0`，
故 `pUV u 0 t = 0`（`v = 0` 不在式 (1) 的范围内）。

原文：`references/pdf/DegnanSalter2005_GeneTreeDistributions.pdf` 第 2 页
（期刊页码 25）；`u ≥ v ≥ 1`，`u = v` 时它是「`T` 内不发生任何合并」的概率。 -/
noncomputable def pUV (u v : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc v u, Real.exp (-(lambdaR k) * t) * pUVCoeff u v k

/-- `pUV u 0 t = 0`（`v = 0` 不是式 (1) 的取值）。 -/
@[simp] theorem pUV_zero_right (u : ℕ) (t : ℝ) : pUV u 0 t = 0 := by
  rw [pUV]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [pUVCoeff]

/-- `v > u` 时 `pUV u v t = 0`（式 (1) 只在 `k ≥ v` 上求和，而 `k ≤ u`）。 -/
theorem pUV_eq_zero_of_gt {u v : ℕ} (h : u < v) (t : ℝ) : pUV u v t = 0 := by
  rw [pUV, Finset.Icc_eq_empty_of_lt h, Finset.sum_empty]

/-! ## 具体系数的求值 -/

/-- `(Icc a a).erase a = ∅`。 -/
theorem erase_Icc_self (a : ℕ) : (Finset.Icc a a).erase a = (∅ : Finset ℕ) := by
  rw [Finset.Icc_self]
  simp

/-- `Icc 1 2 = {1,2}`。 -/
theorem Icc_one_two : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega

/-- `c(1,1,1) = 1`。 -/
theorem pUVCoeff_one_one_one : pUVCoeff 1 1 1 = 1 := by
  have h1 : Finset.Icc 2 1 = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) < 2)
  have h2 : (Finset.Icc 1 1).erase 1 = (∅ : Finset ℕ) := erase_Icc_self 1
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,2,2) = 1`。 -/
theorem pUVCoeff_two_two_two : pUVCoeff 2 2 2 = 1 := by
  have h1 : Finset.Icc 3 2 = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty_of_lt (by norm_num : (2 : ℕ) < 3)
  have h2 : (Finset.Icc 2 2).erase 2 = (∅ : Finset ℕ) := erase_Icc_self 2
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,1,1) = 1`。 -/
theorem pUVCoeff_two_one_one : pUVCoeff 2 1 1 = 1 := by
  have h1 : Finset.Icc 2 2 = ({2} : Finset ℕ) := Finset.Icc_self 2
  have h2 : (Finset.Icc 1 2).erase 1 = ({2} : Finset ℕ) := by
    rw [Icc_one_two]; decide
  rw [pUVCoeff, h1, h2]
  simp

/-- `c(2,1,2) = −1`。 -/
theorem pUVCoeff_two_one_two : pUVCoeff 2 1 2 = -1 := by
  have h1 : Finset.Icc 2 2 = ({2} : Finset ℕ) := Finset.Icc_self 2
  have h2 : (Finset.Icc 1 2).erase 2 = ({1} : Finset ℕ) := by
    rw [Icc_one_two]; decide
  rw [pUVCoeff, h1, h2]
  simp

/-! ## 接合点（与库内既有溯祖设施） -/

/-- `pUV 1 1 t = 1`（单条谱系；`λ_1 = 0`）。 -/
theorem pUV_one_one (t : ℝ) : pUV 1 1 t = 1 := by
  rw [pUV, show Finset.Icc 1 1 = ({1} : Finset ℕ) from Finset.Icc_self 1,
    Finset.sum_singleton, pUVCoeff_one_one_one, lambdaR_one]
  simp

/-- ★★★ **`u = 2, v = 2`**：`pUV 2 2 t = Coalescent.survival 2 t = e^{−t}`。

即「两条谱系在 `t` 内不合并」的概率 —— 正是 Degnan–Salter 的 `u = v` 口径。 -/
theorem pUV_two_two (t : ℝ) : pUV 2 2 t = Coalescent.survival 2 t := by
  rw [pUV, show Finset.Icc 2 2 = ({2} : Finset ℕ) from Finset.Icc_self 2,
    Finset.sum_singleton, pUVCoeff_two_two_two, lambdaR_two, Coalescent.survival_two]
  ring_nf

/-- ★★★ **`u = 2, v = 1`**：`pUV 2 1 t = Coalescent.firstMergeCDF 2 t = 1 − e^{−t}`。

即 `u = 2` 情形**就是**库内已有的 `Coalescent.firstMergeCDF`（`u` 条谱系中
首次合并的分布函数）。 -/
theorem pUV_two_one (t : ℝ) : pUV 2 1 t = Coalescent.firstMergeCDF 2 t := by
  rw [pUV, Icc_one_two, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
    pUVCoeff_two_one_one, pUVCoeff_two_one_two, lambdaR_one, lambdaR_two,
    Coalescent.firstMergeCDF_two]
  ring_nf
  rw [Real.exp_zero]

/-- ★★ **一般对角**（`1 ≤ u`）：`pUV u u t = Coalescent.survival u t`
（式 (1) 的 `u = v` 口径：「`t` 内不发生任何合并」的概率 `e^{−λ_u t}`）。 -/
theorem pUV_diag {u : ℕ} (hu : 1 ≤ u) (t : ℝ) : pUV u u t = Coalescent.survival u t := by
  have hv : u ≠ 0 := by omega
  have hcoef : pUVCoeff u u u = 1 := by
    have h1 : Finset.Icc (u + 1) u = (∅ : Finset ℕ) :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self u)
    have h2 : (Finset.Icc u u).erase u = (∅ : Finset ℕ) := erase_Icc_self u
    rw [pUVCoeff, h1, h2]
    simp [hv]
  rw [pUV, show Finset.Icc u u = ({u} : Finset ℕ) from Finset.Icc_self u,
    Finset.sum_singleton, hcoef, mul_one, Coalescent.survival, lambdaR_eq_kingmanRate]

/-- ★★ **归一化的有限情形**：`pUV 2 1 t + pUV 2 2 t = 1`
（链在 `u = 2` 时只有两个状态，两条接合点直接给出归一化）。 -/
theorem pUV_normalization_two (t : ℝ) : pUV 2 1 t + pUV 2 2 t = 1 := by
  rw [pUV_two_one, pUV_two_two, Coalescent.firstMergeCDF_two, Coalescent.survival_two]
  ring

/-- `pUV 2 1 t` 的显式值：`1 − e^{−t}`。 -/
theorem pUV_two_one_eq (t : ℝ) : pUV 2 1 t = 1 - Real.exp (-t) := by
  rw [pUV_two_one, Coalescent.firstMergeCDF_two]

/-- `pUV 2 2 t` 的显式值：`e^{−t}`。 -/
theorem pUV_two_two_eq (t : ℝ) : pUV 2 2 t = Real.exp (-t) := by
  rw [pUV_two_two, Coalescent.survival_two]

/-- 一般对角的显式值（`1 ≤ u`）：`pUV u u t = e^{−λ_u t}`。 -/
theorem pUV_diag_eq {u : ℕ} (hu : 1 ≤ u) (t : ℝ) :
    pUV u u t = Real.exp (-(lambdaR u) * t) := by
  rw [pUV_diag hu, Coalescent.survival, ← lambdaR_eq_kingmanRate u]

/-! ## 诚实边界：显式缺口（`def … : Prop`，**未证**） -/

/-- ❌ **缺口**：一般归一化 `Σ_{v=1}^{u} pUV u v t = 1`（`u ≥ 3`）。

缺的是系数恒等式 `∀ u k, 1 ≤ k → k ≤ u →
Σ_{v=1}^{k} c(u,v,k) = if k = u then 1 else 0`（即 `Σ_k P_k = I` 的一行）。
脚本 `(C3)`/`(C5)` 在 `u ≤ 9`、多组 `t` 上用精确有理数验证。**未证。** -/
def pUV_normalization : Prop :=
  ∀ (u : ℕ) (t : ℝ), 3 ≤ u → ∑ v ∈ Finset.Icc 1 u, pUV u v t = 1

/-- ❌ **缺口**：`pUV u v t ≥ 0`（`1 ≤ v ≤ u`、`t ≥ 0`）。

`pUV` 是「系数 × 指数」的**交错和**，逐项非负并不显然；正确的论证要用
`p_{uv}` 作为纯死亡过程的转移概率。脚本 `(C4)` 在 `u ≤ 6` 上数值验证。**未证。** -/
def pUV_nonneg : Prop := ∀ (u v : ℕ) (t : ℝ), 1 ≤ v → v ≤ u → 0 ≤ t → 0 ≤ pUV u v t

/-- ❌ **缺口**：`pUV u v 0 = if u = v then 1 else 0`（即 `exp(0·Q) = I`）。

等价于「系数沿 `k` 求和为 `δ_{v,u}`」，与 `pUV_normalization` 同源。**未证。** -/
def pUV_zero_time : Prop :=
  ∀ u v : ℕ, 1 ≤ v → v ≤ u → pUV u v 0 = if u = v then 1 else 0

/-- ❌ **缺口**：`pUV` 的系数与式 (1) **产品形式**的逐项一致性

```text
  c(u,v,k) = (2k−1)(−1)^{k−v} [Π_{y=0}^{k−2}(v+y)] [Π_{y=0}^{k−1}(u−y)/(u+y)] / (v!(k−v)!)
```

（右边就是重新提取的式 (1) 中 `e^{−λ_k T}` 的系数；见文件头。）
脚本 `(C0)`/`(C0c)` 在 `u ≤ 9` 上精确核对；Lean 内未证。**未证。** -/
def pUV_eq_formula1 : Prop :=
  ∀ (u v k : ℕ), 1 ≤ v → v ≤ k → k ≤ u →
    pUVCoeff u v k
      = (2 * (k : ℝ) - 1) * (-1 : ℝ) ^ (k - v)
          * (∏ y ∈ Finset.range (k - 1), ((v : ℝ) + y))
          * (∏ y ∈ Finset.range k, (((u : ℝ) - y) / ((u : ℝ) + y)))
          / ((v.factorial : ℝ) * (((k - v).factorial : ℝ)))

end Phylo.Stat.DegnanSalter
