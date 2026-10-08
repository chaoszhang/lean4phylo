/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERWeights
import Phylo.JukesCantor
import Mathlib.Tactic

/-!
# `Phylo.CASTERJC69` —— CASTER 附录 **命题 A（JC69 情形）** 的形式化

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688,
"Direct species tree inference from whole-genome alignments"，
附录 `sm.tex`（本项目存于 `references/tex/Caster2025_Supplementary.tex`）：

* 三套权重表：**348–375** 行；
* **JC69 的化简推导（那个 `1/8`）**：**1503–1548** 行。

依赖：`Phylo.JukesCantor`（JC69 转移矩阵、`patternProb`）与
`Phylo.Stat.CASTERWeights`（附录 Fig. 1C 的逐模式权重表 `wJC` / `wJCR`、`Topo`、`perm`）。

## 命题 A（JC69）说了什么

四叶物种树拓扑 `12|34`（= `Topo.ab_cd`），叶边 `t 0, t 1, t 3, t 4`、内部边 `t 2`。
真实逐模式权重表 `wJCR T`（`+1` 类 12 个模式、`-1/2` 类 48 个模式、其余 0）下的期望得分

`score t T = ∑_σ wJCR T σ · patternProb t σ`

满足（本文件**全部机器证明**，无 `sorry`、无 `axiom`）：

* ★★★ `score t .ab_cd - score t .ac_bd
      = (3/4) · e(t 0)·e(t 1)·e(t 3)·e(t 4) · (1 - e(t 2))`
  （等价指数形式 `score_ab_cd_sub_ac_bd_exp`：`= (3/4) · e(t 0 + t 1 + t 3 + t 4) · (1 - e(t 2))`）；
* ★★ `score t .ac_bd = score t .ad_bc`（两个「错」拓扑期望得分相等）；
* ★★ `0 < t 2 → 0 < score t .ab_cd - score t .ac_bd`（正性）；
* ★★ 附录印的**代表元化简式** `red`（6 项）满足
  `red t .ab_cd - red t .ac_bd = (1/8) · e(t 0)·e(t 1)·e(t 3)·e(t 4) · (1 - e(t 2))`；
* ★★ 桥梁 `score t .ab_cd - score t .ac_bd = 6 · (red t .ab_cd - red t .ac_bd)`。

## ⚠️ 本文件要讲清楚的「知识点」：附录的 `1/8` 是**代表元式子**的常数

附录 Fig. 1C 印出的权重表只列了**代表元**：`+1` 行 6 个、`-1/2` 行 12 个（不含镜像）。
但按附录自己写的 matching 语义，`χχ|ψω` 与它的镜像 `ψω|χχ` **都**匹配同一拓扑，因此
**逐模式权重表**应取 `+1` 类 12 个（含 6 个镜像）、`-1/2` 类 48 个（含 36 个镜像）
（`Phylo.Stat.CASTERWeights` 已用 `decide` 穷举 256 个模式验证：`card_pos = 12`、
`card_neg = 48`、`sum_wJC_rat = -12`）。

于是：

| 对象 | 类大小 | 差值常数 |
|---|---|---|
| 附录印的**代表元**化简式 `red`（6 项） | 每类取代表元 | **`1/8`** |
| **真实逐模式权重表**得分 `score` | `12 / 12 / 12`（重数） | **`3/4`** |

二者恰好相差 **6 倍**：`score` 差 `= 6 · red` 差。所以

* 附录那个 `1/8` 对它**自己的化简式**是对的；
* 但对**真实权重表**应为 **`3/4`**。数学本质（差值形状 `f = P(L_T)·Q(l_x) > 0`、
  只依赖 `L_T` 与 `l_x`）不受影响，但**常数必须写对**。

数值独立复核（8 组随机参数，含全 0 退化情形，偏差均 < 1.5e-14）：
真实表得分差 / 附录化简式差 `= 6.000000000000`；
附录化简式差 / `((1/8)·e^{...(1-e(t 2))})` `= 1.000000000000`；
`E[w(ac|bd)] = E[w(ad|bc)]` 相对偏差 < 3e-16。

## 证明路线（本文件的结构）

1. §0–§1：`star4`（四条边共用一个内部状态的星形和）与 `patternProb` 的**内部边分解**
   `patternProb t σ = (1/4)·(off(t 2)·K(t 0+t 1)(σ 0,σ 1)·K(t 3+t 4)(σ 2,σ 3)
   + e(t 2)·star4 (t 0,t 1,t 3,t 4) σ)`；
2. §2：`star4` 在**九种相等形状**上的闭式（`fin_cases` 穷举标签 + `ring`）；
3. §3：三个权重类的谓词 `clsPos / clsNeg1 / clsNeg2`、按配对坐标的辅助权重 `wAux`
   （与 `wJCR` 逐拓扑相等，`decide` 验证），以及**按类求和的通用引理** `sum_wAux_class`；
4. §4：九个类上的 `patternProb` 值 `PabPos / … / PadNeg2`；
5. §5–§6：`score` / `red` 的闭式与三条主定理（全部由 `ring` 收口）。

## 诚实边界

* 本文件只做 **JC69**；F84 / LM1 的表（`sm.tex` 1552–1700）不在本批范围。
* `red` 的模式按 `Topo.perm` 搬到对应叶位置：基准 `ab_cd` 就是附录字面量
  `vec 0 0 2 2` 等；对 `ac_bd` 而言 `perm = swap 1 2` 是**对合**，
  故 `perm` 与 `perm⁻¹` 两种约定给同一结果（本文件取 `σ = p ∘ (perm T)⁻¹`）。
* 没有把「附录表是代表元表」当成 `score` 的定义；`score` 用的是共享模块的**真实逐模式表**
  `wJCR`，代表元式子 `red` 是**另一个**（单独定义的）函数，两者关系由定理 `score_sub_eq_six_mul_red` 给出。
-/

noncomputable section

namespace Phylo

namespace CASTERJC69

open Finset
open Phylo.JC
open Phylo.Stat.CASTERWeights

set_option maxRecDepth 100000

/-! ## 0. 星形和 `star4` 与位置辅助 -/

/-- **四叶星形和**：四条边 `l 0, l 1, l 2, l 3` 的叶状态为 `x 0, …, x 3`，
它们共用一个内部状态 `u` 时的概率和 `∑_u ∏_i K(l i)(u, x i)`。 -/
def star4 (l : Fin 4 → ℝ) (x : Fin 4 → Fin 4) : ℝ :=
  ∑ u : Fin 4, ∏ i : Fin 4, kernel (l i) u (x i)

/-- 四条**叶边**的长度函数 `(t 0, t 1, t 3, t 4)`（拓扑 `12|34` 的两侧）。 -/
def edge (t : Fin 5 → ℝ) : Fin 4 → ℝ := ![t 0, t 1, t 3, t 4]

@[simp] theorem edge_zero (t : Fin 5 → ℝ) : edge t 0 = t 0 := rfl

@[simp] theorem edge_one (t : Fin 5 → ℝ) : edge t 1 = t 1 := rfl

@[simp] theorem edge_two (t : Fin 5 → ℝ) : edge t 2 = t 3 := rfl

@[simp] theorem edge_three (t : Fin 5 → ℝ) : edge t 3 = t 4 := rfl

@[simp] theorem vec_app_zero (a b c d : Fin 4) : vec a b c d 0 = a := rfl

@[simp] theorem vec_app_one (a b c d : Fin 4) : vec a b c d 1 = b := rfl

@[simp] theorem vec_app_two (a b c d : Fin 4) : vec a b c d 2 = c := rfl

@[simp] theorem vec_app_three (a b c d : Fin 4) : vec a b c d 3 = d := rfl

/-! ## 1. 内部状态求和与 `patternProb` 的分解 -/

/-- `∑_b ind a b * G b = G a`。 -/
theorem sum_ind_mul (a : Fin 4) (G : Fin 4 → ℝ) : ∑ b : Fin 4, ind a b * G b = G a := by
  rw [Finset.sum_eq_single a]
  · simp [ind]
  · intro b _ hb; simp [ind, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **共起点卷积**：`∑_a K(s)(a,x)·K(u)(a,y) = K(s+u)(x,y)`。 -/
theorem kernel_conv' (s u : ℝ) (x y : Fin 4) :
    ∑ a : Fin 4, kernel s a x * kernel u a y = kernel (s + u) x y := by
  rw [Finset.sum_congr rfl (fun a _ => by rw [kernel_symm s a x])]
  exact kernel_conv s u x y

/-- **单边内部状态求和**：`∑_b K(s)(a,b)·G b = off s · (∑_b G b) + e s · G a`。 -/
theorem sum_kernel_mul (s : ℝ) (a : Fin 4) (G : Fin 4 → ℝ) :
    ∑ b : Fin 4, kernel s a b * G b = off s * (∑ b : Fin 4, G b) + e s * G a := by
  rw [Finset.sum_congr rfl (fun b _ => by rw [kernel_apply, add_mul])]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [show (∑ b : Fin 4, ind a b * e s * G b) = ∑ b : Fin 4, e s * (ind a b * G b) from
    Finset.sum_congr rfl (fun b _ => by ring)]
  rw [← Finset.mul_sum, sum_ind_mul]

/-- **双分划求和**：把内部边 `s` 的求和推到两侧内部状态上。 -/
theorem sum_kernel_split (s : ℝ) (F G : Fin 4 → ℝ) :
    ∑ a : Fin 4, ∑ b : Fin 4, F a * kernel s a b * G b =
      off s * (∑ a : Fin 4, F a) * (∑ b : Fin 4, G b) + e s * (∑ a : Fin 4, F a * G a) := by
  have h1 : ∀ a : Fin 4, ∑ b : Fin 4, F a * kernel s a b * G b
      = F a * (off s * (∑ b : Fin 4, G b) + e s * G a) := by
    intro a
    rw [show (∑ b : Fin 4, F a * kernel s a b * G b)
        = ∑ b : Fin 4, F a * (kernel s a b * G b) from
      Finset.sum_congr rfl (fun b _ => by rw [mul_assoc])]
    rw [← Finset.mul_sum, sum_kernel_mul]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [show (∑ a : Fin 4, F a * (off s * (∑ b : Fin 4, G b) + e s * G a))
      = ∑ a : Fin 4, (F a * (off s * (∑ b : Fin 4, G b)) + F a * (e s * G a)) from
    Finset.sum_congr rfl (fun a _ => by ring)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul]; ring
  · rw [show (∑ a : Fin 4, F a * (e s * G a)) = ∑ a : Fin 4, e s * (F a * G a) from
      Finset.sum_congr rfl (fun a _ => by ring)]
    rw [← Finset.mul_sum]

/-- ★ **`patternProb` 的「内部边 + 星形」分解**：

`patternProb t σ = (1/4)·(off(t 2)·K(t 0+t 1)(σ 0,σ 1)·K(t 3+t 4)(σ 2,σ 3)
+ e(t 2)·star4 (t 0,t 1,t 3,t 4) σ)`。

（把内部边 `t 2` 的求和用 `sum_kernel_split` 推到两侧内部状态上，
两侧的求和再用共起点卷积 `kernel_conv'` 收成 `lam (t 0+t 1)` / `lam (t 3+t 4)`。） -/
theorem patternProb_eq (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4) :
    patternProb t σ = (1 / 4) * (off (t 2) * kernel (t 0 + t 1) (σ 0) (σ 1)
      * kernel (t 3 + t 4) (σ 2) (σ 3) + e (t 2) * star4 (edge t) σ) := by
  rw [patternProb]
  rw [show (∑ a : Fin 4, ∑ b : Fin 4,
        kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
          * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3))
      = ∑ a : Fin 4, ∑ b : Fin 4,
        (kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1)) * kernel (t 2) a b
          * (kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3)) from by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring]
  rw [sum_kernel_split (t 2) (fun a => kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1))
    (fun b => kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3))]
  have hA : ∑ a : Fin 4, kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1)
      = kernel (t 0 + t 1) (σ 0) (σ 1) := kernel_conv' (t 0) (t 1) (σ 0) (σ 1)
  have hB : ∑ b : Fin 4, kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3)
      = kernel (t 3 + t 4) (σ 2) (σ 3) := kernel_conv' (t 3) (t 4) (σ 2) (σ 3)
  have hC : ∑ a : Fin 4, (kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1))
      * (kernel (t 3) a (σ 2) * kernel (t 4) a (σ 3)) = star4 (edge t) σ := by
    simp only [star4, Fin.prod_univ_four, edge_zero, edge_one, edge_two, edge_three]
    apply Finset.sum_congr rfl; intro u _
    ring
  rw [hA, hB, hC]

/-! ## 2. `star4` 的九种相等形状闭式

`l = edge t = (t 0, t 1, t 3, t 4)`，记 `λ_i = lam (l i)`、`o_i = off (l i)`、`P = ∏_i o_i`。
对状态 `x`，`star4 l x = ∑_u ∏_i (o_i + [x i = u]·e (l i))`：只有 `u` 取到 `x` 中
**出现过的标签**时才与全 `o` 项不同，于是按「哪些位置共用一个标签」分类即得下表。
每条都用 `fin_cases` 穷举标签（把变量变成字面量）+ `ring` 机械收口。 -/

/-- 形状 `(χ,χ,ψ,ψ)`（`χ ≠ ψ`）。 -/
theorem star4_aabb (l : Fin 4 → ℝ) (χ ψ : Fin 4) (h : χ ≠ ψ) :
    star4 l (vec χ χ ψ ψ) =
      lam (l 0) * lam (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * lam (l 2) * lam (l 3)
        + 2 * (off (l 0) * off (l 1) * off (l 2) * off (l 3)) := by
  fin_cases χ <;> fin_cases ψ <;>
    first
      | exact absurd rfl h
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(χ,ψ,χ,ψ)`（`χ ≠ ψ`）。 -/
theorem star4_abab (l : Fin 4 → ℝ) (χ ψ : Fin 4) (h : χ ≠ ψ) :
    star4 l (vec χ ψ χ ψ) =
      lam (l 0) * off (l 1) * lam (l 2) * off (l 3)
        + off (l 0) * lam (l 1) * off (l 2) * lam (l 3)
        + 2 * (off (l 0) * off (l 1) * off (l 2) * off (l 3)) := by
  fin_cases χ <;> fin_cases ψ <;>
    first
      | exact absurd rfl h
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(χ,ψ,ψ,χ)`（`χ ≠ ψ`）。 -/
theorem star4_abba (l : Fin 4 → ℝ) (χ ψ : Fin 4) (h : χ ≠ ψ) :
    star4 l (vec χ ψ ψ χ) =
      lam (l 0) * off (l 1) * off (l 2) * lam (l 3)
        + off (l 0) * lam (l 1) * lam (l 2) * off (l 3)
        + 2 * (off (l 0) * off (l 1) * off (l 2) * off (l 3)) := by
  fin_cases χ <;> fin_cases ψ <;>
    first
      | exact absurd rfl h
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(χ,χ,ψ,ω)`，`χ,ψ,ω` 两两互异。 -/
theorem star4_aabc (l : Fin 4 → ℝ) (χ ψ ω : Fin 4) (h1 : χ ≠ ψ) (h2 : χ ≠ ω) (h3 : ψ ≠ ω) :
    star4 l (vec χ χ ψ ω) =
      lam (l 0) * lam (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * lam (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * lam (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases χ <;> fin_cases ψ <;> fin_cases ω <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(ψ,ω,χ,χ)`，`ψ,ω,χ` 两两互异。 -/
theorem star4_bcaa (l : Fin 4 → ℝ) (ψ ω χ : Fin 4) (h1 : ψ ≠ ω) (h2 : ψ ≠ χ) (h3 : ω ≠ χ) :
    star4 l (vec ψ ω χ χ) =
      off (l 0) * off (l 1) * lam (l 2) * lam (l 3)
        + lam (l 0) * off (l 1) * off (l 2) * off (l 3)
        + off (l 0) * lam (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases ψ <;> fin_cases ω <;> fin_cases χ <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(χ,ψ,χ,ω)`，`χ,ψ,ω` 两两互异。 -/
theorem star4_abac (l : Fin 4 → ℝ) (χ ψ ω : Fin 4) (h1 : χ ≠ ψ) (h2 : χ ≠ ω) (h3 : ψ ≠ ω) :
    star4 l (vec χ ψ χ ω) =
      lam (l 0) * off (l 1) * lam (l 2) * off (l 3)
        + off (l 0) * lam (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * lam (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases χ <;> fin_cases ψ <;> fin_cases ω <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(ψ,χ,ω,χ)`，`ψ,χ,ω` 两两互异。 -/
theorem star4_baca (l : Fin 4 → ℝ) (ψ χ ω : Fin 4) (h1 : ψ ≠ χ) (h2 : ψ ≠ ω) (h3 : χ ≠ ω) :
    star4 l (vec ψ χ ω χ) =
      off (l 0) * lam (l 1) * off (l 2) * lam (l 3)
        + lam (l 0) * off (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * lam (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases ψ <;> fin_cases χ <;> fin_cases ω <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(χ,ψ,ω,χ)`，`χ,ψ,ω` 两两互异。 -/
theorem star4_abca (l : Fin 4 → ℝ) (χ ψ ω : Fin 4) (h1 : χ ≠ ψ) (h2 : χ ≠ ω) (h3 : ψ ≠ ω) :
    star4 l (vec χ ψ ω χ) =
      lam (l 0) * off (l 1) * off (l 2) * lam (l 3)
        + off (l 0) * lam (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * lam (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases χ <;> fin_cases ψ <;> fin_cases ω <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-- 形状 `(ψ,χ,χ,ω)`，`ψ,χ,ω` 两两互异。 -/
theorem star4_baac (l : Fin 4 → ℝ) (ψ χ ω : Fin 4) (h1 : ψ ≠ χ) (h2 : ψ ≠ ω) (h3 : χ ≠ ω) :
    star4 l (vec ψ χ χ ω) =
      off (l 0) * lam (l 1) * lam (l 2) * off (l 3)
        + lam (l 0) * off (l 1) * off (l 2) * off (l 3)
        + off (l 0) * off (l 1) * off (l 2) * lam (l 3)
        + off (l 0) * off (l 1) * off (l 2) * off (l 3) := by
  fin_cases ψ <;> fin_cases χ <;> fin_cases ω <;>
    first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | (simp [star4, Fin.sum_univ_four, Fin.prod_univ_four, kernel_apply, ind, vec_app_zero,
          vec_app_one, vec_app_two, vec_app_three, lam, off]
         ring)

/-! ## 3. 三个权重类、辅助权重与按类求和 -/

/-- `+1` 类（配对坐标版）：`{p,q}` 侧同字母、`{r,s}` 侧同字母，两侧字母不同。

用 `abbrev` 而不是 `def`，好让 `Decidable` 实例与 `decide` 能透过它归约。 -/
abbrev clsPos (p q r s : Fin 4) (σ : Fin 4 → Fin 4) : Prop :=
  σ p = σ q ∧ σ r = σ s ∧ σ p ≠ σ r

/-- `-1/2` 类（前一朝向）：`{p,q}` 侧同字母 `χ`，`{r,s}` 侧互异且都 `≠ χ`。 -/
abbrev clsNeg1 (p q r s : Fin 4) (σ : Fin 4 → Fin 4) : Prop :=
  σ p = σ q ∧ σ r ≠ σ s ∧ σ r ≠ σ p ∧ σ s ≠ σ p

/-- `-1/2` 类（后一朝向，即镜像）：`{r,s}` 侧同字母 `χ`，`{p,q}` 侧互异且都 `≠ χ`。 -/
abbrev clsNeg2 (p q r s : Fin 4) (σ : Fin 4 → Fin 4) : Prop :=
  σ r = σ s ∧ σ p ≠ σ q ∧ σ p ≠ σ r ∧ σ q ≠ σ r

theorem clsPos_not_clsNeg1 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsPos p q r s σ) :
    ¬ clsNeg1 p q r s σ := by
  rintro ⟨-, h2, -⟩
  exact h2 h.2.1

theorem clsPos_not_clsNeg2 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsPos p q r s σ) :
    ¬ clsNeg2 p q r s σ := by
  rintro ⟨-, h2, -⟩
  exact h2 h.1

theorem clsNeg1_not_clsNeg2 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsNeg1 p q r s σ) :
    ¬ clsNeg2 p q r s σ := by
  rintro ⟨h2, -⟩
  exact h.2.1 h2

/-- `Val` 版的**按配对坐标**权重（与附录表 `wJCBase` 同一张表，只是坐标换成配对 `(p,q,r,s)`）。 -/
def wAuxV (p q r s : Fin 4) (σ : Fin 4 → Fin 4) : Val :=
  if clsPos p q r s σ then Val.pos
  else if clsNeg1 p q r s σ ∨ clsNeg2 p q r s σ then Val.negHalf
  else Val.zero

/-- `ℝ` 版的按配对坐标权重（`Val.toReal`）。 -/
noncomputable def wAux (p q r s : Fin 4) (σ : Fin 4 → Fin 4) : ℝ := (wAuxV p q r s σ).toReal

@[simp] theorem wAuxV_pos (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsPos p q r s σ) :
    wAuxV p q r s σ = Val.pos := by
  simp only [wAuxV, ite_eq_left h]

@[simp] theorem wAuxV_neg1 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsNeg1 p q r s σ) :
    wAuxV p q r s σ = Val.negHalf := by
  have h1 : ¬ clsPos p q r s σ := fun hc => clsPos_not_clsNeg1 p q r s hc h
  simp only [wAuxV, ite_eq_right h1, ite_eq_left (Or.inl h)]

@[simp] theorem wAuxV_neg2 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsNeg2 p q r s σ) :
    wAuxV p q r s σ = Val.negHalf := by
  have h1 : ¬ clsPos p q r s σ := fun hc => clsPos_not_clsNeg2 p q r s hc h
  simp only [wAuxV, ite_eq_right h1, ite_eq_left (Or.inr h)]

@[simp] theorem wAuxV_zero (p q r s : Fin 4) {σ : Fin 4 → Fin 4}
    (h1 : ¬ clsPos p q r s σ) (h2 : ¬ clsNeg1 p q r s σ) (h3 : ¬ clsNeg2 p q r s σ) :
    wAuxV p q r s σ = Val.zero := by
  simp only [wAuxV, ite_eq_right h1, ite_eq_right (not_or.mpr ⟨h2, h3⟩)]

@[simp] theorem wAux_pos (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsPos p q r s σ) :
    wAux p q r s σ = 1 := by
  simp only [wAux, wAuxV_pos p q r s h, Val.toReal_pos]

@[simp] theorem wAux_neg1 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsNeg1 p q r s σ) :
    wAux p q r s σ = -(1 / 2) := by
  simp only [wAux, wAuxV_neg1 p q r s h, Val.toReal_negHalf]

@[simp] theorem wAux_neg2 (p q r s : Fin 4) {σ : Fin 4 → Fin 4} (h : clsNeg2 p q r s σ) :
    wAux p q r s σ = -(1 / 2) := by
  simp only [wAux, wAuxV_neg2 p q r s h, Val.toReal_negHalf]

@[simp] theorem wAux_zero (p q r s : Fin 4) {σ : Fin 4 → Fin 4}
    (h1 : ¬ clsPos p q r s σ) (h2 : ¬ clsNeg1 p q r s σ) (h3 : ¬ clsNeg2 p q r s σ) :
    wAux p q r s σ = 0 := by
  simp only [wAux, wAuxV_zero p q r s h1 h2 h3, Val.toReal_zero]

/-- ★ **按配对坐标的权重与附录表逐拓扑相等**（`decide` 穷举 256 个模式）。 -/
theorem wJC_eq_wAuxV_ab_cd : ∀ σ : Fin 4 → Fin 4, wJC .ab_cd σ = wAuxV 0 1 2 3 σ := by
  decide

theorem wJC_eq_wAuxV_ac_bd : ∀ σ : Fin 4 → Fin 4, wJC .ac_bd σ = wAuxV 0 2 1 3 σ := by
  decide

theorem wJC_eq_wAuxV_ad_bc : ∀ σ : Fin 4 → Fin 4, wJC .ad_bc σ = wAuxV 0 3 1 2 σ := by
  decide

theorem wJCR_eq_wAux_ab_cd (σ : Fin 4 → Fin 4) : wJCR .ab_cd σ = wAux 0 1 2 3 σ := by
  show (wJC .ab_cd σ).toReal = (wAuxV 0 1 2 3 σ).toReal
  rw [wJC_eq_wAuxV_ab_cd σ]

theorem wJCR_eq_wAux_ac_bd (σ : Fin 4 → Fin 4) : wJCR .ac_bd σ = wAux 0 2 1 3 σ := by
  show (wJC .ac_bd σ).toReal = (wAuxV 0 2 1 3 σ).toReal
  rw [wJC_eq_wAuxV_ac_bd σ]

theorem wJCR_eq_wAux_ad_bc (σ : Fin 4 → Fin 4) : wJCR .ad_bc σ = wAux 0 3 1 2 σ := by
  show (wJC .ad_bc σ).toReal = (wAuxV 0 3 1 2 σ).toReal
  rw [wJC_eq_wAuxV_ad_bc σ]

/-- ★★ **按类求和**：若 `F` 在三个权重类上分别取常数 `v1`、`v2`、`v3`，
则 `∑_σ wAux p q r s σ · F σ = 12·v1 - 12·v2 - 12·v3`
（`+1` 类 12 个、`-1/2` 类各 24 个，故两个负类各贡献 `24·(-1/2) = -12`）。 -/
theorem sum_wAux_class (p q r s : Fin 4) (F : (Fin 4 → Fin 4) → ℝ) (v1 v2 v3 : ℝ)
    (hcard1 : (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => clsPos p q r s σ)).card = 12)
    (hcard2 : (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => clsNeg1 p q r s σ)).card = 24)
    (hcard3 : (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => clsNeg2 p q r s σ)).card = 24)
    (hF1 : ∀ σ : Fin 4 → Fin 4, clsPos p q r s σ → F σ = v1)
    (hF2 : ∀ σ : Fin 4 → Fin 4, clsNeg1 p q r s σ → F σ = v2)
    (hF3 : ∀ σ : Fin 4 → Fin 4, clsNeg2 p q r s σ → F σ = v3) :
    ∑ σ : Fin 4 → Fin 4, wAux p q r s σ * F σ = 12 * v1 - 12 * v2 - 12 * v3 := by
  have key : ∀ σ : Fin 4 → Fin 4, wAux p q r s σ * F σ =
      (if clsPos p q r s σ then v1 else 0)
        + (if clsNeg1 p q r s σ then -(1 / 2) * v2 else 0)
        + (if clsNeg2 p q r s σ then -(1 / 2) * v3 else 0) := by
    intro σ
    by_cases h1 : clsPos p q r s σ
    · rw [hF1 σ h1, wAux_pos p q r s h1, one_mul, ite_eq_left h1,
        ite_eq_right (clsPos_not_clsNeg1 p q r s h1), ite_eq_right (clsPos_not_clsNeg2 p q r s h1)]
      ring
    · by_cases h2 : clsNeg1 p q r s σ
      · rw [hF2 σ h2, wAux_neg1 p q r s h2, ite_eq_right h1, ite_eq_left h2,
          ite_eq_right (clsNeg1_not_clsNeg2 p q r s h2)]
        ring
      · by_cases h3 : clsNeg2 p q r s σ
        · rw [hF3 σ h3, wAux_neg2 p q r s h3, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          ring
        · rw [wAux_zero p q r s h1 h2 h3, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          ring
  rw [Finset.sum_congr rfl (fun σ _ => key σ), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : (∑ σ : Fin 4 → Fin 4, (if clsPos p q r s σ then v1 else 0)) = 12 * v1 := by
    rw [← Finset.sum_filter, Finset.sum_const, hcard1, nsmul_eq_mul]
    norm_num
  have e2 : (∑ σ : Fin 4 → Fin 4, (if clsNeg1 p q r s σ then -(1 / 2) * v2 else 0))
      = 24 * (-(1 / 2) * v2) := by
    rw [← Finset.sum_filter, Finset.sum_const, hcard2, nsmul_eq_mul]
    norm_num
  have e3 : (∑ σ : Fin 4 → Fin 4, (if clsNeg2 p q r s σ then -(1 / 2) * v3 else 0))
      = 24 * (-(1 / 2) * v3) := by
    rw [← Finset.sum_filter, Finset.sum_const, hcard3, nsmul_eq_mul]
    norm_num
  rw [e1, e2, e3]
  ring

/-! ## 4. 九个类上的 `patternProb` 值

记 `t 0, t 1, t 3, t 4` 为四条叶边、`t 2` 为内部边。每条都是
`patternProb t σ = (1/4)·(off(t 2)·K(t 0+t 1)(σ 0,σ 1)·K(t 3+t 4)(σ 2,σ 3) + e(t 2)·star4)`
的代入：同侧配对相等时 `K` 取 `lam`、不等时取 `off`，`star4` 由 §2 的九条形状引理给出。 -/

/-- `ab|cd` 的 `+1` 类上的 `patternProb` 值。 -/
noncomputable def PabPos (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * lam (t 0 + t 1) * lam (t 3 + t 4)
    + e (t 2) * (lam (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * lam (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4))))

/-- `ab|cd` 的 `-1/2` 类（前一朝向）上的 `patternProb` 值。 -/
noncomputable def PabNeg1 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * lam (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (lam (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

/-- `ab|cd` 的 `-1/2` 类（后一朝向）上的 `patternProb` 值。 -/
noncomputable def PabNeg2 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * lam (t 3 + t 4)
    + e (t 2) * (off (t 0) * off (t 1) * lam (t 3) * lam (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

/-- `ac|bd` 的 `+1` 类上的 `patternProb` 值。 -/
noncomputable def PacPos (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (lam (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * lam (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4))))

/-- `ac|bd` 的 `-1/2` 类（前一朝向）上的 `patternProb` 值。 -/
noncomputable def PacNeg1 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (lam (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

/-- `ac|bd` 的 `-1/2` 类（后一朝向）上的 `patternProb` 值。 -/
noncomputable def PacNeg2 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (off (t 0) * lam (t 1) * off (t 3) * lam (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

/-- `ad|bc` 的 `+1` 类上的 `patternProb` 值。 -/
noncomputable def PadPos (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (lam (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * lam (t 1) * lam (t 3) * off (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4))))

/-- `ad|bc` 的 `-1/2` 类（前一朝向）上的 `patternProb` 值。 -/
noncomputable def PadNeg1 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (lam (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

/-- `ad|bc` 的 `-1/2` 类（后一朝向）上的 `patternProb` 值。 -/
noncomputable def PadNeg2 (t : Fin 5 → ℝ) : ℝ :=
  (1 / 4) * (off (t 2) * off (t 0 + t 1) * off (t 3 + t 4)
    + e (t 2) * (off (t 0) * lam (t 1) * lam (t 3) * off (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4)))

theorem patternProb_clsPos_ab (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 1) (h2 : σ 2 = σ 3) (h3 : σ 0 ≠ σ 2) :
    patternProb t σ = PabPos t := by
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = lam (t 0 + t 1) := by rw [h1, kernel_diag]
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = lam (t 3 + t 4) := by rw [h2, kernel_diag]
  have hstar : star4 (edge t) σ = lam (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * lam (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4)) := by
    have hfun : σ = vec (σ 0) (σ 0) (σ 2) (σ 2) := by
      funext i; fin_cases i <;> simp [h1, h2]
    rw [hfun, star4_aabb (edge t) (σ 0) (σ 2) h3]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PabPos]

theorem patternProb_clsNeg1_ab (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 1) (h2 : σ 2 ≠ σ 3) (h3 : σ 2 ≠ σ 0) (h4 : σ 3 ≠ σ 0) :
    patternProb t σ = PabNeg1 t := by
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = lam (t 0 + t 1) := by rw [h1, kernel_diag]
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h2
  have hstar : star4 (edge t) σ = lam (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 0) (σ 2) (σ 3) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_aabc (edge t) (σ 0) (σ 2) (σ 3) (Ne.symm h3) (Ne.symm h4) h2]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PabNeg1]

theorem patternProb_clsNeg2_ab (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 2 = σ 3) (h2 : σ 0 ≠ σ 1) (h3 : σ 0 ≠ σ 2) (h4 : σ 1 ≠ σ 2) :
    patternProb t σ = PabNeg2 t := by
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h2
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = lam (t 3 + t 4) := by rw [h1, kernel_diag]
  have hstar : star4 (edge t) σ = off (t 0) * off (t 1) * lam (t 3) * lam (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 2) (σ 2) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_bcaa (edge t) (σ 0) (σ 1) (σ 2) h2 h3 h4]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PabNeg2]

theorem patternProb_clsPos_ac (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 2) (h2 : σ 1 = σ 3) (h3 : σ 0 ≠ σ 1) :
    patternProb t σ = PacPos t := by
  have h23 : σ 2 ≠ σ 3 := by rw [← h1, ← h2]; exact h3
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h3
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = lam (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * lam (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4)) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 0) (σ 1) := by
      funext i; fin_cases i <;> simp [h1, h2]
    rw [hfun, star4_abab (edge t) (σ 0) (σ 1) h3]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PacPos]

theorem patternProb_clsNeg1_ac (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 2) (h2 : σ 1 ≠ σ 3) (h3 : σ 1 ≠ σ 0) (h4 : σ 3 ≠ σ 0) :
    patternProb t σ = PacNeg1 t := by
  have h01 : σ 0 ≠ σ 1 := Ne.symm h3
  have h04 : σ 0 ≠ σ 3 := Ne.symm h4
  have h23 : σ 2 ≠ σ 3 := by rw [← h1]; exact Ne.symm h4
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h01
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = lam (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 0) (σ 3) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_abac (edge t) (σ 0) (σ 1) (σ 3) h01 h04 h2]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PacNeg1]

theorem patternProb_clsNeg2_ac (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 1 = σ 3) (h2 : σ 0 ≠ σ 2) (h3 : σ 0 ≠ σ 1) (h4 : σ 2 ≠ σ 1) :
    patternProb t σ = PacNeg2 t := by
  have h23 : σ 2 ≠ σ 3 := by rw [← h1]; exact h4
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h3
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = off (t 0) * lam (t 1) * off (t 3) * lam (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 2) (σ 1) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_baca (edge t) (σ 0) (σ 1) (σ 2) h3 h2 (Ne.symm h4)]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PacNeg2]

theorem patternProb_clsPos_ad (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 3) (h2 : σ 1 = σ 2) (h3 : σ 0 ≠ σ 1) :
    patternProb t σ = PadPos t := by
  have h23 : σ 2 ≠ σ 3 := by rw [← h2, ← h1]; exact Ne.symm h3
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h3
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = lam (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * lam (t 1) * lam (t 3) * off (t 4)
      + 2 * (off (t 0) * off (t 1) * off (t 3) * off (t 4)) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 1) (σ 0) := by
      funext i; fin_cases i <;> simp [h1, h2]
    rw [hfun, star4_abba (edge t) (σ 0) (σ 1) h3]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PadPos]

theorem patternProb_clsNeg1_ad (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 0 = σ 3) (h2 : σ 1 ≠ σ 2) (h3 : σ 1 ≠ σ 0) (h4 : σ 2 ≠ σ 0) :
    patternProb t σ = PadNeg1 t := by
  have h01 : σ 0 ≠ σ 1 := Ne.symm h3
  have h02 : σ 0 ≠ σ 2 := Ne.symm h4
  have h23 : σ 2 ≠ σ 3 := by rw [← h1]; exact h4
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h01
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = lam (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * lam (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * lam (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 2) (σ 0) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_abca (edge t) (σ 0) (σ 1) (σ 2) h01 h02 h2]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PadNeg1]

theorem patternProb_clsNeg2_ad (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4)
    (h1 : σ 1 = σ 2) (h2 : σ 0 ≠ σ 3) (h3 : σ 0 ≠ σ 1) (h4 : σ 3 ≠ σ 1) :
    patternProb t σ = PadNeg2 t := by
  have h01 : σ 0 ≠ σ 1 := h3
  have h23 : σ 2 ≠ σ 3 := by rw [← h1]; exact Ne.symm h4
  have hk1 : kernel (t 0 + t 1) (σ 0) (σ 1) = off (t 0 + t 1) := kernel_ne _ h01
  have hk2 : kernel (t 3 + t 4) (σ 2) (σ 3) = off (t 3 + t 4) := kernel_ne _ h23
  have hstar : star4 (edge t) σ = off (t 0) * lam (t 1) * lam (t 3) * off (t 4)
      + lam (t 0) * off (t 1) * off (t 3) * off (t 4)
      + off (t 0) * off (t 1) * off (t 3) * lam (t 4)
      + off (t 0) * off (t 1) * off (t 3) * off (t 4) := by
    have hfun : σ = vec (σ 0) (σ 1) (σ 1) (σ 3) := by
      funext i; fin_cases i <;> simp [h1]
    rw [hfun, star4_baac (edge t) (σ 0) (σ 1) (σ 3) h01 h2 (Ne.symm h4)]
    simp only [edge_zero, edge_one, edge_two, edge_three]
  rw [patternProb_eq, hk1, hk2, hstar, PadNeg2]

/-! ## 5. 得分、附录化简式与闭式 -/

/-- **CASTER 的 JC69 期望得分**：真实逐模式权重表 `wJCR` 下的
`∑_σ wJCR T σ · patternProb t σ`。 -/
noncomputable def score (t : Fin 5 → ℝ) (T : Topo) : ℝ :=
  ∑ σ : Fin 4 → Fin 4, wJCR T σ * patternProb t σ

/-- **把 `T` 基准坐标下的模式搬到叶位置上**：`(shift T p) i = p ((perm T)⁻¹ i)`。

`perm T` 把 `T` 的两侧搬回基准拓扑 `ab|cd`，故逆置换把基准坐标的模式搬回叶位置。 -/
def shift (T : Topo) (p : Fin 4 → Fin 4) : Fin 4 → Fin 4 := fun i => p ((perm T).symm i)

/-- ★ **附录印的代表元化简式**（6 项，模式按 `Topo.perm` 搬到对应叶位置）：
`P(aa|cc) + P(cc|aa) - P(aa|cg) - P(aa|gc) - P(cg|aa) - P(gc|aa)`。 -/
noncomputable def red (t : Fin 5 → ℝ) (T : Topo) : ℝ :=
  patternProb t (shift T (vec 0 0 2 2)) + patternProb t (shift T (vec 2 2 0 0))
    - patternProb t (shift T (vec 0 0 2 1)) - patternProb t (shift T (vec 0 0 1 2))
    - patternProb t (shift T (vec 2 1 0 0)) - patternProb t (shift T (vec 1 2 0 0))

theorem shift_ab_cd (p : Fin 4 → Fin 4) : shift .ab_cd p = p := rfl

theorem shift_ac_bd_0022 : shift .ac_bd (vec 0 0 2 2) = vec 0 2 0 2 := by decide

theorem shift_ac_bd_2200 : shift .ac_bd (vec 2 2 0 0) = vec 2 0 2 0 := by decide

theorem shift_ac_bd_0021 : shift .ac_bd (vec 0 0 2 1) = vec 0 2 0 1 := by decide

theorem shift_ac_bd_0012 : shift .ac_bd (vec 0 0 1 2) = vec 0 1 0 2 := by decide

theorem shift_ac_bd_2100 : shift .ac_bd (vec 2 1 0 0) = vec 2 0 1 0 := by decide

theorem shift_ac_bd_1200 : shift .ac_bd (vec 1 2 0 0) = vec 1 0 2 0 := by decide

theorem shift_ad_bc_0022 : shift .ad_bc (vec 0 0 2 2) = vec 0 2 2 0 := by decide

theorem shift_ad_bc_2200 : shift .ad_bc (vec 2 2 0 0) = vec 2 0 0 2 := by decide

theorem shift_ad_bc_0021 : shift .ad_bc (vec 0 0 2 1) = vec 0 2 1 0 := by decide

theorem shift_ad_bc_0012 : shift .ad_bc (vec 0 0 1 2) = vec 0 1 2 0 := by decide

theorem shift_ad_bc_2100 : shift .ad_bc (vec 2 1 0 0) = vec 2 0 0 1 := by decide

theorem shift_ad_bc_1200 : shift .ad_bc (vec 1 2 0 0) = vec 1 0 0 2 := by decide

/-- ★★ `ab|cd` 的得分闭式（真实逐模式权重表）。 -/
theorem score_ab_cd (t : Fin 5 → ℝ) :
    score t .ab_cd = 12 * PabPos t - 12 * PabNeg1 t - 12 * PabNeg2 t := by
  simp only [score, wJCR_eq_wAux_ab_cd]
  exact sum_wAux_class 0 1 2 3 (fun σ => patternProb t σ) (PabPos t) (PabNeg1 t) (PabNeg2 t)
    (by decide) (by decide) (by decide)
    (fun σ h => patternProb_clsPos_ab t σ h.1 h.2.1 h.2.2)
    (fun σ h => patternProb_clsNeg1_ab t σ h.1 h.2.1 h.2.2.1 h.2.2.2)
    (fun σ h => patternProb_clsNeg2_ab t σ h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- ★★ `ac|bd` 的得分闭式。 -/
theorem score_ac_bd (t : Fin 5 → ℝ) :
    score t .ac_bd = 12 * PacPos t - 12 * PacNeg1 t - 12 * PacNeg2 t := by
  simp only [score, wJCR_eq_wAux_ac_bd]
  exact sum_wAux_class 0 2 1 3 (fun σ => patternProb t σ) (PacPos t) (PacNeg1 t) (PacNeg2 t)
    (by decide) (by decide) (by decide)
    (fun σ h => patternProb_clsPos_ac t σ h.1 h.2.1 h.2.2)
    (fun σ h => patternProb_clsNeg1_ac t σ h.1 h.2.1 h.2.2.1 h.2.2.2)
    (fun σ h => patternProb_clsNeg2_ac t σ h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- ★★ `ad|bc` 的得分闭式。 -/
theorem score_ad_bc (t : Fin 5 → ℝ) :
    score t .ad_bc = 12 * PadPos t - 12 * PadNeg1 t - 12 * PadNeg2 t := by
  simp only [score, wJCR_eq_wAux_ad_bc]
  exact sum_wAux_class 0 3 1 2 (fun σ => patternProb t σ) (PadPos t) (PadNeg1 t) (PadNeg2 t)
    (by decide) (by decide) (by decide)
    (fun σ h => patternProb_clsPos_ad t σ h.1 h.2.1 h.2.2)
    (fun σ h => patternProb_clsNeg1_ad t σ h.1 h.2.1 h.2.2.1 h.2.2.2)
    (fun σ h => patternProb_clsNeg2_ad t σ h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- ★★ 附录化简式在 `ab|cd` 上的闭式（6 项中 2 项在 `+1` 类、4 项在两个 `-1/2` 类）。 -/
theorem red_ab_cd (t : Fin 5 → ℝ) :
    red t .ab_cd = 2 * PabPos t - 2 * PabNeg1 t - 2 * PabNeg2 t := by
  simp only [red, shift_ab_cd]
  rw [patternProb_clsPos_ab t (vec 0 0 2 2) (by decide) (by decide) (by decide),
    patternProb_clsPos_ab t (vec 2 2 0 0) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ab t (vec 0 0 2 1) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ab t (vec 0 0 1 2) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ab t (vec 2 1 0 0) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ab t (vec 1 2 0 0) (by decide) (by decide) (by decide) (by decide)]
  ring

/-- ★★ 附录化简式在 `ac|bd` 上的闭式。 -/
theorem red_ac_bd (t : Fin 5 → ℝ) :
    red t .ac_bd = 2 * PacPos t - 2 * PacNeg1 t - 2 * PacNeg2 t := by
  simp only [red, shift_ac_bd_0022, shift_ac_bd_2200, shift_ac_bd_0021, shift_ac_bd_0012,
    shift_ac_bd_2100, shift_ac_bd_1200]
  rw [patternProb_clsPos_ac t (vec 0 2 0 2) (by decide) (by decide) (by decide),
    patternProb_clsPos_ac t (vec 2 0 2 0) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ac t (vec 0 2 0 1) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ac t (vec 0 1 0 2) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ac t (vec 2 0 1 0) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ac t (vec 1 0 2 0) (by decide) (by decide) (by decide) (by decide)]
  ring

/-- ★★ 附录化简式在 `ad|bc` 上的闭式。 -/
theorem red_ad_bc (t : Fin 5 → ℝ) :
    red t .ad_bc = 2 * PadPos t - 2 * PadNeg1 t - 2 * PadNeg2 t := by
  simp only [red, shift_ad_bc_0022, shift_ad_bc_2200, shift_ad_bc_0021, shift_ad_bc_0012,
    shift_ad_bc_2100, shift_ad_bc_1200]
  rw [patternProb_clsPos_ad t (vec 0 2 2 0) (by decide) (by decide) (by decide),
    patternProb_clsPos_ad t (vec 2 0 0 2) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ad t (vec 0 2 1 0) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg1_ad t (vec 0 1 2 0) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ad t (vec 2 0 0 1) (by decide) (by decide) (by decide) (by decide),
    patternProb_clsNeg2_ad t (vec 1 0 0 2) (by decide) (by decide) (by decide) (by decide)]
  ring

/-! ## 6. 主定理（命题 A，JC69 情形） -/

/-- ★★★ **命题 A（JC69）**：真实逐模式权重表下，正确拓扑 `ab|cd` 与错拓扑 `ac|bd`
的期望得分差 `= (3/4)·e(t 0)e(t 1)e(t 3)e(t 4)·(1 - e(t 2))`。 -/
theorem score_ab_cd_sub_ac_bd (t : Fin 5 → ℝ) :
    score t .ab_cd - score t .ac_bd
      = (3 / 4) * (e (t 0) * e (t 1) * e (t 3) * e (t 4)) * (1 - e (t 2)) := by
  rw [score_ab_cd, score_ac_bd]
  simp only [PabPos, PabNeg1, PabNeg2, PacPos, PacNeg1, PacNeg2, lam, off, e_add]
  ring

/-- ★★★ 命题 A 的**等价指数形式**：`= (3/4)·e(t 0 + t 1 + t 3 + t 4)·(1 - e(t 2))`。 -/
theorem score_ab_cd_sub_ac_bd_exp (t : Fin 5 → ℝ) :
    score t .ab_cd - score t .ac_bd
      = (3 / 4) * e (t 0 + t 1 + t 3 + t 4) * (1 - e (t 2)) := by
  rw [score_ab_cd_sub_ac_bd]
  rw [show t 0 + t 1 + t 3 + t 4 = (t 0 + t 1) + (t 3 + t 4) from by ring]
  simp only [e_add]
  ring

/-- ★★ 两个「错」拓扑的期望得分相等：`score t .ac_bd = score t .ad_bc`。 -/
theorem score_ac_bd_eq_ad_bc (t : Fin 5 → ℝ) : score t .ac_bd = score t .ad_bc := by
  rw [score_ac_bd, score_ad_bc]
  simp only [PacPos, PacNeg1, PacNeg2, PadPos, PadNeg1, PadNeg2]
  ring

/-- ★★ **正性**：内部边为正时正确拓扑的期望得分严格更大。 -/
theorem score_ab_cd_sub_ac_bd_pos (t : Fin 5 → ℝ) (h : 0 < t 2) :
    0 < score t .ab_cd - score t .ac_bd := by
  rw [score_ab_cd_sub_ac_bd_exp]
  have h2 : e (t 2) < 1 := by
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have h3 : 0 < 1 - e (t 2) := by linarith
  have h4 : 0 < e (t 0 + t 1 + t 3 + t 4) := Real.exp_pos _
  exact mul_pos (mul_pos (by norm_num) h4) h3

/-- ★★ **附录印的化简式（代表元 6 项）**的差值常数是 `1/8`。 -/
theorem red_ab_cd_sub_ac_bd (t : Fin 5 → ℝ) :
    red t .ab_cd - red t .ac_bd
      = (1 / 8) * (e (t 0) * e (t 1) * e (t 3) * e (t 4)) * (1 - e (t 2)) := by
  rw [red_ab_cd, red_ac_bd]
  simp only [PabPos, PabNeg1, PabNeg2, PacPos, PacNeg1, PacNeg2, lam, off, e_add]
  ring

/-- ★★ **桥梁**：真实逐模式权重表的得分差是附录代表元化简式差的 **6 倍**。
（这正是「附录的 `1/8` 对真实表应为 `3/4`」的形式化表述。） -/
theorem score_sub_eq_six_mul_red (t : Fin 5 → ℝ) :
    score t .ab_cd - score t .ac_bd = 6 * (red t .ab_cd - red t .ac_bd) := by
  rw [score_ab_cd, score_ac_bd, red_ab_cd, red_ac_bd]
  ring

/-- ★★ 附录化简式在两个「错」拓扑上也相等（`red` 的镜像不变性）。 -/
theorem red_ac_bd_eq_ad_bc (t : Fin 5 → ℝ) : red t .ac_bd = red t .ad_bc := by
  rw [red_ac_bd, red_ad_bc]
  simp only [PacPos, PacNeg1, PacNeg2, PadPos, PadNeg1, PadNeg2]
  ring

end CASTERJC69

end Phylo
