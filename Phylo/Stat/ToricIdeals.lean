/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.InvariantsRank
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.ZMod.Basic

/-!
# `Phylo.Stat.ToricIdeals` —— I7：JC-DNA（Klein 四元群）模型的 **toric 理想**与「生成元次数 ≤ 4」

## 文献依据（篇名 + 行号；行号指 `references/md/` 下的文本文件）

* **B. Sturmfels, S. Sullivant, *Toric ideals of phylogenetic invariants*,
  `references/md/SturmfelsSullivant2005_ToricIdealsPhyloInvariants.md`（共 2831 行）**：
  * **480–500 行（Lemma 4）**：有限交换群 `G` 的对偶群与 Fourier 变换的基本性质
    （(b) **Fourier 变换把卷积变成乘法**）；**507–520 行**：「group based model 是 toric
    variety」；**628–654 行（Theorem 6, Evans–Speed）**：Fourier 坐标下的**单项式参数化**
    `q(χ₁,…,χ_m) = π̂(χ₁···χ_m) · ∏_v f̂^{(v)}(∏_{l∈Λ(v)}χ_l)`；
  * **2055–2075 行（§6.1）**：**均匀根分布**下 `π̂` 只在单位元处为 `1`，故
    「`g₁+···+g_m ≠ 0` 的 Fourier 坐标 `q_{g₁…g_m}` 是（线性）不变量」（本文件的
    `Coord` 只保留 `∑ gᵢ = 0` 的坐标，正是把这一步模掉）；
  * **2222–2240 行（§6.3, Jukes–Cantor DNA）**：JC DNA 是 `G = Z₂×Z₂` 的 group based model，
    标号函数 `L` 把群映到 `{0,1}`；
  * **2242–2258 行**：模去线性不变量后 claw tree `K₁,₃` 只剩五个未知量
    `q000, q011, q101, q110, q111`，其理想由**一个三次式**生成
    `q000 q111² − q011 q101 q110`；
  * **1040–1111 行（Remark 16 ＋ Lemma 17 ＋ Definition 18）**：**这是本文件的核心**——
    二项式 `M − M′ ∈ I_{T,L}` **当且仅当**每个 tableau 的每行是 allowed labeling，
    且**每条边（每一列）上的标号多重集在 `M` 与 `M′` 中相同**；Lemma 17 的二次二项式
    `q_{l₁ m n₁} q_{l₂ m n₂} − q_{l₁ m n₂} q_{l₂ m n₁}` 就是这一条件的实例。
    本文件的 `balanced_binomial_mem_toricIdeal` 证的就是「**列多重集平衡 ⟹ 落在 toric 理想里**」；
  * **278–290 行（Theorem 2）**：`(b)` JC DNA 的不变量理想由**次数 1, 2, 3** 的多项式生成；
    `(c)` K2P 为 **1, 2, 3, 4**；`(d)` K3P 为 **2, 3, 4**。
    ⇒ 「**生成元次数 ≤ 4**」；本文件把这一条落成显式缺口
    `toricIdeal_generated_in_degree_le_four_gap`，只证**已写下的二项式的次数 ≤ 4**；
  * **1955–1990 行（Theorem 26）＋ 2022–2040 行（Conjecture 28）**：`φ(Z₂,n) = 2`（二元 JC 由
    二次式生成）；`φ(Z₂×Z₂) = 4` 是**猜想**（本文件不假设、不使用）。
* **S. N. Evans, T. P. Speed, *Invariants of some probability models used in phylogenetic
  inference*, `references/md/EvansSpeed1993_InvariantsProbabilityModels.md`（共 1113 行）**：
  * **283–350 行（§3）**：有限交换群上的离散 Fourier 分析（特征标、对偶群、Fourier 逆公式）；
  * **376–420 行（Lemma 4.1–4.3）**：K3P / K2P / JC 的 Fourier 参数化（`f̂(χ)` 的乘积形式）；
  * **532–560 行 ＋ 597–650 行（§6, Theorem 6.1 / 6.2）**：由 Fourier 坐标构造全部不变量的
    一般方法（本文件的 `φ` 就是其中「单项式参数化」这一步）。

## 关于**新增 Mathlib import**（`import Mathlib.Data.ZMod.Basic`）的说明

本文件用了 `G4 := ZMod 2 × ZMod 2`（Klein 四元群）。**为什么必须是这个群**：

* SS2005 **§6.3, 2222–2240 行**：「the Jukes-Cantor DNA model … is a group based model for
  `G = Z₂×Z₂`」；
* Evans–Speed 1993 **431–440 行**：「Identify the four bases {A,G,C,T} with the elements of
  the **Klein four-group** `G = Z₂ ⊕ Z₂`」；
* 本文件的核心机制是**均匀根分布条件 `∑ᵢ gᵢ = 0`**（SS2005 §6.1, 2055–2075 行：
  不满足者是线性不变量）与坐标上的**群加法** —— `Fin 4` 上没有群结构，
  故必须取一个真正的有限交换群；`ZMod 2 × ZMod 2` 是文献里那个群的**最小忠实实现**
  （用 `Fin 2 × Fin 2` 加自定义加法只会把群公理变成额外假设，更差）。

**「显式 import 是否必需」的实测**（脚本 `scripts/msc/_w11b_zmod_test.sh`）：

* 删掉这一行显式 import 后本文件**仍然** `exit 0`、输出 **0 字节** —— 即 `ZMod` 的名字
  是由既有 import（`Mathlib.RingTheory.MvPolynomial.Ideal` 一侧）**传递引入**的；
* 本文件**仍保留**显式 import：显式依赖优于隐式传递依赖（升级 mathlib 时会失败得更早、
  更清楚）。若协调侧要求「不新增任何 Mathlib import」，**删掉这一行即可**，实测不影响编译。
* 全库 `grep -rn 'import Mathlib.Data.ZMod' Phylo/` 只有本文件这一处（见 W11b 报告）。

## 本文件做的事

**设定**（SS2005 §6.1/§6.3 的 claw tree `K₁,ₘ`，均匀根分布）：
`G = Z₂ × Z₂`（Klein 四元群）；
* **坐标**：`Coord m = {g : Fin m → G // ∑ᵢ gᵢ = 0}` —— 就是满足均匀根分布约束的
  Fourier 坐标 `q_g`（`m` 片叶，每片叶一个特征标）；
* **参数**：`Param m = Fin m × G` —— 每片叶 `i` 与每个特征标 `χ` 一个参数 `Y(i,χ) = f̂^{(i)}(χ)`；
* **φ-同态**：`phi m (q_g) = ∏ᵢ Y(i, gᵢ)`（SS2005 (10)/(11) 在 claw tree + 均匀根 + JC DNA 上的
  显式形式；**这就是 Evans–Speed/SS2005 的单项式参数化**）；
* **toric 理想**：`toricIdeal m = ker (phi m)`。

## 已证清单

| 声明 | 一句话 |
|---|---|
| `phi_X` | ★ φ 在坐标上就是那个显式单项式 |
| `monomialOf_prod_eq` | ★★ 两个 tableaux 的**列多重集**逐列相同 ⟹ 它们的 φ-像相同 |
| `balanced_binomial_mem_toricIdeal` | ★★★ **列多重集平衡 ⟹ 二项式 ∈ toric 理想**（Remark 16 / Lemma 17） |
| `totalDegree_sub_le` | ★ 辅助：`(p−q).totalDegree ≤ max` |
| `prod_X_totalDegree_le` | ★ `d` 个不同坐标变量之积的次数 ≤ `d` |
| `binomial_totalDegree_le_four` | ★★ **任意次数 `d ≤ 4` 的平衡二项式次数 ≤ 4**（Theorem 2 的「≤4」这一半） |
| `quadric_mem_toricIdeal` | ★★ `K₁,₄` 上的显式二次不变量（Lemma 17 的实例） |
| `cubic_mem_toricIdeal` | ★★ `K₁,₃` 上的显式三次不变量（SS2005 2242–2258 行那个三次式的**合法提升**） |
| `cubic_reduces_to_SS2005` | ★★ 该三次式模去线性不变量后正是 `q000 q111² − q011 q101 q110` |
| `toricIdeal_ne_top` | ★★ 反空真：toric 理想是**真**理想（φ 不是零映射） |
| `balanced_hypothesis_nonvacuous` | ★★ 反空真：平衡条件是**可满足且非平凡**的 |
| `toricIdeal_generated_in_degree_le_four_gap` | **缺口**：生成元次数 ≤ 4（Theorem 2 / 21 / 24） |

## 反例检查（★B）

1. **平衡条件是必要的**（不是「随便什么二项式都进理想」）：取
   `q_{(a,0,a,0)} q_{(0,0,0,0)} − q_{(a,0,0,a)} q_{(0,0,a,a)}`（`m = 4`，`a = (1,0)`），
   列 3 的多重集是 `{0,0}` 对 `{a,a}`，**不**平衡。Python 脚本
   `scripts/msc/w11b_i3_i6_i7_check.py` 精确穷举给出两者的 φ-像分别是
   `((0,0),(0,1),(1,0),(1,0),(2,0),(2,1),(3,0),(3,0))` 与
   `((0,0),(0,1),(1,0),(1,0),(2,0),(2,1),(3,1),(3,1))`，**不相等** ⇒ 该二项式**不是**不变量。
   （脚本同时穷举 `m = 3`：**不存在**平衡二次二项式 —— 与 SS2005「`K₁,₃` 的理想由单个三次式
   生成」一致；`m = 4`：11584 个平衡二次二项式。）
2. **`toricIdeal ≠ ⊤`**（`toricIdeal_ne_top`）：坐标变量 `X g` 本身不在理想里（φ 把它送到
   非零单项式），故「平衡 ⟹ 在理想里」不是「一切都是不变量」。
3. **`d = 5` 的平衡二项式也是不变量**：`balanced_binomial_mem_toricIdeal` 对**任意** `d` 成立
   （SS2005 的生成元次数 ≤ 4 是**生成元**的限制，不是「不变量次数」的限制）——
   故 `binomial_totalDegree_le_four` **只对 `d ≤ 4`** 断言，不冒充一般结论。

## 诚实边界

* **未证（核心缺口）**：`toricIdeal_generated_in_degree_le_four_gap` —— 「toric 理想**由**这些
  （局部二次 + 局部三次，SS2005 Lemma 17/22 + Theorem 21/24）二项式**生成**」。
  这需要 Gröbner 基 / Markov 基理论（SS2005 §4–§5），当前库内无此器材。
  本文件**只**证「**已写下的**平衡二项式在理想里」＋「它们的次数 ≤ 4」，
  **不**声称「理想由它们生成」。
* **未证**：Theorem 2 的完整形式（一般二元树、四种标准模型的次数上界）与 Conjecture 28
  （`φ(Z₂×Z₂) = 4`）—— 后者是**猜想**，本文件不使用。
* **未做**：一般树（非 claw tree）的 `φ`（需要 SS2005 Theorem 6 的顶点因子 `Λ(v)` 与
  树的组合结构）；`K₁,ₘ` 的 `m ≥ 5` 的显式生成元列表（穷举在 Python 脚本里做，Lean 只给一般定理）。
* **未做**：K2P / K3P / 二元 JC 的对应物（本文件只做 JC DNA = `Z₂ × Z₂`）。
* 本文件**不引入** `Phylo` 根模块，也不改任何无关文件。
* 无 `sorry`、无 `axiom`、无 `native_decide`。
-/

namespace Phylo.Stat.ToricIdeals

open MvPolynomial

/-- **Klein 四元群** `Z₂ × Z₂`（与 `Phylo.LakeInvariants` 的 `Fin 4` 编码
`A=(0,0), C=(1,0), G=(0,1), T=(1,1)` 一致）。 -/
abbrev G4 := ZMod 2 × ZMod 2

/-- ★ **Fourier 坐标**：`m` 片叶、每片叶一个特征标，**均匀根分布**要求
`g₁ + ⋯ + g_m = 0`（SS2005 §6.1, 2055–2075 行：不满足者是线性不变量）。 -/
abbrev Coord (m : ℕ) := {g : Fin m → G4 // ∑ i, g i = 0}

/-- ★ **参数**：`(叶 i, 特征标 χ) ↦ f̂^{(i)}(χ)`（SS2005 Theorem 6 的 `f̂^{(v)}`）。 -/
abbrev Param (m : ℕ) := Fin m × G4

/-- ★★ **φ-像的单项式**：`q_g ↦ ∏ᵢ Y(i, gᵢ)`
（SS2005 (10)/(11) 在 claw tree `K₁,ₘ` + 均匀根 + JC DNA 上的显式形式）。 -/
noncomputable def monomialOf (m : ℕ) (g : Fin m → G4) : MvPolynomial (Param m) ℝ :=
  ∏ i, MvPolynomial.X (i, g i)

/-- ★★★ **φ-同态**（Evans–Speed / SS2005 的**单项式参数化**，Theorem 6, 628–654 行）：
把坐标环 `ℝ[q_g]` 送到参数环 `ℝ[Y]`，`q_g ↦ ∏ᵢ Y(i, gᵢ)`。

因为像是单项式，`im φ` 是 torus 的闭包 —— 这正是「group based model 是 **toric** variety」
（SS2005, 507–520 行）的代数表述。 -/
noncomputable def phi (m : ℕ) : MvPolynomial (Coord m) ℝ →ₐ[ℝ] MvPolynomial (Param m) ℝ :=
  MvPolynomial.aeval fun g => monomialOf m g.1

/-- ★★★ **toric 理想** `I_{G,m} = ker φ`（SS2005 (4) 的 `ker`）。

（`Coord m` 已经把「均匀根分布 ⟹ `∑ gᵢ ≠ 0` 的坐标全是线性不变量」这一步模掉了，
故本理想是**模去线性不变量后**的 toric 理想，与 SS2005 §5 的表格一致。） -/
noncomputable def toricIdeal (m : ℕ) : Ideal (MvPolynomial (Coord m) ℝ) :=
  RingHom.ker (phi m).toRingHom

/-- ★ φ 在坐标上的显式取值。 -/
theorem phi_X (m : ℕ) (g : Coord m) :
    phi m (MvPolynomial.X g) = monomialOf m g.1 :=
  MvPolynomial.aeval_X _ _

/-! ## 1. ★★ 列多重集平衡 ⟹ φ-像相同（Remark 16 的组合半边） -/

/-- ★★ **列多重集平衡 ⟹ 两个 tableau 的 φ-像相同**。

设 `A B : Fin d → Coord m` 是两组坐标（一个 `d` 行 tableau 的两边）。
若对**每一片叶 `i`**，两组坐标在第 `i` 列的取值**多重集相同**，则
`∏_k monomialOf (A k) = ∏_k monomialOf (B k)`。

（这就是 SS2005 **Remark 16 (b)**（1040–1055 行）的「组合半边」：
`φ(M) = φ(M′) ⟺ 每列的多重集相同`。证明直接把 `∏_k ∏_i` 交换成 `∏_i ∏_k`，
再逐列用多重集相等） -/
theorem monomialOf_prod_eq {m d : ℕ} (A B : Fin d → Coord m)
    (h : ∀ i, (Finset.univ.val.map fun k => (A k).1 i)
      = (Finset.univ.val.map fun k => (B k).1 i)) :
    (∏ k, monomialOf m (A k).1) = ∏ k, monomialOf m (B k).1 := by
  have key : ∀ i : Fin m,
      (∏ k, (MvPolynomial.X (i, (A k).1 i) : MvPolynomial (Param m) ℝ))
        = ∏ k, (MvPolynomial.X (i, (B k).1 i) : MvPolynomial (Param m) ℝ) := by
    intro i
    have hm : (Finset.univ.val.map fun k =>
          (MvPolynomial.X (i, (A k).1 i) : MvPolynomial (Param m) ℝ))
        = (Finset.univ.val.map fun k =>
          (MvPolynomial.X (i, (B k).1 i) : MvPolynomial (Param m) ℝ)) := by
      have h1 : (Finset.univ.val.map fun k =>
            (MvPolynomial.X (i, (A k).1 i) : MvPolynomial (Param m) ℝ))
          = (Finset.univ.val.map fun k => (A k).1 i).map
              (fun χ => (MvPolynomial.X (i, χ) : MvPolynomial (Param m) ℝ)) :=
        (Multiset.map_map (fun χ => (MvPolynomial.X (i, χ) : MvPolynomial (Param m) ℝ))
          (fun k => (A k).1 i) _).symm
      have h2 : (Finset.univ.val.map fun k =>
            (MvPolynomial.X (i, (B k).1 i) : MvPolynomial (Param m) ℝ))
          = (Finset.univ.val.map fun k => (B k).1 i).map
              (fun χ => (MvPolynomial.X (i, χ) : MvPolynomial (Param m) ℝ)) :=
        (Multiset.map_map (fun χ => (MvPolynomial.X (i, χ) : MvPolynomial (Param m) ℝ))
          (fun k => (B k).1 i) _).symm
      rw [h1, h2, h i]
    simp only [Finset.prod_eq_multiset_prod]
    rw [hm]
  have hA : (∏ k, monomialOf m (A k).1)
      = ∏ i, ∏ k, (MvPolynomial.X (i, (A k).1 i) : MvPolynomial (Param m) ℝ) := by
    simp only [monomialOf]
    exact Finset.prod_comm
  have hB : (∏ k, monomialOf m (B k).1)
      = ∏ i, ∏ k, (MvPolynomial.X (i, (B k).1 i) : MvPolynomial (Param m) ℝ) := by
    simp only [monomialOf]
    exact Finset.prod_comm
  rw [hA, hB]
  exact Finset.prod_congr rfl fun i _ => key i

/-! ## 2. ★★★ 平衡二项式 ∈ toric 理想（Remark 16 ＋ Lemma 17） -/

/-- ★★★ **列多重集平衡 ⟹ 二项式属于 toric 理想**。

这是 SS2005 **Remark 16**（1040–1055 行）与 **Lemma 17**（1089–1107 行）的核心内容：
把 `M − M′` 写成「`d` 个坐标变量的乘积之差」，只要每一列的标号多重集相同，
它就在 `ker φ` 里。 -/
theorem balanced_binomial_mem_toricIdeal {m d : ℕ} (A B : Fin d → Coord m)
    (h : ∀ i, (Finset.univ.val.map fun k => (A k).1 i)
      = (Finset.univ.val.map fun k => (B k).1 i)) :
    ((∏ k, MvPolynomial.X (A k)) - (∏ k, MvPolynomial.X (B k))
      : MvPolynomial (Coord m) ℝ) ∈ toricIdeal m := by
  rw [toricIdeal, RingHom.mem_ker]
  change phi m ((∏ k, MvPolynomial.X (A k)) - (∏ k, MvPolynomial.X (B k))) = 0
  simp only [map_sub, map_prod, phi_X]
  rw [sub_eq_zero]
  exact monomialOf_prod_eq A B h

/-- ★★ **二次平衡二项式**（Lemma 17 的直接形式，便于显式实例）：若对每片叶 `i`
列多重集 `{a_i, b_i}` 与 `{c_i, d_i}` 相同（等价地：`a_i = c_i ∧ b_i = d_i`
或 `a_i = d_i ∧ b_i = c_i`），则二项式属于 toric 理想。

证明：φ 把两边分别送到 `∏ᵢ X(i,aᵢ)X(i,bᵢ)` 与 `∏ᵢ X(i,cᵢ)X(i,dᵢ)`，
再逐叶用 `X(i,a)X(i,b) = X(i,c)X(i,d)`（交换律）收口。 -/
theorem pair_balanced_mem_toricIdeal {m : ℕ} (a b c d : Coord m)
    (h : ∀ i, (a.1 i = c.1 i ∧ b.1 i = d.1 i) ∨ (a.1 i = d.1 i ∧ b.1 i = c.1 i)) :
    (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d
      : MvPolynomial (Coord m) ℝ) ∈ toricIdeal m := by
  rw [toricIdeal, RingHom.mem_ker]
  change phi m (MvPolynomial.X a * MvPolynomial.X b
    - MvPolynomial.X c * MvPolynomial.X d) = 0
  simp only [map_sub, map_mul, phi_X, monomialOf]
  rw [sub_eq_zero, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, mul_comm]

/-! ## 3. ★★ 次数 ≤ 4（SS2005 Theorem 2 的「≤4」半边） -/

/-- ★ 辅助：差的次数不超过两者的最大次数。 -/
theorem totalDegree_sub_le {σ : Type*} {R : Type*} [CommRing R]
    (p q : MvPolynomial σ R) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le_max le_rfl (le_of_eq (MvPolynomial.totalDegree_neg q)))

/-- ★ `d` 个坐标变量之积的次数 ≤ `d`（用 `totalDegree_finsetProd`）。 -/
theorem prod_X_totalDegree_le {m d : ℕ} (A : Fin d → Coord m) :
    (∏ k, MvPolynomial.X (A k) : MvPolynomial (Coord m) ℝ).totalDegree ≤ d := by
  have h := MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin d))
    (fun k => (MvPolynomial.X (A k) : MvPolynomial (Coord m) ℝ))
  simpa using h

/-- ★★ **次数 ≤ 4 的平衡二项式的次数确实 ≤ 4**（SS2005 Theorem 2(b)/(c)/(d) 的
「生成元次数 ≤ 4」这一**可计算**半边）。

⚠️ 注意：这条**只**说「写下来的这类二项式次数 ≤ 4」，
**不**说「toric 理想由次数 ≤ 4 的元素生成」（后者是 `..._gap`，未证）。 -/
theorem binomial_totalDegree_le_four {m d : ℕ} (A B : Fin d → Coord m) (hd : d ≤ 4) :
    ((∏ k, MvPolynomial.X (A k)) - (∏ k, MvPolynomial.X (B k))
      : MvPolynomial (Coord m) ℝ).totalDegree ≤ 4 :=
  (totalDegree_sub_le _ _).trans
    (max_le ((prod_X_totalDegree_le A).trans hd) ((prod_X_totalDegree_le B).trans hd))

/-! ## 4. ★★ 显式生成元：`K₁,₄` 的二次式与 `K₁,₃` 的三次式 -/

/-- `a = C = (1,0) ∈ Z₂ × Z₂`（Klein 四元群的第一个非平凡元）。 -/
abbrev aG : G4 := (1, 0)

/-- `b = G = (0,1)`。 -/
abbrev bG : G4 := (0, 1)

/-- `c = T = a + b = (1,1)`。 -/
abbrev cG : G4 := (1, 1)

/-! ### 4.1 `K₁,₄` 的二次不变量（Lemma 17 的显式实例） -/

/-- 坐标 `q_{(a,0,a,0)}`。 -/
def q_a0a0 : Coord 4 := ⟨![aG, 0, aG, 0], by decide⟩

/-- 坐标 `q_{(0,a,0,a)}`。 -/
def q_0a0a : Coord 4 := ⟨![0, aG, 0, aG], by decide⟩

/-- 坐标 `q_{(a,a,0,0)}`。 -/
def q_aa00 : Coord 4 := ⟨![aG, aG, 0, 0], by decide⟩

/-- 坐标 `q_{(0,0,a,a)}`。 -/
def q_00aa : Coord 4 := ⟨![0, 0, aG, aG], by decide⟩

/-- ★★ **`K₁,₄` 上的显式二次不变量**（SS2005 Lemma 17 / 1089–1107 行 的实例）：

`q_{(a,0,a,0)} · q_{(0,a,0,a)} − q_{(a,a,0,0)} · q_{(0,0,a,a)} ∈ I_{K₁,₄}`。

列多重集（Klein 群）：列 1 `{a,0} = {a,0}`、列 2 `{0,a} = {a,0}`、
列 3 `{a,0} = {0,a}`、列 4 `{0,a} = {0,a}` —— 全部平衡。 -/
theorem quadric_mem_toricIdeal :
    (MvPolynomial.X q_a0a0 * MvPolynomial.X q_0a0a
      - MvPolynomial.X q_aa00 * MvPolynomial.X q_00aa
      : MvPolynomial (Coord 4) ℝ) ∈ toricIdeal 4 := by
  have h := pair_balanced_mem_toricIdeal q_a0a0 q_0a0a q_aa00 q_00aa (by decide)
  simpa using h

/-- ★ 该二次式的次数 ≤ 4（可计算）。 -/
theorem quadric_totalDegree_le_four :
    (MvPolynomial.X q_a0a0 * MvPolynomial.X q_0a0a
      - MvPolynomial.X q_aa00 * MvPolynomial.X q_00aa
      : MvPolynomial (Coord 4) ℝ).totalDegree ≤ 4 := by
  have h := binomial_totalDegree_le_four ![q_a0a0, q_0a0a] ![q_aa00, q_00aa] (by norm_num)
  simpa [Fin.prod_univ_two] using h

/-! ### 4.2 `K₁,₃` 的三次不变量（SS2005 2242–2258 行的合法提升） -/

/-- 坐标 `q_{000}`。 -/
def q000 : Coord 3 := ⟨![0, 0, 0], by decide⟩

/-- 坐标 `q_{(a,b,c)}`（三个非平凡元各一次，`a+b+c = 0`）。 -/
def q_abc : Coord 3 := ⟨![aG, bG, cG], by decide⟩

/-- 坐标 `q_{(b,c,a)}`（同一个「模式类」，模去线性不变量后与 `q_abc` 同类）。 -/
def q_bca : Coord 3 := ⟨![bG, cG, aG], by decide⟩

/-- 坐标 `q_{(0,c,c)}`（模式 `011`）。 -/
def q_0cc : Coord 3 := ⟨![0, cG, cG], by decide⟩

/-- 坐标 `q_{(a,0,a)}`（模式 `101`）。 -/
def q_a0a : Coord 3 := ⟨![aG, 0, aG], by decide⟩

/-- 坐标 `q_{(b,b,0)}`（模式 `110`）。 -/
def q_bb0 : Coord 3 := ⟨![bG, bG, 0], by decide⟩

/-- ★★ **`K₁,₃` 上的显式三次不变量**（SS2005 2242–2258 行那个三次式的**合法提升**）：

`q_{000} · q_{(a,b,c)} · q_{(b,c,a)} − q_{(0,c,c)} · q_{(a,0,a)} · q_{(b,b,0)} ∈ I_{K₁,₃}`。

**为什么需要「提升」**：文献写的 `q000 q111² − q011 q101 q110` 是在**模去线性不变量之后**
的 5 个未知量上写的；`q111` 那一类里有两个不同的实际坐标 `q_{(a,b,c)}` 与 `q_{(b,c,a)}`，
必须用它们两个（而不是 `q_{(a,b,c)}²`）才能让**每一列的多重集**真正平衡 ——
见 `cubic_reduces_to_SS2005`。
（Python 脚本穷举确认：`m = 3` 时**不存在**平衡的**二次**二项式，三次的则有 1152 个有序对。） -/
theorem cubic_mem_toricIdeal :
    (MvPolynomial.X q000 * MvPolynomial.X q_abc * MvPolynomial.X q_bca
      - MvPolynomial.X q_0cc * MvPolynomial.X q_a0a * MvPolynomial.X q_bb0
      : MvPolynomial (Coord 3) ℝ) ∈ toricIdeal 3 := by
  have h := balanced_binomial_mem_toricIdeal ![q000, q_abc, q_bca] ![q_0cc, q_a0a, q_bb0]
    (by decide)
  simpa [Fin.prod_univ_three] using h

/-- ★ 该三次式的次数 ≤ 4（可计算）。 -/
theorem cubic_totalDegree_le_four :
    (MvPolynomial.X q000 * MvPolynomial.X q_abc * MvPolynomial.X q_bca
      - MvPolynomial.X q_0cc * MvPolynomial.X q_a0a * MvPolynomial.X q_bb0
      : MvPolynomial (Coord 3) ℝ).totalDegree ≤ 4 := by
  have h := binomial_totalDegree_le_four ![q000, q_abc, q_bca] ![q_0cc, q_a0a, q_bb0]
    (by norm_num)
  simpa [Fin.prod_univ_three] using h

/-- ★★ **三次式降到 SS2005 的写法**：把 `L`-标号（`0 ↦ 0`，非零 ↦ `1`）作用在三个坐标上，
左边两个非平凡行都映到模式 `111`、右边三行分别映到 `011`、`101`、`110`。

即本文件的显式三次式在「模去线性不变量」的商环里正是文献的
`q000 q111² − q011 q101 q110`（SS2005 2242–2258 行）。 -/
theorem cubic_reduces_to_SS2005 :
    (List.ofFn fun i : Fin 3 => if q_abc.1 i = 0 then (0 : ℕ) else 1)
      = [1, 1, 1]
    ∧ (List.ofFn fun i : Fin 3 => if q_bca.1 i = 0 then (0 : ℕ) else 1)
      = [1, 1, 1]
    ∧ (List.ofFn fun i : Fin 3 => if q_0cc.1 i = 0 then (0 : ℕ) else 1)
      = [0, 1, 1]
    ∧ (List.ofFn fun i : Fin 3 => if q_a0a.1 i = 0 then (0 : ℕ) else 1)
      = [1, 0, 1]
    ∧ (List.ofFn fun i : Fin 3 => if q_bb0.1 i = 0 then (0 : ℕ) else 1)
      = [1, 1, 0]
    ∧ (List.ofFn fun i : Fin 3 => if q000.1 i = 0 then (0 : ℕ) else 1)
      = [0, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## 5. ★★ 反空真（anti-vacuity） -/

/-- ★★ **toric 理想是真理想**：坐标变量 `X g` 不在 `ker φ` 里（φ 把它送到非零单项式）。
反空真：这说明「平衡 ⟹ 在理想里」这句话不是「一切都是不变量」。 -/
theorem toricIdeal_ne_top (m : ℕ) : toricIdeal m ≠ ⊤ := by
  intro h
  have hmem : (MvPolynomial.X (⟨fun _ => 0, by simp⟩ : Coord m)) ∈ toricIdeal m := by
    rw [h]; exact Submodule.mem_top
  rw [toricIdeal, RingHom.mem_ker] at hmem
  change phi m (MvPolynomial.X (⟨fun _ => 0, by simp⟩ : Coord m)) = 0 at hmem
  rw [phi_X] at hmem
  have hne : monomialOf m (fun _ => (0 : G4)) ≠ 0 := by
    rw [monomialOf]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero _
  exact hne hmem

/-- ★★ **平衡条件的假设非空真**：`K₁,₄` 的二次例子里，两组坐标 `A ≠ B`，
且列多重集平衡确实成立。 -/
theorem balanced_hypothesis_nonvacuous :
    ∃ A B : Fin 2 → Coord 4, A ≠ B
      ∧ (∀ i, (Finset.univ.val.map fun k => (A k).1 i)
          = (Finset.univ.val.map fun k => (B k).1 i)) :=
  ⟨![q_a0a0, q_0a0a], ![q_aa00, q_00aa],
    by decide, by decide⟩

/-- 用于**分离**两个单项式的具体赋值：`q_aa00`、`q_00aa ↦ 2`，其余坐标 `↦ 1`。
（注意：不能用 `φ` 来分离 —— 平衡条件说的正是 `φ` 在两边**取同一个单项式**。） -/
def quadPoint : Coord 4 → ℝ := fun g => if g = q_aa00 ∨ g = q_00aa then 2 else 1

theorem quadPoint_a0a0 : quadPoint q_a0a0 = 1 := by
  have h1 : ¬ (q_a0a0 = q_aa00) := by decide
  have h2 : ¬ (q_a0a0 = q_00aa) := by decide
  simp [quadPoint, h1, h2]

theorem quadPoint_0a0a : quadPoint q_0a0a = 1 := by
  have h1 : ¬ (q_0a0a = q_aa00) := by decide
  have h2 : ¬ (q_0a0a = q_00aa) := by decide
  simp [quadPoint, h1, h2]

theorem quadPoint_aa00 : quadPoint q_aa00 = 2 := by simp [quadPoint]

theorem quadPoint_00aa : quadPoint q_00aa = 2 := by simp [quadPoint]

/-- ★★ **二次式非零**（说明 `quadric_mem_toricIdeal` 不是「`0 ∈ I`」这种平凡结论，
也说明 toric 理想确实含有**非零**元素）。

证明：在环同态 `eval quadPoint` 下两个单项式分别取 `1 · 1` 与 `2 · 2`，故多项式像为 `−3 ≠ 0`。 -/
theorem quadric_ne_zero :
    (MvPolynomial.X q_a0a0 * MvPolynomial.X q_0a0a
      - MvPolynomial.X q_aa00 * MvPolynomial.X q_00aa
      : MvPolynomial (Coord 4) ℝ) ≠ 0 := by
  intro h
  have h2 : MvPolynomial.eval quadPoint
      ((MvPolynomial.X q_a0a0 * MvPolynomial.X q_0a0a
        - MvPolynomial.X q_aa00 * MvPolynomial.X q_00aa : MvPolynomial (Coord 4) ℝ)) = 0 := by
    rw [h, map_zero]
  rw [map_sub, map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
    MvPolynomial.eval_X, MvPolynomial.eval_X, quadPoint_a0a0, quadPoint_0a0a,
    quadPoint_aa00, quadPoint_00aa] at h2
  norm_num at h2

/-! ## 6. 诚实边界（显式缺口） -/

/-- **缺口（I7 的核心）**：SS2005 **Theorem 2（278–290 行）＋ Theorem 21（1335 行）＋
Theorem 24（1709–1734 行）**：JC DNA 模型的 toric 理想由（沿边的二次 + 沿顶点的三次）
二项式**生成** —— 因而由**次数 ≤ 4** 的多项式生成（`(b)` 说 1,2,3；`(c)` K2P 说 1,2,3,4；
`(d)` K3P 说 2,3,4）。

形式化版本：`toricIdeal m` 等于「其中次数 ≤ 4 的元素」生成的理想。

**缺什么**：SS2005 §4–§5 的 Gröbner 基 / Markov 基机器（Lemma 12 的 `Ext` 扩张、
Remark 16 的必要性方向、Theorem 21/24 的局部生成元装配）。库内没有 `MvPolynomial` 的
Gröbner 基层可用（`Mathlib/RingTheory/MvPolynomial/Groebner.lean` 存在，但本批未使用：
它需要 `MonomialOrder` 层与 `Ideal` 的消元论证，属于独立的大工程）。
**本文件只证 `⊇` 方向对已写下的二项式成立（`balanced_binomial_mem_toricIdeal`），
`=` 方向如实落缺口。** -/
def toricIdeal_generated_in_degree_le_four_gap (m : ℕ) : Prop :=
  toricIdeal m
    = Ideal.span {g : MvPolynomial (Coord m) ℝ | g ∈ toricIdeal m ∧ g.totalDegree ≤ 4}

/-- 缺口的**已证半边**：`⊇` 方向恒成立（低次元素生成的理想含于原理想）。 -/
theorem toricIdeal_gap_forward (m : ℕ) :
    Ideal.span {g : MvPolynomial (Coord m) ℝ | g ∈ toricIdeal m ∧ g.totalDegree ≤ 4}
      ≤ toricIdeal m :=
  Ideal.span_le.mpr fun _ hg => hg.1

end Phylo.Stat.ToricIdeals
