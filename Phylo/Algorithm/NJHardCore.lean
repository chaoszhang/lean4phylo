/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.LeafStatus
import Phylo.CherryQuartet
-- T0.3 收口的**最后一步（无条件形式）**（HANDOVER.md:231 的 ★★★ `maxZCherryCore`）需要两件弹药：
-- ★★★ `exists_realizingPhylogram_pos_of_addConst`（`δ.addConst ε` 的**全正**实现树，(A2) 器械层）
-- 与 `addConst` 的代数件（★★★ `z_addConst` / ★★ `fourSum_addConst` / ★★ `fourPoint_addConst`）。
import Phylo.DissimilarityPerturb
import Phylo.PhylogramContract

/-!
# `Phylo.Algorithm.NJHardCore` —— T0.3 步骤 C 的**桥接层**（`δ` 层 ↔ 树层）

**动机**：`Phylo/Algorithm/NJ.lean` 的 ★ 硬核 `Dissimilarity.MaxZCherryCore` 目前是 `def` 缺口
（`nj_cherry` 以它为假设）。Weller (2023) 的 leaf-status 论证要把它接到**实现树**上，
而 Weller 的 `ℓ_T(u)`（叶状态）、`ℓ_T(p)`（路径叶状态）在纯 `δ` 层没有对应物 ——
本文件把两者**逐点对齐**：

* ★★ `S_eq_leafStatus` —— `δ.S u = ℓ_T(leaf u)`；
* ★★★ `ell_eq_pathLeafStatus` —— `δ.ell u v = ℓ_T(p_{uv})`（对照 Weller **Observation 2**）；
* ★★★ `z_eq_dist_add_pathLeafStatus` —— `δ.z u v = d(u,v) + ℓ_T(p_{uv})`
  （Weller **eq (3)** 的树层形式）。

最后一条是 **Lemma 3 / Thm 2 的接口**：`δ.z u v ≤ ℓ_T(w)` 正是它的另一写法
（`Phylogram.dist_add_pathLeafStatus_le_leafStatus`，`w` 在 `u–v` 路径上即可）。

## 证明路线（全是定义对齐）

`δ.S` / `δ.ell` 与 `Phylogram.leafStatus` / `Phylogram.pathLeafStatus` 逐项相等
（`Finset.sum_congr` + `hT : d(leaf x, leaf y) = δ.val x y`）；
`δ.ell` / `δ.z` 再经库里已有的 ★★ `Dissimilarity.ell_eq_S`、
★★★ `Phylogram.pathLeafStatus_eq`（Weller Observation 2，需正边权）对齐。

## 状态

* ✅ ★★ `NJ.Dissimilarity.S_eq_leafStatus`
* ✅ ★★★ `NJ.Dissimilarity.ell_eq_pathLeafStatus`
* ✅ ★★★ `NJ.Dissimilarity.z_eq_dist_add_pathLeafStatus`（**零 `sorry` / 零 `axiom`**）
* ✅ ★★★ `maxZCherryCore_of_pos`（T0.8 兜底）
* ✅ ★★ `maxZCherryCore_of_card_le_three`（T0.8）
* ✅ ★★ `maxZCherryCore_of_pos'`（T0.8）
* ✅ ★★★ **`maxZCherryCore_of_exists_pos`（T0.3 收口：度量层 = 「存在全正实现树 ⟹ `MaxZCherryCore`」，
  `def` 缺口正式变成定理；正权假设显式化，理由与反例见该定理 docstring）**
* ✅ ★★ `HasPositiveRealization`（正权实现树，可复用命题名）
* ✅ ★★★ `maxZCherryCore_of_hasPositiveRealization`
* ✅ ★★ `max_z_gives_split_of_hasPositiveRealization`（**T0.3 step D**：`hcore`-自由版）
* ✅ ★★★ `nj_cherry_of_hasPositiveRealization`（**T0.3 step D 主接口**：`hcore` 从下游接口上摘掉）
* ✅ ★★★ `maxZCherryCore`（🏆 **T0.3 终局**：`MaxZCherryCore` 的**无条件**形式
  `theorem maxZCherryCore (δ) : δ.MaxZCherryCore`，`HANDOVER.md:231` W2b 的验收原文 ——
  **无** `HasPositiveRealization` / 无基数假设 / 无 `∃ 树`。路线 = ★★★ `exists_realizingPhylogram_pos_of_addConst`
  （`δ+1` 的全正实现树）→ ★★★ `maxZCherryCore_of_pos`（`(δ+1).MaxZCherryCore`）
  → ★★★ `z_addConst` + ★★ `fourSum_addConst` + ★★ `fourPoint_addConst`（shift-不变性，搬回 `δ`），
  `|X| ≤ 3` 走 ★★ `maxZCherryCore_of_card_le_three`。详见该定理 docstring）
-/


universe u v

namespace NJ

namespace Dissimilarity

open Finset
open scoped BigOperators

variable {X : Type u} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- ★★ **实现树上：`δ.S` 就是该叶的叶状态**。

`δ.S u = ∑_k δ(u,k)`（对**标签**求和）与 `ℓ_T(leaf u) = ∑_x d(leaf u, leaf x)`（对**叶**求和）
逐项相同：本库的叶恰是 `X` 的像（`T.leaf : X ↪ V`），且 `x = u` 项为 `0`。 -/
theorem S_eq_leafStatus (δ : Dissimilarity X) {T : Phylogram.{u, v} X}
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) (u : X) :
    δ.S u = T.leafStatus (T.leaf u) := by
  show (∑ k, δ.val u k) = T.leafStatus (T.leaf u)
  rw [Phylogram.leafStatus_def]
  exact Finset.sum_congr rfl fun x _ => (hT u x).symm

omit [DecidableEq X] in
/-- 辅助（对任意端点都成立）：`δ.ell` 的**代数恒等式**部分 —— 与 Weller 的 `u ≠ v` 语境无关。 -/
private theorem ell_eq_pathLeafStatus_aux (δ : Dissimilarity X) {T : Phylogram.{u, v} X}
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) {u v : X} (_huv : u ≠ v) :
    δ.ell u v = T.pathLeafStatus (T.leaf u) (T.leaf v) := by
  rw [ell_eq_S, Phylogram.pathLeafStatus_eq T hpos,
    S_eq_leafStatus δ hT u, S_eq_leafStatus δ hT v, ← hT u v]

omit [DecidableEq X] in
/-- ★★★ **实现树上：`δ.ell u v` 就是 `u–v` 路径的路径叶状态 `ℓ_T(p)`**（Weller Obs 2 的
`δ` 层对照）。

左边用 ★★ `Dissimilarity.ell_eq_S`，右边用 ★★★ `Phylogram.pathLeafStatus_eq`
（Observation 2，需正边权），再用 `S_eq_leafStatus` 与 `hT` 把两侧的 `S`、`δ` 换成 `ℓ_T`、`d`。

⚠️ `huv : u ≠ v` 是 Weller 的语境假设（「`p` 是真正的路径，两端为不同叶」）；
上式的**代数恒等式**对任意 `u,v` 都成立（见辅助引理 `ell_eq_pathLeafStatus_aux`），
此参数为**签名兼容**保留（T0.3 调用方按「`u ≠ v`」调用），并在此处经它转发下去。 -/
theorem ell_eq_pathLeafStatus (δ : Dissimilarity X) {T : Phylogram.{u, v} X}
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) {u v : X} (huv : u ≠ v) :
    δ.ell u v = T.pathLeafStatus (T.leaf u) (T.leaf v) :=
  ell_eq_pathLeafStatus_aux δ hpos hT huv

omit [DecidableEq X] in
/-- ★★★ **实现树上 `δ.z u v = d(u,v) + ℓ_T(p_{uv})`**（Weller eq (3) 的树层形式）。

`δ.z = δ.val + δ.ell` 逐项展开，再用 `hT` 与 `ell_eq_pathLeafStatus`。

**这是 Lemma 3 / Thm 2 的接口**：`δ.z u v ≤ ℓ_T(w)` 正是该式的另一写法
（`Phylogram.dist_add_pathLeafStatus_le_leafStatus`，`w` 在 `u–v` 路径上即可）。 -/
theorem z_eq_dist_add_pathLeafStatus (δ : Dissimilarity X) {T : Phylogram.{u, v} X}
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) {u v : X} (huv : u ≠ v) :
    δ.z u v = T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v) := by
  show δ.val u v + δ.ell u v
    = T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v)
  rw [ell_eq_pathLeafStatus δ hpos hT huv, ← hT u v]

-- ===== T08 BEGIN =====
/-! ## T0.8 兜底：`MaxZCherryCore` 在「有**正权实现树**」的假设下**成立** -/

/-- ★★★ **`MaxZCherryCore` 在「有正权实现树」的假设下成立**（T0.3 的兜底形式）。

设 `δ` 由一棵**正边权**的 `Phylogram` `T` 实现（`hT : d(leaf x, leaf y) = δ.val x y`），
且 `4 ≤ |X|`，则 ★ 硬核 `Dissimilarity.MaxZCherryCore` **是定理**（不再作为假设）。

证明（`δ` 层 ↔ 树层三条桥接引理 + Weller Thm 2 + 樱桃的 quartet 不等式）：

1. ★★★ `z_eq_dist_add_pathLeafStatus` 把 `hmax`（关于 `δ.z` 的最大性）**翻译到树层**；
2. ★★★ `Cladogram.exists_isCherry_of_max_z`（Weller **Thm 2**，需正边权与 `3 ≤ |X|`）给出
   `T.IsCherry a b`；
3. ★★★ `Cladogram.dist_add_le_of_isCherry` 给出**树层**两条 quartet 不等式；
4. 再用 `hT` 把它们**搬回 `δ` 层**。

⚠️ `hfp : δ.FourPoint` 在本路线中**未被使用**（`δ` 直接由树实现，四点条件自动成立）；
为签名兼容保留为**匿名假设**。 -/
theorem maxZCherryCore_of_pos {X : Type u} [Fintype X] [DecidableEq X] (δ : Dissimilarity X)
    {T : Phylogram.{u, v} X} (hcard : 4 ≤ Fintype.card X)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    δ.MaxZCherryCore := by
  intro _ a b hab hmax i j hij hia hib hja hjb
  -- ① `δ.z` 的最大性 ⟹ 树层 `d + ℓ` 的最大性
  have hmaxT : ∀ p q : X, p ≠ q →
      T.dist (T.leaf p) (T.leaf q) + T.pathLeafStatus (T.leaf p) (T.leaf q) ≤
        T.dist (T.leaf a) (T.leaf b) + T.pathLeafStatus (T.leaf a) (T.leaf b) := by
    intro p q hpq
    have h := hmax p q hpq
    rwa [z_eq_dist_add_pathLeafStatus δ hpos hT hpq,
      z_eq_dist_add_pathLeafStatus δ hpos hT hab] at h
  -- ② Weller Thm 2（★★★）：`z` 最大的一对叶是樱桃
  have hc : T.IsCherry a b :=
    Cladogram.exists_isCherry_of_max_z hpos (by omega) hab hmaxT
  -- ③ 樱桃的 quartet 不等式（树层）
  have hle := Cladogram.dist_add_le_of_isCherry hc hia hib hja hjb hij
  -- ④ 搬回 `δ` 层
  exact ⟨by rw [← hT a b, ← hT i j, ← hT a i, ← hT b j]; exact hle.1,
    by rw [← hT a b, ← hT i j, ← hT a j, ← hT b i]; exact hle.2⟩

/-- ★★ **基数 ≤ 3 时 `MaxZCherryCore` 空真**：结论要求 4 个互异点 `a, b, i, j`
（`a ≠ b`、`i ≠ j`、`i,j ∉ {a,b}`），故 `4 ≤ |X|` 是结论的**必要条件**；
与 `h : |X| ≤ 3` 矛盾（经 `Finset.card_le_card` + `Finset.card_eq_four`）。

与 ★★★ `maxZCherryCore_of_pos` 合起来**覆盖全部基数**。 -/
theorem maxZCherryCore_of_card_le_three {X : Type u} [Fintype X] [DecidableEq X]
    (δ : Dissimilarity X) (h : Fintype.card X ≤ 3) : δ.MaxZCherryCore := by
  intro _ a b hab _ i j hij hia hib hja hjb
  have hs : ({a, b, i, j} : Finset X).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨a, b, i, j, hab, hia.symm, hja.symm, hib.symm, hjb.symm, hij, rfl⟩
  have hle : 4 ≤ Fintype.card X := by
    have hsub := Finset.card_le_card (Finset.subset_univ ({a, b, i, j} : Finset X))
    rwa [hs, Finset.card_univ] at hsub
  exact absurd hle (by omega)

/-- ★★ **无基数条件的合并形式**：`MaxZCherryCore` 由**正权实现树**直接给出，
`|X| ≤ 3` 与 `4 ≤ |X|` 两种情形分别归约到
★★ `maxZCherryCore_of_card_le_three` 与 ★★★ `maxZCherryCore_of_pos`。

（这是 T0.3 收口时最省事的一条接口。） -/
theorem maxZCherryCore_of_pos' {X : Type u} [Fintype X] [DecidableEq X] (δ : Dissimilarity X)
    {T : Phylogram.{u, v} X}
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    δ.MaxZCherryCore := by
  by_cases hcard : 4 ≤ Fintype.card X
  · exact maxZCherryCore_of_pos δ hcard hpos hT
  · exact maxZCherryCore_of_card_le_three δ (by omega)

/-- ★★★ **T0.3 收口的度量层形态（正权假设显式）**：只要 `δ` **存在**一棵边权全正的实现树，
`δ.MaxZCherryCore` 就是**定理**（不再有 `def` 缺口）。

这正是 Weller (2023) **Thm 2** 在「显式带正权假设」下的写法：Weller `:397–399` 自述其证明
只要求**正权边**，而本库 `Phylogram.w_nonneg` 只给 `≥ 0` ⇒ 正权**必须**作为假设
（HANDOVER §4.2 T0.3 缺口③ 的原话：「T0.3 的定理必须显式带正权假设」）。

⚠️ **「无条件」形式（去掉 `∃ T` 假设）不属于文献内容**，且朴素路线**已被反例堵死**：
对星形度量 `ρ = (ρ_p,ρ_q,ρ_r,ρ_x) = (1,1,3,0)` 取 `ε = 1`、`δ_ε := δ.addConst 1`
（六条距离 `pq=3, pr=5, qr=5, xp=2, xq=2, xr=4`），**T0.2 的构造**给出的实现树含 **0 权内边**
（`t—t'` 权为 `0`，且第 0 层三个并列极大三元组、第 1 层两个并列选择**都躲不掉**）
⇒ 「T0.2 的构造作用在 `δ_ε` 上各边全正」是**假命题**，不要再证。
但**该度量确有全正实现树**：四叶星 `x : ½, p : 3/2, q : 3/2, r : 7/2`（六条距离逐条验过）
⇒ 无条件命题**可能仍真**，只是需要超出文献的新工作（把 0 权内边收缩掉，或改造树层的 Thm 2 论证）。
🔎 独立脚本实证（400 组随机树度量，含大量 0 权边，穷举全部并列选择 = 9244 次构造，0 次未实现 `δ_ε`）：
`δ_ε` 下 T0.2 的构造**从不**给**实标签**（`X` 的 `Sum.inl`）0 权挂边 —— 0 权只出现在
**合成点**（`Sum.inr ()`，即 shrink 造出的新点）之间，而合成点在最终树里都是内部点
⇒ 打磨这条「实标签挂边恒正 + 收缩合成点间 0 权内边」即可得无条件形式（工作量 = 图收缩器械）。

✅ **2026-10-08 更新：这条「无条件形式」已经做完** —— 上面的「图收缩器械」已由
`Phylo/PhylogramContract.lean` + `Phylo/ContractCount.lean` 的 (A2) 层兑现
（★★★ `exists_realizingPhylogram_pos_of_addConst`：`δ.FourPoint → 4 ≤ |X| → 0 < ε →`
`δ.addConst ε` 有**边权全正**的实现树），其「搬回 `δ`」的一步由本文件末尾的
★★★ `maxZCherryCore` 用 `addConst` 的 shift-不变性（★★★ `z_addConst` + ★★ `fourSum_addConst`）完成
⇒ **`MaxZCherryCore` 已是无条件定理**（`HANDOVER.md:231` 的验收达成）。
本节的条件版本保留：它们是 ★★★ `maxZCherryCore` 的构造性中间件，也是下游 `_of_hasPositiveRealization`
一族（T0.3 step D）的依据。 -/
theorem maxZCherryCore_of_exists_pos (δ : Dissimilarity X)
    (h : ∃ T : Phylogram.{u, v} X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
      ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    δ.MaxZCherryCore := by
  obtain ⟨T, hpos, hT⟩ := h
  exact maxZCherryCore_of_pos' δ hpos hT

/-! ## T0.3 step D：把 `hcore` 假设从 NJ 的接口上摘掉

`Phylo/Algorithm/NJ.lean` 的 ★★ `max_z_gives_split` 与 ★★★ `nj_cherry` 都以
`hcore : δ.MaxZCherryCore`（那个 `def` 缺口）为**显式假设**。本节的封装把它们换成
**文献形态的假设**「`δ` 有一棵每条边权都严格为正的实现树」（= Weller 2023 Thm 2 的前提，
也 = ADR 2016 里物种树的「binary 且内部边长全正」），于是 `MaxZCherryCore` 这个 `def`
**不再出现在下游接口上**（HANDOVER §4.2 T0.3 的「D 步」）。

⚠️ **为什么不在 `NJ.lean` 里直接改签名**：`NJ.lean` 不能 import 本文件（本文件 import `NJ`，会成环），
故 `hcore`-自由版只能住在 NJ 之上 —— 就是本节。 -/

/-- ★★ **正权实现树**（T0.3 的文献形态假设，可复用的命题名）。 -/
def HasPositiveRealization (δ : Dissimilarity X) : Prop :=
  ∃ T : Phylogram.{u, v} X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
    ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y

/-- ★★★ **`HasPositiveRealization ⟹ MaxZCherryCore`**（= ★★★ `maxZCherryCore_of_exists_pos` 的打包形式）。 -/
theorem maxZCherryCore_of_hasPositiveRealization (δ : Dissimilarity X)
    (h : δ.HasPositiveRealization) : δ.MaxZCherryCore :=
  maxZCherryCore_of_exists_pos δ h

/-- ★★ **`max_z_gives_split` 的 `hcore`-自由版**：假设换成「正权实现树」。 -/
theorem max_z_gives_split_of_hasPositiveRealization (δ : Dissimilarity X)
    (h : δ.HasPositiveRealization) (hcard : 4 ≤ Fintype.card X) (hfp : δ.FourPoint)
    (a b : X) (hab : a ≠ b)
    (hmax : ∀ i j : X, i ≠ j → δ.z i j ≤ δ.z a b) :
    ∀ i j : X, i ≠ j → i ≠ a → i ≠ b → j ≠ a → j ≠ b →
      δ.val a b + δ.val i j ≤ δ.val a i + δ.val b j ∧
      δ.val a b + δ.val i j ≤ δ.val a j + δ.val b i :=
  max_z_gives_split δ (maxZCherryCore_of_hasPositiveRealization δ h) hcard hfp a b hab hmax

/-- ★★★ **`nj_cherry` 的 `hcore`-自由版**（T0.3 step D 的主接口）：
「`δ` 满足四点条件 + 有正权实现树 + `(a,b)` 最小化 `Q` ⟹ `(a,b)` 是樱桃」，
**不再需要把 `MaxZCherryCore` 当假设**。 -/
theorem nj_cherry_of_hasPositiveRealization (δ : Dissimilarity X)
    (h : δ.HasPositiveRealization) (hfp : δ.FourPoint)
    (a b : X) (hab : a ≠ b)
    (hmin : ∀ i j : X, i ≠ j → δ.Q a b ≤ δ.Q i j) :
    δ.IsCherry a b :=
  nj_cherry δ (maxZCherryCore_of_hasPositiveRealization δ h) hfp a b hab hmin

-- ===== T08 END =====

-- ===== W2b FINAL STEP BEGIN =====
/-! ## T0.3 收口（**无条件形式**）：`MaxZCherryCore` 由 `def` 缺口变成**无条件定理**

**验收原文**（`HANDOVER.md:231`，W2b 一行，逐字）：

```lean
theorem maxZCherryCore (δ) : δ.MaxZCherryCore
```

**无** `HasPositiveRealization`、**无** `∃ 正权实现树`、**无**基数假设。下面的 ★★★ `maxZCherryCore`
就是它的形式（`{X} [Fintype X] [DecidableEq X]` 是 `Dissimilarity X` 自身的类型类要求，
不是额外假设；`δ.FourPoint` 是 `MaxZCherryCore` **定义内部**的前提，不是新假设）。

## 路线：`addConst` 的 **shift-不变性**（把 `δ+ε` 的结果搬回 `δ`）

此前记录为「扰动法 / `ℓ` 改造已判死」的是**另外两件事**（见 `HANDOVER.md:201–204` 的两条判死记录）：
「拿 T0.2 的构造树直接吃 `hpos`」（反例作废）与「改造树层的 `ℓ` 论证」（`hpos` 贯穿 `LeafStatus`
20+ 条定理）。本节**两者都没用**：走的是派单指定的另一条通道 —— `HANDOVER.md:46-51` 所述的
「把 `δ+ε` 的正性搬回 `δ`」，即 `addConst` 的 **shift-不变性**。
而「收缩 0 权内边」这条通道也已由 ★★★ `exists_realizingPhylogram_pos_of_addConst`（(A2) 器械）兑现，
于是只差平移：

1. 取 `ε = 1`，★★★ `exists_realizingPhylogram_pos_of_addConst` 给出 `δ+1` 的**边权全正**实现树 `T`；
2. ★★★ `maxZCherryCore_of_pos`（Weller Thm 2 的树层论证作用在 `T` 上）给出 `(δ+1).MaxZCherryCore`；
3. ★★★ `z_addConst`：`z_{δ+1}(i,j) = z_δ(i,j) + (|X|/2)·1` —— 平移量**与 `i j` 无关**
   ⇒ `δ` 的 `z`-最大化对在 `δ+1` 里**仍是**最大化对；★★ `fourPoint_addConst` 给 `(δ+1).FourPoint`；
4. ★★ `fourSum_addConst`：quartet 不等式两边**同步平移 `2ε`** ⇒ 对 `δ+1` 证出的不等式搬回 `δ`。

`|X| ≤ 3` 时结论要量化四个互异点 ⇒ **空真**，由 ★★ `maxZCherryCore_of_card_le_three` 收口。

## 诚实边界

* 本定理**不需要**任何超出 `MaxZCherryCore` 自身定义的前提（逐字对照见其上 docstring）。
* 唯一「非文献」的步骤是第 3 步的 shift-不变性：它是 `addConst` 的**纯代数**恒等式，
  出自本库 `Phylo/DissimilarityPerturb.lean`（★★★ `z_addConst` / ★★ `fourSum_addConst`），
  不含任何未证缺口。 -/
theorem maxZCherryCore (δ : Dissimilarity X) : δ.MaxZCherryCore := by
  by_cases hcard : 4 ≤ Fintype.card X
  · -- 主情形：经 `δ.addConst 1` 中转（(A2) 器械 + shift-不变性）
    intro hfp a b hab hmax i j hij hia hib hja hjb
    -- ① `(A2)`：`δ + 1` 有**边权全正**的实现树
    obtain ⟨T, hpos, hT⟩ :=
      Phylo.Contract.exists_realizingPhylogram_pos_of_addConst δ hfp hcard (ε := 1) (by norm_num)
    -- ② Weller Thm 2（树层）⇒ `(δ+1).MaxZCherryCore`
    have hcore : (δ.addConst 1).MaxZCherryCore :=
      maxZCherryCore_of_pos (δ.addConst 1) hcard hpos hT
    -- ③ `z` 的平移不变性：`z`-最大化对不变；四点条件保持
    have hmax' : ∀ p q : X, p ≠ q → (δ.addConst 1).z p q ≤ (δ.addConst 1).z a b := by
      intro p q hpq
      rw [z_addConst (δ := δ) (ε := 1) (i := p) (j := q) hpq,
        z_addConst (δ := δ) (ε := 1) (i := a) (j := b) hab]
      linarith [hmax p q hpq]
    have hfp' : (δ.addConst 1).FourPoint := fourPoint_addConst δ (by norm_num) hfp
    obtain ⟨hq1, hq2⟩ := hcore hfp' a b hab hmax' i j hij hia hib hja hjb
    -- ④ 四点和同步平移 `2·1` ⇒ 搬回 `δ`
    have eab : (δ.addConst 1).val a b + (δ.addConst 1).val i j
        = δ.val a b + δ.val i j + 2 * 1 :=
      fourSum_addConst δ 1 hab hij hia hib hja hjb
    have eai : (δ.addConst 1).val a i + (δ.addConst 1).val b j
        = δ.val a i + δ.val b j + 2 * 1 :=
      fourSum_addConst δ 1 hia.symm hjb.symm hab.symm hib.symm hja hij.symm
    have eaj : (δ.addConst 1).val a j + (δ.addConst 1).val b i
        = δ.val a j + δ.val b i + 2 * 1 :=
      fourSum_addConst δ 1 hja.symm hib.symm hab.symm hjb.symm hia hij
    refine ⟨?_, ?_⟩
    · rw [eab, eai] at hq1; linarith
    · rw [eab, eaj] at hq2; linarith
  · -- 退化情形 `|X| ≤ 3`：结论空真
    exact maxZCherryCore_of_card_le_three δ (by omega)

-- ===== W2b FINAL STEP END =====

end Dissimilarity

end NJ
