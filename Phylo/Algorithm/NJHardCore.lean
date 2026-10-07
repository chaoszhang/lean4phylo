/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.LeafStatus
import Phylo.CherryQuartet

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

-- ===== T08 END =====

end Dissimilarity

end NJ
