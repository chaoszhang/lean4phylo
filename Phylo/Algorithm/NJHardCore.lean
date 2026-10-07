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

end Dissimilarity

end NJ
