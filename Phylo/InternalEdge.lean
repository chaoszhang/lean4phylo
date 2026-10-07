/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SideSubtree
import Phylo.Algorithm.Cherry

/-!
# `Phylo.InternalEdge` —— 内部边两侧各含 ≥ 2 叶（`SideSubtree` 阶段 2）

`Phylo/SideSubtree.lean` 已证「边的侧分量诱导一棵子树」（阶段 1）。本文件补上**阶段 2**：
**`no_degree_two` 的树中，任意边（的两侧）各含 ≥ 2 个叶**。

这是 HANDOVER §3 / §4 的 **T2** —— 「T1 第 1 步 / quartet → split 恢复 / KF 距离」三处的共同前置。

## 证明骨架（计数）

设 `U := T.sideVertices e u`（`T - e` 中含 `u` 的分量），`ℓ_U`、`i_U` 为 `U` 内的叶/内部顶点数。

1. **跨越 `U` 的边只有 `e` 本身**（`SideSubtree` 的 `eq_edge_of_adj_of_mem_sideVertices_of_notMem`）；
2. `x ∈ U`、`x ≠ u` ⟹ `x` 的邻居全在 `U ∪ {u}` 内；
   ⟹ `deg_{T[U]}(x) ≥ deg_T(x) - 1 ≥ 2`（用 `no_degree_two`：`deg_T(x) ≥ 3`）；
3. `u` 本身：`deg_{T[U]}(u) ≥ 1`（握手 + `no_degree_two` 排除 `deg=0`）；
4. 手算度数和 + 阶段 1 的 `#边 + 1 = |U|`：
   `2(|U| - 1) ≥ ℓ_U + 2(i_U - 1) + 1`；
5. 代入 `|U| = ℓ_U + i_U` 并用 `T` 的全局不等式 `ℓ ≥ i + 2` 挤出 **`ℓ_U ≥ 2`**；
6. `ℓ_U = (T.sideLeaves e u).card`。

## ⬜ 未完成：第 2 步

`neighborSet_subset_sideVertices_union`：`x ∈ U`、`x ≠ u` ⟹ `N(x) ⊆ U ∪ {u}`。

**⚠️ 不能加强成 `⊆ U`（这是假命题，务必不要试）**：
设 `T` 是路径 `u—x—w`，`e = {x,w}`，则 `U = T - e` 中 `u` 的分量含 `u, x`，
而 `x` 的邻居 `w ∉ U`。所以 `w ∈ U` 推不出来 —— 这就是我本轮反复卡住的原因。

**⚠️ 死路二**：想用「`e = s(x,w)` ⟹ 删边后 `x`、`w` 仍相邻」推 `w ∈ U`。
这是**假命题**：`Sym2.eq_swap` 给出 `s(w,x) = s(x,w)`，与 `hedge : s(x,w) = e` 合起来
**证明了** `s(w,x) = e`，即 `{x,w}` **正是**被删掉的 `e`。任何写法都推不出 `s(w,x) ∉ {e}`。

**⚠️ 死路三（等价于上面）**：想证 `u ∈ e`。同样为假：路径 `u—x—w` 中 `u` 只是 `e` 的
邻居侧的点，**不是** `e` 的端点。

**⇒ 正确的第 2 步**：直接证 `N(x) ⊆ U ∪ {u}`。
* 若邻居 `w ∈ U`：完成；
* 若 `w ∉ U`：跨越 `U` 的边只有 `e`，故 `s(x,w) = e`，即 `w` 是 `e` 的端点；
  而 `e` 的另一端 `x ∈ U`。由桥论证（`not_reachable_deleteEdges_of_adj`）：
  `x` 与 `u` 在 `T - e` 中可达、`w` 不可达 ⟹ `w = u`。

**剩下唯一的技术障碍**：从 `w ∈ e` 与 `e = s(x,w)` 推出 `w = x ∨ w = u` 时，
**`Sym2.mem_iff.mp` 会把第二个端点归一化成 `w` 自己**（因为 `w` 同时是「被提取的点」），
于是 `rcases` 的第二支给出 `w = w` 而非 `w = u`。
绕过办法（未及实施）：改用 `Sym2.eq_iff` 作用于 `s(x,w) = s(x,u)`（需先造出 `s(x,u) = e`），
或把「`w = u`」这一支排掉后再用 `Sym2.mem_iff`（此时 `w ≠ u` 已知，
`rcases` 的第一支 `w = x` 已足够给出矛盾）。
-/

open Phylo
open SimpleGraph

universe u v

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

variable (T : Cladogram.{u, v} X)

/-! ## 辅助引理（已验证） -/

/-- **`Sym2` 端点提取**：`u ∈ e`、`e = s(x,w)`、`u ≠ x` ⟹ `u = w`。 -/
theorem eq_of_mem_of_eq_pair {e : Sym2 T.V} {u x w : T.V}
    (hu : u ∈ e) (he : s(x, w) = e) (hux : u ≠ x) : u = w := by
  rw [← he] at hu
  rcases Sym2.mem_iff.mp hu with h | h
  · exact absurd h hux
  · exact h

/-- 若 `e = s(x,w)`，则 `x ∈ e`。 -/
theorem mem_pair_left {e : Sym2 T.V} {x w : T.V} (he : s(x, w) = e) : x ∈ e :=
  he ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : x ∈ s(x, w))

/-- 若 `e = s(x,w)`，则 `w ∈ e`。 -/
theorem mem_pair_right {e : Sym2 T.V} {x w : T.V} (he : s(x, w) = e) : w ∈ e :=
  he ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : w ∈ s(x, w))

/-- 由 `s(x,w) = e = s(x,u)` 与 `u ≠ x` 得 `w = u`（走 `Sym2.eq_iff`，避开 `mem_iff` 的坑）。 -/
theorem eq_right_of_eq_pair {e : Sym2 T.V} {x w u : T.V}
    (he : s(x, w) = e) (hu : e = s(x, u)) (hux : u ≠ x) : w = u := by
  rcases Sym2.eq_iff.mp (he.trans hu) with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd h1.symm hux

end Cladogram
