/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERD

/-!
# `Phylo.Stat.CASTERFourPoint` —— `n = 4` 的四点不等式（W44 · L4.1）

文献：`references/CASTER_NJ_2026-11-04.md` §5.2（定理 5）。

## 内容

`S = {x,y,z,w}`、真拓扑 `xy|zw`、A4（`f ≡ c`）。`n = 4` 时每个 `D_ab` 只有一个求和项，
故由 L3（`Dtilde_eq`）直接得四个 `D̃` 的取值（`ε` 表：真拓扑 `+1`、另两张 `−1/2`）：

```text
D̃_xy = α c W_z W_w · (+1)      D̃_zw = α c W_x W_y · (+1)
D̃_xz = α c W_y W_w · (−1/2)    D̃_yw = α c W_x W_z · (−1/2)
```

于是

```text
Δ := D̃_xy + D̃_zw − D̃_xz − D̃_yw = α c ( W_z W_w + W_x W_y + ½W_y W_w + ½W_x W_z ) > 0 .
```

本文件把这条拆成两块：**代数恒等式**（`fourPoint_n4_eq`，`ring`）＋**严格正性**
（`fourPoint_n4_pos`，`positivity`）。`α > 0`、`c > 0`、`W > 0` 都是**显式假设**
（文档 A1–A4 的算术部分），没有藏进证明。

⚠️ 诚实边界：`Δ` 与四个 `D̃` 的**相等**依赖 L3 与 A1–A3（`ε` 表），本文件把
「四个 `D̃` 恰为上面那四式」作为**显式前提** `hD` 传入，不假装已从模型推出。
-/

namespace Phylo.Stat.CASTERFourPoint

/-- 
 = 4 时的 Δ（四个 D̃ 的显式组合；ε 表已代入：真拓扑 +1、另两张 −1/2）。 -/
noncomputable def casterDelta4 (α c Wx Wy Wz Ww : ℝ) : ℝ :=
  (α * c * Wz * Ww) + (α * c * Wx * Wy)
    - (-(1 / 2) * (α * c * Wy * Ww)) - (-(1 / 2) * (α * c * Wx * Wz))

/-- ★★ **L4.1（代数恒等式）**：把 `n = 4` 的四个 `D̃` 代入 `Δ`，等于文档定理 5 的显式公式。 -/
theorem fourPoint_n4_eq (α c Wx Wy Wz Ww : ℝ) :
    casterDelta4 α c Wx Wy Wz Ww
      = α * c * (Wz * Ww + Wx * Wy + (1 / 2) * (Wy * Ww) + (1 / 2) * (Wx * Wz)) := by
  simp only [casterDelta4]; ring

/-- ★★★ **L4.1（文档定理 5）**：`n = 4`、`f ≡ c` 时 Δ **严格为正**。

四个 `ε` 值取自 A1–A3 的表（真拓扑 `+1`、另两张 `−1/2`）——由 `hD` 显式传入。 -/
theorem fourPoint_n4_pos (α c Wx Wy Wz Ww : ℝ) (hα : 0 < α) (hc : 0 < c)
    (hx : 0 < Wx) (hy : 0 < Wy) (hz : 0 < Wz) (hw : 0 < Ww)
    (hD : casterDelta4 α c Wx Wy Wz Ww
      = α * c * (Wz * Ww + Wx * Wy + (1 / 2) * (Wy * Ww) + (1 / 2) * (Wx * Wz))) :
    0 < casterDelta4 α c Wx Wy Wz Ww := by
  rw [hD]
  have h1 : 0 < α * c := mul_pos hα hc
  have h2 : 0 < Wz * Ww := mul_pos hz hw
  have h3 : 0 < Wx * Wy := mul_pos hx hy
  have h4 : 0 < Wy * Ww := mul_pos hy hw
  have h5 : 0 < Wx * Wz := mul_pos hx hz
  nlinarith [mul_pos h1 (by linarith : (0 : ℝ) < Wz * Ww + Wx * Wy
    + (1 / 2) * (Wy * Ww) + (1 / 2) * (Wx * Wz))]

end Phylo.Stat.CASTERFourPoint
