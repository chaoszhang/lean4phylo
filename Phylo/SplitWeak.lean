/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split
import Phylo.Binary
import Mathlib.Tactic

/-!
# `Phylo.SplitWeak` —— 弱相容（weak compatibility）与「4 元 3-split」障碍（W11h / X7）

文献：H.-J. Bandelt & A. W. M. Dress, *A canonical decomposition theory for metrics on a
finite set*, Advances in Mathematics **92**(1) (1992) 47–105。
文本见 `references/md/BandeltDress1992_CanonicalDecompositionMetrics.md`；
**下文行号一律指该 md 的行号**（OCR 有损；逐字引用处以 `>` 标出）。

> ⚠️ 新增 import：`Mathlib.Tactic`（本文件用到 `linarith` / `omega` / `tauto` / `ring`；
> `Phylo.Split` 只带了 `Mathlib.Tactic.FinCases`）。这是**唯一**新增的 import。

## 0. 两种「可实现性」

| | 判据 | 实现对象 | 库内零件 |
|---|---|---|---|
| **强相容** | 任意两个 split 的四个交至少一个为空 | 一棵**树**（= 满足四点条件的度量） | `Split.Compatible` / `Split.Incompatible`（`Phylo/Split.lean`、`Phylo/Binary.lean`） |
| **弱相容**（本文件） | 不存在四个点被**三个** split 按**三种**方式 2\|2 分开 | 某个对称函数 `δ` 的 **d-split 全体** | 新 |

**强 ⟹ 弱**（★★ `weaklyCompatible_of_pairwiseCompatible`），反之**不成立**——
任意两个 split 都弱相容（`weaklyCompatible_pair`），故 `{ab|cde, ac|bde}` 弱相容却不两两相容。

### 文献逐字（行号 = md 行号）

弱相容**定义**（1663–1679 行，Fig. 5）：

> "we define a collection Σ of splits of X to be **weakly compatible** if there are no four
>  points t, u, v, w ∈ X and three splits S₁, S₂, S₃ ∈ Σ such that S₁ extends the partial split
>  {t,u}, {v,w}, while S₂ extends {t,v}, {u,w}, and S₃ extends {t,w}, {v,u}."

等价写法（695–710 行）：

> "A given collection Σ of splits of X is of the form Σ = Σ_d for some metric d ∈ M(X) if and
>  only if any three splits {A₁,B₁}, {A₂,B₂}, {A₃,B₃} in Σ are weakly compatible in the
>  following sense: there are no four points a, a₁, a₂, a₃ ∈ X with {a, a_i} ⊆ A_i and
>  {a_j, a_k} ⊆ B_i for {i,j,k} = {1,2,3}."

**主定理**（1683–1699 行，Theorem 3）：

> "**THEOREM 3.** The d-splits with respect to any symmetric function d on a set X are weakly
>  compatible. Conversely, let Σ be any collection of weakly compatible splits of X. For each
>  S ∈ Σ choose some λ_S > 0 and consider d := Σ_{S∈Σ} λ_S δ_S. Then Σ is the set of all
>  d-splits, and moreover, the isolation index α_S = λ_S for each S ∈ Σ."

**d-split 的定义**（438–456 行）：

> "d(a, a') + d(b, b') < max{d(a, b) + d(a', b'), d(a, b') + d(a', b)} for all a, a' ∈ A and
>  b, b' ∈ B, that is, if and only if the **isolation index** α_{A,B} ... of A, B with respect
>  to d is **positive**."

**四点条件**（503–509 行）：

> "the two larger ones of the three expressions d(a, a') + d(b, b'), d(a, b) + d(a', b'), and
>  d(a, b') + d(a', b) are equal for all a, a', b, b' ∈ X. This condition is well known to be
>  characteristic [of] tree metrics."

**强相容 ⟺ 树度量**（539–544 行）：

> "a family Σ of splits is of the form Σ = Σ_d for some metric d satisfying the four-point
>  condition if and only if any two splits A, B and A', B' in Σ are compatible in the sense
>  that one of the four intersections A ∩ A', A ∩ B', B ∩ A', B ∩ B' is empty ..."

**典范分解**（1651–1655 行 Theorem 2；673–684 行）：

> "any metric d can be expressed in a canonical fashion as a sum of certain split metrics δ_S
>  (where S runs through all d-splits) and a split-prime residue d₀"
> "the residue d₀ := d − Σ_{S ∈ Σ_d} α_S δ_S of d with respect to its splits is always in M(X)
>  and it is **split-prime**; that is, it has isolation index 0 with respect to every split of X."

## 1. 本文件证出（零 `sorry` / `axiom` / `native_decide`）

* ★★★ `weaklyCompatible_of_isDSplit` —— Theorem 3 的**第一句**：`d`-split 全体弱相容。
  证明只用**纯 `max` 不等式** `not_all_three_deficit_pos`：三个「四点亏损」
  `α₁ = max(Y,Z) − X`、`α₂ = max(X,Z) − Y`、`α₃ = max(X,Y) − Z` 不可能同时为正。
* ★★ `weaklyCompatible_of_pairwiseCompatible` —— 强 ⟹ 弱；
  `Cladogram.weaklyCompatible_splits` —— 树的 split 系统弱相容
  （接 `pairwiseCompatible`，`Phylo/Split.lean:894`）。
* ★ 非空真：`hasConflictingQuartet_four`（`Fin 4` 上三个 2|2 split 真的冲突）；
  `weaklyCompatible_pair` + `exists_weaklyCompatible_not_pairwiseCompatible`
  （`Fin 5` 上 `{{0,1}|{2,3,4}, {0,2}|{1,3,4}}` 弱相容但**不**两两相容 ⟹ 弱是**严格**弱化）。
* ⬜ 三个显式缺口（文件末 `def … : Prop`）：Theorem 3 的**逆**、**典范分解**、四点条件刻画。

⚠️ `IsDSplit` 把「隔离指数的 `min` 为正」写成「**所有** `a,a' ∈ A`、`b,b' ∈ B` 的逐对条件」
（二者等价：`min > 0 ⟺ 全为正`），省掉 `sInf` / `Finset.min'` 的枝节。
-/

noncomputable section

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. 由「第一侧」造 split（供具体小例子使用） -/

/-- 由 `A` 造 split：`sideA = A`、`sideB = Aᶜ`（要求两侧都非空）。 -/
def ofSideA (A : Finset α) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) : Split α where
  parts := fun i => if i = (0 : Fin 2) then A else Aᶜ
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Finset.disjoint_left, Finset.mem_compl]
  union_eq_univ := by
    ext x
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    by_cases hx : x ∈ A
    · exact Finset.mem_biUnion.mpr ⟨0, by simp [hx]⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simp [hx]⟩
  nonempty := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hAc

@[simp] theorem ofSideA_sideA (A : Finset α) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (ofSideA A hA hAc).sideA = A := by
  show (if (0 : Fin 2) = 0 then A else Aᶜ) = A
  simp

@[simp] theorem ofSideA_sideB (A : Finset α) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (ofSideA A hA hAc).sideB = Aᶜ := by
  show (if (1 : Fin 2) = 0 then A else Aᶜ) = Aᶜ
  simp

/-! ## 2. 四交判据与自相容 -/

/-- 两个 split 的**四个交全非空**（`incompatible_iff` 的打包形式）。 -/
def FourIntersections (s t : Split α) : Prop :=
  (s.sideA ∩ t.sideA).Nonempty ∧ (s.sideA ∩ t.sideB).Nonempty ∧
    (s.sideB ∩ t.sideA).Nonempty ∧ (s.sideB ∩ t.sideB).Nonempty

/-- 四交全非空 ⟺ 不兼容（`Phylo/Binary.lean` 的 `incompatible_iff`）。 -/
theorem fourIntersections_iff_incompatible {s t : Split α} :
    s.FourIntersections t ↔ s.Incompatible t :=
  incompatible_iff.symm

/-- 每个 split 与**自身**相容（`sideA ⊥ sideB`）。 -/
theorem compatible_self (s : Split α) : s.Compatible s :=
  Or.inr (Or.inl s.disjoint_sides)

/-! ## 3. 4 元组上的 2|2 诱导、冲突四点、弱相容 -/

/-- `s` 在四点组 `(a,b,c,e)` 上**诱导 2|2 split `ab|ce`**（两侧可互换）。

对应文献 1663–1679 行的 "S₁ extends the partial split {t,u}, {v,w}"。 -/
def Separates (s : Split α) (a b c e : α) : Prop :=
  (a ∈ s.sideA ∧ b ∈ s.sideA ∧ c ∈ s.sideB ∧ e ∈ s.sideB) ∨
    (a ∈ s.sideB ∧ b ∈ s.sideB ∧ c ∈ s.sideA ∧ e ∈ s.sideA)

/-- **冲突四点**：存在四点与三个成员分别在它们上诱导 `ab|ce`、`ac|be`、`ae|bc`
（= 全部三个 2|2 split）。这正是文献 1663–1679 行禁止的构形（Fig. 5）。 -/
def HasConflictingQuartet (F : Set (Split α)) : Prop :=
  ∃ a b c e : α,
    (∃ s ∈ F, s.Separates a b c e) ∧ (∃ t ∈ F, t.Separates a c b e) ∧
      (∃ u ∈ F, u.Separates a e b c)

/-- **弱相容**（文献 1663–1679 行）：不含冲突四点。

> "we define a collection Σ of splits of X to be weakly compatible if there are no four points
>  t, u, v, w ∈ X and three splits S₁, S₂, S₃ ∈ Σ such that S₁ extends {t,u},{v,w}, while S₂
>  extends {t,v},{u,w}, and S₃ extends {t,w},{v,u}." -/
def WeaklyCompatible (F : Set (Split α)) : Prop := ¬ HasConflictingQuartet F

/-- `Separates` 对前两点的次序不敏感（同一 2|2 split）。 -/
theorem separates_comm_first (s : Split α) (a b c e : α) :
    s.Separates a b c e ↔ s.Separates b a c e := by
  simp only [Separates]; tauto

/-- `Separates` 对后两点的次序不敏感。 -/
theorem separates_comm_last (s : Split α) (a b c e : α) :
    s.Separates a b c e ↔ s.Separates a b e c := by
  simp only [Separates]; tauto

/-- `Separates` 对两侧互换不敏感。 -/
theorem separates_comm_sides (s : Split α) (a b c e : α) :
    s.Separates a b c e ↔ s.Separates c e a b := by
  simp only [Separates]; tauto

/-- 两个成员若分别诱导 `ab|ce` 与 `ac|be`，则它们**不兼容**（四个交全非空）。 -/
theorem not_compatible_of_separates {s t : Split α} {a b c e : α}
    (hs : s.Separates a b c e) (ht : t.Separates a c b e) : ¬ s.Compatible t := by
  have h : s.Incompatible t := by
    rw [incompatible_iff]
    rcases hs with ⟨ha, hb, hc, he⟩ | ⟨ha, hb, hc, he⟩ <;>
      rcases ht with ⟨ha', hc', hb', he'⟩ | ⟨ha', hc', hb', he'⟩
    · exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha, ha'⟩⟩, ⟨b, Finset.mem_inter.mpr ⟨hb, hb'⟩⟩,
        ⟨c, Finset.mem_inter.mpr ⟨hc, hc'⟩⟩, ⟨e, Finset.mem_inter.mpr ⟨he, he'⟩⟩⟩
    · exact ⟨⟨b, Finset.mem_inter.mpr ⟨hb, hb'⟩⟩, ⟨a, Finset.mem_inter.mpr ⟨ha, ha'⟩⟩,
        ⟨e, Finset.mem_inter.mpr ⟨he, he'⟩⟩, ⟨c, Finset.mem_inter.mpr ⟨hc, hc'⟩⟩⟩
    · exact ⟨⟨c, Finset.mem_inter.mpr ⟨hc, hc'⟩⟩, ⟨e, Finset.mem_inter.mpr ⟨he, he'⟩⟩,
        ⟨a, Finset.mem_inter.mpr ⟨ha, ha'⟩⟩, ⟨b, Finset.mem_inter.mpr ⟨hb, hb'⟩⟩⟩
    · exact ⟨⟨e, Finset.mem_inter.mpr ⟨he, he'⟩⟩, ⟨c, Finset.mem_inter.mpr ⟨hc, hc'⟩⟩,
        ⟨b, Finset.mem_inter.mpr ⟨hb, hb'⟩⟩, ⟨a, Finset.mem_inter.mpr ⟨ha, ha'⟩⟩⟩
  exact h

/-- 一个 split 在**同一**四点组上**至多**诱导一个 2|2 split。

（由 `not_compatible_of_separates` + `compatible_self` 立得：同一 split 诱导两种 2|2
会与自身不兼容。） -/
theorem Separates.exclusive {s : Split α} {a b c e : α} (h : s.Separates a b c e) :
    ¬ (s.Separates a c b e ∨ s.Separates a e b c) := by
  rintro (h2 | h3)
  · exact not_compatible_of_separates h h2 (compatible_self s)
  · exact not_compatible_of_separates h3 ((separates_comm_last s a b c e).mp h)
      (compatible_self s)

/-! ## 4. ★★ 强 ⟹ 弱 -/

/-- ★★ **两两相容 ⟹ 弱相容**（强 ⟹ 弱）。

若 `s, t, u` 在四点 `a,b,c,e` 上分别诱导 `ab|ce`、`ac|be`、`ae|bc`，
则 `s` 与 `t` 的四个交全非空（`not_compatible_of_separates`），与两两相容矛盾。 -/
theorem weaklyCompatible_of_pairwiseCompatible {F : Set (Split α)}
    (h : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) : WeaklyCompatible F := by
  rintro ⟨a, b, c, e, ⟨s, hs, hsa⟩, ⟨t, ht, hta⟩, _⟩
  exact not_compatible_of_separates hsa hta (h s hs t ht)

/-- 弱相容的**子族**弱相容。 -/
theorem WeaklyCompatible.mono {F F' : Set (Split α)} (h : WeaklyCompatible F)
    (hsub : F' ⊆ F) : WeaklyCompatible F' := by
  rintro ⟨a, b, c, e, ⟨s, hs, hsa⟩, ⟨t, ht, hta⟩, ⟨u, hu, hua⟩⟩
  exact h ⟨a, b, c, e, ⟨s, hsub hs, hsa⟩, ⟨t, hsub ht, hta⟩, ⟨u, hsub hu, hua⟩⟩

/-- 任意**两个** split 的族都弱相容（冲突四点需要三个不同方式，
而一个 split 在同一四点组上至多诱导一个 2|2 split）。 -/
theorem weaklyCompatible_pair (s t : Split α) : WeaklyCompatible ({s, t} : Set (Split α)) := by
  rintro ⟨a, b, c, e, ⟨s', hs', h1⟩, ⟨t', ht', h2⟩, ⟨u', hu', h3⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs' ht' hu'
  -- 用 `rw` 而不是 `subst`：`s' = t` 型的等式若 `subst` 掉定理参数 `t` 会失名
  rcases hs' with hs1 | hs1 <;> rcases ht' with ht1 | ht1 <;> rcases hu' with hu1 | hu1 <;>
    rw [hs1] at h1 <;> rw [ht1] at h2 <;> rw [hu1] at h3
  · exact (Separates.exclusive h1) (Or.inl h2)
  · exact (Separates.exclusive h1) (Or.inl h2)
  · exact (Separates.exclusive h1) (Or.inr h3)
  · exact (Separates.exclusive h2) (Or.inr ((separates_comm_last t a e b c).mp h3))
  · exact (Separates.exclusive h2) (Or.inr ((separates_comm_last s a e b c).mp h3))
  · exact (Separates.exclusive h1) (Or.inr h3)
  · exact (Separates.exclusive h1) (Or.inl h2)
  · exact (Separates.exclusive h1) (Or.inl h2)

/-! ## 5. ★★★ 对称函数的 d-split 全体弱相容（Theorem 3，1683–1699 行） -/

/-- **单对四点亏损**（文献 438–456 行的 `max{…} − d(a,a') − d(b,b')`，省去 `½`）。 -/
def pairDeficit (δ : α → α → ℝ) (a a' b b' : α) : ℝ :=
  max (δ a b + δ a' b') (δ a b' + δ a' b) - (δ a a' + δ b b')

/-- ★ **`d`-split**（文献 438–456 行）：`A|B` 的隔离指数为正，即对**所有** `a,a' ∈ A`、
`b,b' ∈ B` 都有 `d(a,a') + d(b,b') < max{d(a,b)+d(a',b'), d(a,b')+d(a',b)}`。

（隔离指数取 `min`，故「`min > 0`」⟺「逐对全为正」。）

⚠️ **W12j 更正 —— 已被 W25-b ★D 校正推翻**：上面括号里的等价**只对「两个配对都为正」的强形式成立**，
对本 `def` 的 `max` 形式**不成立**（当时据此判 `IsDSplit` 不忠实；**该判断作废**，见下）。

★★★ **W25-b ★D 校正（四要素）**

* **旧形态/旧判断（作废）**：BdD 的 d-split（隔离指数 `α_{A,B} > 0`）是 `min` 形 ⇒ 本 `def`（`max` 形）
  不忠实；`bunemanIndex`（`α`）取 `min`，故两者不等价；
* **新形态/新判断**：BdD 的
  `α := min{max{d(a,b)+d(a',b'), d(a,b')+d(a',b), d(a,a')+d(b,b')} − d(a,a') − d(b,b')}`（md `:446-454`）
  的 `max` **含内部项** ⇒ `α = max(min{max{P,Q} − I}, 0)` ⇒ `α_{A,B} > 0 ⟺ ∀ 四元组 max{P,Q} > I`
  ⟺ **本 `def`（`max` 形）** ⇒ **`IsDSplit` 是忠实的** ✓；两项 `min` 形是
  **Buneman 1971 p. 390 的 `μ_σ`**（= 库内 `bunemanIndex`，`μ > 0 ⟺ IsDSplitStrong`，**严格强于**本 `def`）；
* **文献行号**：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:438-440`（d-split ⟺ 隔离指数为正）
  ＋ `:446-454`（三项 `max` 的 `α`）＋ `:673-684`（split-prime = 隔离指数**恰为 `0`**）；
* **理由（真假判据）**：两项 `min` 形可取负值 ⇒ `:673-684` 的「isolation index `0`」无法刻画 split-prime；
  且 `:438-440` 会与 `:446` 的三项 `max` 自相矛盾。⇒ 本文件的反例
  `Phylo/Stat/BunemanIndexBridge.lean` 的 `Split.not_isDSplit_implies_bunemanIndex_pos` 仍是**真命题**
  （`δ : Dissimilarity (Fin 4)`，`{0,1}|{2,3}` 满足 `IsDSplit` 而 `bunemanIndex < 0`），但它反的是
  「`IsDSplit ⟺ 0 < bunemanIndex`」，**不是**「`IsDSplit` 的忠实性」。
  强形式（两项 `min`）登记为 `Split.IsDSplitStrong`（同文件），两者的等价**在四点条件 `FourPoint` 下成立**
  （`Split.isDSplit_iff_isDSplitStrong_of_fourPoint`）。 -/
def IsDSplit (δ : α → α → ℝ) (A B : Finset α) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
    δ a a' + δ b b' < max (δ a b + δ a' b') (δ a b' + δ a' b)

/-- **纯 `max` 不等式**：三个「四点亏损」
`max(Y,Z) − X`、`max(X,Z) − Y`、`max(X,Y) − Z` **不可能同时为正**。

（取三者中最大者即得；与度量公理、对称性都无关。） -/
theorem not_all_three_deficit_pos (X Y Z : ℝ) :
    ¬ (0 < max Y Z - X ∧ 0 < max X Z - Y ∧ 0 < max X Y - Z) := by
  rintro ⟨h1, h2, h3⟩
  have h1' : X < max Y Z := sub_pos.mp h1
  have h2' : Y < max X Z := sub_pos.mp h2
  have h3' : Z < max X Y := sub_pos.mp h3
  rcases le_total Y Z with hYZ | hZY
  · have hZ : max Y Z = Z := max_eq_right hYZ
    have hXZ : X < Z := by rw [hZ] at h1'; exact h1'
    have hle : max X Y ≤ Z := max_le (le_of_lt hXZ) hYZ
    linarith
  · have hY : max Y Z = Y := max_eq_left hZY
    have hXY : X < Y := by rw [hY] at h1'; exact h1'
    have hle : max X Z ≤ Y := max_le (le_of_lt hXY) hZY
    linarith

/-! `IsDSplit` 对两侧互换不变（需对称性，与文献的「对称函数」一致）。 -/
omit [Fintype α] [DecidableEq α] in
theorem isDSplit_comm {δ : α → α → ℝ} (hδ : ∀ x y, δ x y = δ y x) {A B : Finset α} :
    IsDSplit δ A B ↔ IsDSplit δ B A := by
  have key : ∀ {A B : Finset α}, IsDSplit δ A B → IsDSplit δ B A := by
    intro A B h a ha a' ha' b hb b' hb'
    have hh := h b hb b' hb' a ha a' ha'
    have e1 : δ b b' + δ a a' = δ a a' + δ b b' := by ring
    have e2 : max (δ b a + δ b' a') (δ b a' + δ b' a)
        = max (δ a b + δ a' b') (δ a b' + δ a' b) := by
      congr 1
      · rw [hδ b a, hδ b' a']
      · rw [hδ b a', hδ b' a]; ring
    rw [e1, e2] at hh
    exact hh
  exact ⟨key, fun h => key h⟩

/-- 一个 2|2 诱导给出**正的**对应四点亏损。 -/
theorem deficit_pos_of_separates {δ : α → α → ℝ} (hδ : ∀ x y, δ x y = δ y x)
    {s : Split α} {a b c e : α} (h : IsDSplit δ s.sideA s.sideB)
    (hsep : s.Separates a b c e) :
    0 < max (δ a c + δ b e) (δ a e + δ b c) - (δ a b + δ c e) := by
  rcases hsep with ⟨ha, hb, hc, he⟩ | ⟨ha, hb, hc, he⟩
  · exact sub_pos.mpr (h a ha b hb c hc e he)
  · exact sub_pos.mpr ((isDSplit_comm hδ).mp h a ha b hb c hc e he)

/-- ★★★ **Theorem 3 第一句**（1683–1684 行）：任意**对称**函数的全体 `d`-split **弱相容**。

> "The d-splits with respect to any symmetric function d on a set X are weakly compatible."

证明：三个成员分别给出三个正的「四点亏损」，与 `not_all_three_deficit_pos` 矛盾
（对称性用于把 `δ c b` 换成 `δ b c`、把 `δ e c`/`δ e b` 换成 `δ c e`/`δ b e`）。 -/
theorem weaklyCompatible_of_isDSplit {δ : α → α → ℝ} (hδ : ∀ x y, δ x y = δ y x)
    {F : Set (Split α)} (h : ∀ s ∈ F, IsDSplit δ s.sideA s.sideB) :
    WeaklyCompatible F := by
  rintro ⟨a, b, c, e, ⟨s, hs, hsa⟩, ⟨t, ht, hta⟩, ⟨u, hu, hua⟩⟩
  have h1 := deficit_pos_of_separates hδ (h s hs) hsa
  have h2 := deficit_pos_of_separates hδ (h t ht) hta
  have h3 := deficit_pos_of_separates hδ (h u hu) hua
  rw [hδ c b] at h2
  rw [hδ e c, hδ e b] at h3
  exact not_all_three_deficit_pos (δ a b + δ c e) (δ a c + δ b e) (δ a e + δ b c) ⟨h1, h2, h3⟩

/-! ## 6. 非空真与严格性（★B / ★C） -/

/-- `Fin 4` 上的 2|2 split `{0,1}|{2,3}`。 -/
def fourA : Split (Fin 4) := ofSideA {0, 1} (by decide) (by decide)

/-- `Fin 4` 上的 2|2 split `{0,2}|{1,3}`。 -/
def fourB : Split (Fin 4) := ofSideA {0, 2} (by decide) (by decide)

/-- `Fin 4` 上的 2|2 split `{0,3}|{1,2}`。 -/
def fourC : Split (Fin 4) := ofSideA {0, 3} (by decide) (by decide)

/-- ★ **非空真**：`Fin 4` 上这三个 split 真的构成冲突四点
（`{0,1}|{2,3}`、`{0,2}|{1,3}`、`{0,3}|{1,2}` 全在族内）。 -/
theorem hasConflictingQuartet_four :
    HasConflictingQuartet ({fourA, fourB, fourC} : Set (Split (Fin 4))) := by
  refine ⟨0, 1, 2, 3, ?_, ?_, ?_⟩
  · exact ⟨fourA, by simp, by simp [Separates, fourA]⟩
  · exact ⟨fourB, by simp, by simp [Separates, fourB]⟩
  · exact ⟨fourC, by simp, by simp [Separates, fourC]⟩

/-- ★ **非空真**（对偶）：这三个 split 的族**不**弱相容。 -/
theorem not_weaklyCompatible_four :
    ¬ WeaklyCompatible ({fourA, fourB, fourC} : Set (Split (Fin 4))) :=
  fun h => h hasConflictingQuartet_four

/-- `Fin 5` 上的 2|2 split `{0,1}|{2,3,4}`。 -/
def fiveA : Split (Fin 5) := ofSideA {0, 1} (by decide) (by decide)

/-- `Fin 5` 上的 2|2 split `{0,2}|{1,3,4}`。 -/
def fiveB : Split (Fin 5) := ofSideA {0, 2} (by decide) (by decide)

/-- ★★ **严格性**：`Fin 5` 上 `{0,1}|{2,3,4}` 与 `{0,2}|{1,3,4}` 弱相容（任意二元族都如此），
但**不**两两相容。

⇒ 弱相容是强相容的**严格**弱化（文献 Fig. 5 需要**三个** split 正是这个原因）。 -/
theorem exists_weaklyCompatible_not_pairwiseCompatible :
    ∃ F : Set (Split (Fin 5)),
      WeaklyCompatible F ∧ ¬ (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) := by
  refine ⟨{fiveA, fiveB}, weaklyCompatible_pair fiveA fiveB, ?_⟩
  intro h
  have hsepA : fiveA.Separates 0 1 2 3 := by simp [Separates, fiveA]
  have hsepB : fiveB.Separates 0 2 1 3 := by simp [Separates, fiveB]
  exact not_compatible_of_separates hsepA hsepB (h fiveA (by simp) fiveB (by simp))

/-! ## 7. 缺口（显式 `Prop`；未证） -/

/-- **split 度量** `δ_S(x,y) = 1`（`x,y` 被 `S` 分开）`/ 0`（文献 531 行的 `δ_{A,B}`）。 -/
def SplitMetric (s : Split α) (x y : α) : ℝ :=
  if (x ∈ s.sideA ∧ y ∈ s.sideB) ∨ (x ∈ s.sideB ∧ y ∈ s.sideA) then 1 else 0

/-- **split-prime**：对**每个** split 的隔离指数都是 `0`（文献 673–684 行）。

⚠️ **W12k ★D：本 `def` 不可满足 ✗**（`def` 原文未改）。取 `A = ∅` 时 `IsDSplit δ ∅ B` 是**空真**
（`∀ a ∈ ∅, …`）⇒ `¬ IsDSplit δ ∅ B` **为假** ⇒ `SplitPrime δ` 对**任何** `δ` 都不成立：
形式化见 `Phylo/Stat/BunemanIndexBridge.lean` 的 `Split.not_splitPrime`。
根因：BdD 的「(partial) split」两侧**非空**，本定义**漏了非空侧条件**。
补齐非空侧后的形态登记为 `Split.SplitPrimeStd`（同文件），
且库内形态（补齐非空侧后）⟹ 它（`splitPrimeStd_of_splitPrimeNE`）。
★ **W25-b ★D 校正**：`SplitPrimeStd` 用的是两项 `min` 形的 `¬ IsDSplitStrong`（= `bunemanIndex ≤ 0`），
**不是**忠实 split-prime；忠实形态是「隔离指数 `α_{A,B} = 0`」即 `¬ IsDSplit`（`max` 形，md `:673-684`），
登记为 `Split.SplitPrimeFaithful`（`Phylo/Stat/BunemanIndexBridge.lean` 的 `§8.1`），
且 `SplitPrimeFaithful ⟹ SplitPrimeStd`（严格）。 -/
def SplitPrime (δ : α → α → ℝ) : Prop := ∀ A B : Finset α, ¬ IsDSplit δ A B

/-- ⛔ **四点条件（旧 / 错形态）—— 已被证伪；本名保留为 `FourPointLegacy`，仅供追溯，勿引用。**

★★ **2026-10-17 W22（老师原话「**允许**」）**：本体**已改对** —— `def FourPoint` 现为标准形态
（见下方下一个 `def`）；本定义**改名 `FourPointLegacy`**，留存为「旧形态的反例登记」。
⇒ ★ **下面「为何 W21 不改本体」那一节是当时的记录，现已作废**（保留仅为追溯）；
它列的 5 处依赖**逐处处置**见 `def FourPoint` 的 docstring 里的改名清单 ✓。

⚠️⚠️ **本 `def` 的第三合取项末项写错**：写的是 `δ a b + δ a' b`（两对**共享端点 `b`**），
而三个应比较的和是 `P₁ = δ a a' + δ b b'`、`P₂ = δ a b + δ a' b'`、`P₃ = δ a b' + δ a' b`
⇒ 第三式的右端应为 `max P₁ P₂`，本定义却写成 `max P₁ (δ a b + δ a' b)`（**既非 P₂ 亦非 P₃**）。

## ★D 复核（W20–W21，逐字符核实）

* **缺陷成立**：与同文件 `FourPointStd`（`:422`）逐字符比对，**唯一差异**就是这个 `b'`；
* **不等价**：`Split.fourPointStd_of_fourPoint`（`BunemanIndexBridge.lean:367`）给「本库 ⟹ 标准」；
  反向**不成立**（`Split.not_fourPointStd_imp_fourPoint`，`:443`，与 `cexTreeVal_not_fourPoint` 同反例）；
* **严重性**：真实树度量**几乎全不满足**本形态（`n = 4` 随机 3000 例中仅 **1** 例；`n = 5/6/7` 为 `0/3000`；
  独立机检：标准形态违反 `0/75`、本库形态违反 `68/75`）⇒ 以本形态为**前提**的定理把真实对象类排除在外；
* 最小显式见证：`Split.cexTreeVal_not_fourPoint`（`BunemanIndexBridge.lean:431`）。

## 为何 W21 **不改本体**（任务 C / C4 的裁定；D1 允许「如实说明并只做标注」）

派单 D1 称「下游只有 2 个 Prop 缺口，**库内无人依赖** ⇒ 改本体是安全的」——
★★ **W21 实测：该描述不成立**。本定义有 **5 处**库内依赖，其中 **3 条是以错形态为真的定理**，
改本体会使它们**真值反转**：

| 依赖（位置） | 改本体后的后果 |
|---|---|
| `Split.fourPointStd_of_fourPoint`（`BunemanIndexBridge.lean:367`） | 退化为 `P → P`：证明失效，须改写 |
| `Split.cexTreeVal_not_fourPoint`（`:431`） | 变**假**（该度量满足标准形态，见 `cexTreeVal_fourPointStd` `:424`） |
| `Split.not_fourPointStd_imp_fourPoint`（`:443`） | 变**假**（「标准 ⟹ 标准」恒真） |
| `Split.pairwiseCompatible_of_exists_symm_fourPoint_isDSplit`（`:335`） | 前提变**弱** ⇒ 陈述变**强**，证明须重核 |
| `fourPointOfSplitMetricSum_gap`（本文件 `:547`） | 与 `…_gap_correct_shape`（`:518`）**变成同一条陈述** ⇒ W12k「该 `Prop` 为假」的登记失真 |

⇒ 彻底收干净须**同时**做三件超出「只改本体」的动作：
**(i)** 把 3 条历史反例定理**改名**（如 `…_fourPointLegacy`）—— 即**动既有定理名**；
**(ii)** 改 `fourPointOfSplitMetricSum_gap` 的语义并作废「已判为假」的登记；
**(iii)** 走 `@[deprecated]` **亦不可行**：它会在上述使用点触发警告 ⇒ 违反「单文件门 stdout 0 字节」，
除非先做 (i)。

★ 故本批依 D1 例外条款 **只做标注**，并**逐条写出解除条件**：
「是否允许把 3 条历史反例定理改名到 `…Legacy`」**需老师裁定**（超出本批授权边界）。
★★ **全库唯一的「错定义仍在库内」隐患即此一处**，已在此**永久登记**。

## 留证（四要素；本体未改 ⇒ 记「为何不改」）

* **旧形态**（= 现状，逐字未动）：第三合取项末项 `δ a b + δ a' b`；
* **文献形态**：三对和的最大者**至少取到两次** —— **`Buneman1974_MetricPropertiesOfTrees.md`
  THEOREM 1（`:33-36`）＋ THEOREM 2（`:70-74`）**；库内对应物 = `FourPointStd`（`:422`）；
* **理由**：见上表（改本体会使 3 条既有定理真值反转 ＋ 1 条 gap 语义漂移 ＋ deprecate 违反门禁）；
* **影响的下游**：`B-3`（`fourPointCharacterization_gap`）已于 W20 改用 `FourPointStd` ✓；
  ★ **本批未放弃该修正**，只是把「改名 + 语义迁移 + 报告同步」打包留给老师裁定。 -/
def FourPointLegacy (δ : α → α → ℝ) : Prop :=
  ∀ a a' b b' : α,
    δ a a' + δ b b' ≤ max (δ a b + δ a' b') (δ a b' + δ a' b) ∧
      δ a b + δ a' b' ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) ∧
        δ a b' + δ a' b ≤ max (δ a a' + δ b b') (δ a b + δ a' b)

/-- ★★★ **四点条件**（文献形态，**标准**）：三对和
`P₁ = δ a a' + δ b b'`、`P₂ = δ a b + δ a' b'`、`P₃ = δ a b' + δ a' b` 中**最大者至少取到两次**
（等价写法：每个 `≤` 其余两者的 `max`）。

★★★ **2026-10-17 W22 任务 A：本体修正（老师已批准「允许」）—— 四要素留证** ✓

* **旧形态** ✗（现名 `FourPointLegacy`，同文件上方）：第三合取项末项写 `δ a b + δ a' b`
  （两对**共享端点 `b`**，**既非 `P₂` 亦非 `P₃`**）；
* **新形态** ✓：第三合取项末项 `δ a b + δ a' b'`；三个 `max` 约束**合起来**恰是
  「三对和的最大者至少出现两次」；
* **文献依据** ✓：`references/md/Buneman1974_MetricPropertiesOfTrees.md` **THEOREM 1**（`:33-36`，
  逐字「…distance satisfying **the four-point condition**」）＋ **THEOREM 2**（`:70-74`）；
  对应 `SempleSteel2002:539–544` ✓（与 W12k 给 `FourPointStd` 的文献依据**同一处**）；
* **理由（★D 先判真假，非措辞）** ✗：**真实树度量几乎全不满足旧形态** —— `n = 4` 的 3000 个
  随机树度量里仅 **1** 个满足、`n = 5/6/7` 为 **0/3000**；独立机检 `scripts/msc/w12d_b2_b1_search.py`：
  两两相容族上**标准形态违反 0 例**、**旧形态违反 68/75 例** ✗。
  ⇒ 凡以旧形态为**前提**的定理都把真实对象类排除在外。最小显式见证 = 4 叶平衡树
  `((0,1),(2,3))` 全边权 `1`（即 `Split.cexTreeVal_fourPointStd` 的那个度量）。

### ★ 改名 / 处置清单（旧 → 新 → 理由；除注明者外都在 `Phylo/Stat/BunemanIndexBridge.lean`）

| # | 旧 | 新 | 理由 |
|---|---|---|---|
| 1 | `cexTreeVal_not_fourPoint` | **`cexTreeVal_not_fourPointLegacy`** | 改本体后该陈述**变假**（`cexTreeVal_fourPointStd` 给标准形态成立）⇒ 只能对 `FourPointLegacy` 陈述 |
| 2 | `not_fourPointStd_imp_fourPoint` | **`not_fourPointLegacy_of_fourPoint`** | 同理：改本体后「标准 ⟹ 标准」恒真 ⇒ 真内容变成「标准 ⟹ **旧形态**」**不成立** |
| 3 | `fourPointStd_of_fourPoint` | **`fourPoint_of_fourPointLegacy`** | 改本体后退化为 `P → P`（无内容）⇒ ★ **改锚到旧形态**，保住**非平凡**内容「旧 ⟹ 标准」（比「保留为 rfl 级」更有价值） |
| 4 | `not_fourPointOfSplitMetricSum` | **`not_fourPointOfSplitMetricSum_legacy`** | 同 #1：改本体后 (B1) 变**真**（见 #5）⇒ 反驳只能对旧形态陈述 |
| 5 | `fourPointOfSplitMetricSum_gap` | **名字不变**，但已**收口可证** | 改本体后它与 `fourPointOfSplitMetricSum_gap_correct_shape`（`BunemanIndexBridge.lean`，W12k 已收口）**成为同一条陈述** ⇒ 由 `fourPointOfSplitMetricSum_gap_proof` 收口 ✓ |
| 6 | `compatible_of_fourPoint_isDSplit` · `pairwiseCompatible_of_exists_symm_fourPoint_isDSplit` | **名字不变** | 两者证明**只用第一合取项**（两形态共享）⇒ 改本体后陈述**变强**且**仍真** ✓ |

★ **`FourPointStd` 的去向**：两 `def` 现**定义相同** ⇒ 收成**别名**
`abbrev FourPointStd (δ) := FourPoint δ`（保留名字，使 W12k–W21 全部既有引用**无需改动**）。

★ **影响的下游**：`B-3`（`fourPointCharacterization_gap`）W20 已改用 `FourPointStd`
⇒ 现与 `FourPoint` **同义** ✓；且第 3 条（派单 B-③）的 `⟹` 半边因此**重新可做**（见下批）。 -/
def FourPoint (δ : α → α → ℝ) : Prop :=
  ∀ a a' b b' : α,
    δ a a' + δ b b' ≤ max (δ a b + δ a' b') (δ a b' + δ a' b) ∧
      δ a b + δ a' b' ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) ∧
        δ a b' + δ a' b ≤ max (δ a a' + δ b b') (δ a b + δ a' b')

/-- **`FourPointStd` —— 别名**（W22 起）：与 `def FourPoint`（同文件上方）**定义上相同**。

W12k 曾把「标准形态」另立此名并在其 docstring 里记录与旧形态的逐字符差异；
W22 把 `FourPoint` 本体改对之后两者同义，故收成 `abbrev`
（★ 保留此名，使 W12k–W21 的全部既有引用**无需改动**）。
★ 原 W12k docstring 的**实质内容**（差异、方向性、严重性、文献依据）已**整体并入**
`def FourPoint` 的 docstring，此处不重复。 -/
abbrev FourPointStd (δ : α → α → ℝ) : Prop := FourPoint δ

omit [Fintype α] [DecidableEq α] in
/-- ★★ **四点条件 ⟹ 对称**（W22 任务 B-③ 的器材）：三条 `max` 不等式**强制** `δ x y = δ y x`。

★ 这条**不是**琐碎改写：本库 `FourPoint` 的形态里**没有**「对称」「零对角」两要素，
而 `Phylo/Stat/BunemanIndexBridge.lean` 的 `compatible_of_fourPoint_isDSplit` 把 `symm`
当作**额外假设**传入 ⇒ 该文件此前只能证「对称 ＋ 四点 ⇒ …」。本定理把那条假设**去掉**，
使 `fourPointCharacterization_gap` 的 `⟸` 半边得以按**原陈述**证明
（`Split.fourPointCharacterization_gap_reverse`）。

**证明**：取 `a = x`、`a' = y`、`b = b' = x`，第一合取项为
`δ x y + δ x x ≤ max (δ x x + δ y x) (δ x x + δ y x)` —— 两个 `max` 槽是**同一表达式**
⇒ `max` 退化（`max_self`）⇒ `δ x y ≤ δ y x`；再把 `x ↔ y` 做一次得反向不等式。 -/
theorem fourPoint_symm {δ : α → α → ℝ} (h : FourPoint δ) (x y : α) : δ x y = δ y x := by
  have h1 : δ x y ≤ δ y x := by
    have h' := (h x y x x).1
    rw [max_self] at h'
    linarith
  have h2 : δ y x ≤ δ x y := by
    have h' := (h y x y y).1
    rw [max_self] at h'
    linarith
  linarith

/-- ⬜ **缺口 1（Theorem 3 的逆，1683–1699 行）**：弱相容 ⟹ `Σ` 恰是某个对称 `δ` 的
`d`-split 全体（取 `δ := Σ_{S∈Σ} λ_S δ_S`，`λ_S > 0`，且隔离指数 `α_S = λ_S`）。

本文件已证其**一半**（`weaklyCompatible_of_isDSplit` 的逆否：`Σ ⊆ Σ_δ`）；
「`Σ_δ ⊆ Σ`」（非成员的隔离指数为 `0`）需要隔离指数的层析论证，未落。

⚠️ **W12j 忠实性更正（协调侧提出，已逐条核实；本 `def` 原文未改）**：

1. 参数 `w` **只出现在假设里**，结论里**完全不出现** ⇒ 本 `Prop` 实质等价于「弱相容 `F` ⟹
   存在实现它的对称 `δ`」，**拿不到** Theorem 3 的系数那一半（隔离指数 `α_S = w S`）；
2. 结论里的 `IsDSplit` 是 **`max` 形式**（两个配对**至少一个**为正），而 BdD 的「d-split」
   是隔离指数 `α > 0`（**两个配对都为正**）；两者对**任意对称** `δ` **不等价** ——
   形式化反例：`Phylo/Stat/BunemanIndexBridge.lean` 的 `Split.not_isDSplit_implies_bunemanIndex_pos`
   （`δ : Dissimilarity (Fin 4)`，`{0,1}|{2,3}` 满足 `IsDSplit` 而 `bunemanIndex = -2/5 < 0`）；
3. `δ` 是**裸对称函数**（无 `δ x x = 0`），而隔离指数的 `inf'` 会取到 `a = a'`、`b = b'` 的项
   （BdD 的 setting 里 `d(x,x) = 0`）。

⇒ **正确形态**已登记为 `Split.weakCompatibilityRealization_gap_correct_shape`
（`Phylo/Stat/BunemanIndexBridge.lean` §4，用库内 `bunemanIndex` = 隔离指数 `α` 表达
「`α_S = w S`（成员）」与「非成员 `α = 0`」）；本 `def` 保持原样，作为该形态的**弱化**登记。 -/
def weakCompatibilityRealization_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    WeaklyCompatible (↑F : Set (Split α)) → (∀ s ∈ F, 0 < w s) →
      ∃ δ : α → α → ℝ, (∀ x y, δ x y = δ y x) ∧
        ∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s

/-- ⬜ **缺口 2（典范分解，1651–1655 行 Theorem 2 + 673–684 行）**：
任一对称 `δ` 可写成 `δ = δ₀ + Σ_{S ∈ Σ} c_S · δ_S`，其中 `c_S > 0`、残差 `δ₀` **split-prime**。

未落原因：需要先把「度量」「四点条件」与树的边权（`Phylogram.dist`）接起来，
并证明残差的 split-prime 性（隔离指数为 0）。

⚠️ **W12k ★D：本缺口是假命题** ✗（`def` 原文未改）。其结论要求 `∃ δ₀, SplitPrime δ₀`，
而 `SplitPrime` **不可满足**（见上一条：`A = ∅` 使 `IsDSplit` 空真）⇒ 对**任何** `δ` 都不存在这样的分解：
形式化反驳见 `Phylo/Stat/BunemanIndexBridge.lean` 的 `Split.not_canonicalSplitDecomposition_gap`。
**正确形态**（残差改为忠实形态 `SplitPrimeStd`）登记为
`Split.canonicalSplitDecomposition_gap_correct_shape`（同文件，未证）。
另注（协调侧机器判定）：库内 `SplitPrime`（处处 `¬Max`）**严格强于**文献形态（处处 `¬Strong`）——
`¬Max ⟹ ¬Strong` 而反向不成立；不过本缺口的致命伤是**非空侧条件缺失**，比这一条更基本。
⚠️ 一旦确认 `SplitPrime` **恒假**（不可满足），「`SplitPrime` 比 `SplitPrimeStd` 严格」这个比较
就**不再有实际用途**（前者抓不到任何 `δ`）⇒ 无需为它形式化分离反例（W12l 决定：只在 docstring 登记）。 -/
def canonicalSplitDecomposition_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrime δ₀ ∧
        ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

/-- ⬜ **缺口 3（强相容 ⟺ 树度量，**Buneman 1974 Thm 2**，`SempleSteel2002:539–544`）**：
两两相容 ⟺ `Σ` 恰是某个**满足四点条件**的 `δ` 的 `d`-split 全体。

「⟸」方向由本文件的 ★★（强 ⟹ 弱）配合 `not_all_three_deficit_pos` 给出**弱**结论；
完整刻画还需「四点条件 ⟹ 树度量（`Phylogram.dist`）」一侧（`Phylo/BunemanTree.lean` 的 F6/T-6 接口）。

★★★ **2026-10-15 W20 任务 B-3 改命题（留证：旧形态 → 新形态 → 文献依据 → 理由）** ✓

* **旧形态** ✗：右边写 `∃ δ : α → α → ℝ, **FourPoint** δ ∧ …` —— 用的是**本库** `def FourPoint` ✗；
* **新形态** ✓：右边写 `∃ δ : α → α → ℝ, **FourPointStd** δ ∧ …` —— 用的是**文献形态** ✓
  （`FourPointStd`，同文件 `:422`，三对和中**最大者至少取到两次** ✓）；
* **文献依据** ✓：`references/md/Buneman1974_MetricPropertiesOfTrees.md` **THEOREM 1** `:33-36`
  （**逐字**：「A graph is a tree iff it is connected, contains no triangles, and has graphical distance
  satisfying **the four-point condition**」✓ —— 即标准四点条件 ✓）＋ **Thm 2** `:70-74` ✓；
  对应 `SempleSteel2002:539–544`；★ 派单原引 `SempleSteel2002:539-544` 的**定位**已在 W19 更正为 Buneman ✓；
* **理由（★D 先判真假，非措辞问题）** ✗：本库 `def FourPoint` 的**第三**合取项末项写的是
  `δ a b + δ a' b`（两对**共享端点 `b`** ✗），而正确的三表达式之一是 `δ a b + δ a' b'` ✓
  （详见同文件 `FourPointStd` 的 docstring `:402-421` ✓）。后果：**真实树度量几乎全都不满足本库形态** ✗ ——
  随机树 + 随机正边权，`n = 4` 的 3000 个有效树度量里只有 **1** 个满足 ✓；`n = 5/6/7` 是 `0/3000` ✓；
  独立机检 `scripts/msc/w12d_b2_b1_search.py`：两两相容 split 族上**标准形态违反 0 例**、
  **本库形态违反 68/75 例** ✗；最小显式见证 = 4 叶平衡树 `((0,1),(2,3))` 全边权 `1`，
  见 `BunemanIndexBridge.lean` 的 `Split.cexTreeVal_not_fourPoint` ✓。
  ⇒ 用本库形态写的 `⟹` 半边（两两相容 ⟹ ∃ `δ` 满足它）**为假** ✗（自然候选 `δ` 正是树度量 ✓）；
* ★ **这不是"借改之便改弱"** ✗（派单纪律③）：新形态**就是文献那条** ✓；旧形态是**另一个（错的）命题** ✗。
  方向性说明（已证 ✓）：`Split.fourPointStd_of_fourPoint`（`BunemanIndexBridge.lean` ✓）给出
  「本库形态 ⟹ 标准形态」✓，反向**不成立** ✗ ⇒ 两者**不等价** ✓；
* ★★ **关于右边的 `IsDSplit`（`max` 形式）—— 为什么**不**换成文献的 d-split（`α > 0`）** ✓：
  文献（BD Thm 3 `:1683-1699` ✓）的 d-split 是 **隔离指数 `α_S > 0`** ✓，本库对应物是
  **`Split.IsDSplitStrong`**（`BunemanIndexBridge.lean:50` ✓）；但在本文件**不能引用它** ✗ ——
  它所在的模块 `Phylo/Stat/BunemanIndexBridge.lean` **import 本文件** ⇒ 引用会**循环依赖** ✗。
  ★★ 而在**四点条件下两者等价** ✓（本文件 `IsDSplit` 的 docstring `:260-265` 记有
  `Split.isDSplit_iff_isDSplitStrong_of_fourPoint` ✓）⇒ 本 `def` 的右边在当前**层次**下已是
  文献语义的**忠实表达** ✓（★ 这一点在此**写明**，免后读成"仍未忠实" ✗）；
* **影响的下游声明**：本 `def` 是 `Prop` 缺口，**库内无人依赖** ✓（仅 docstring 互引 ✓）；
  ★ 同源的 `fourPointOfSplitMetricSum_gap`（`:513`）W12k 已同样更正并登记
  `fourPointOfSplitMetricSum_gap_correct_shape` ✓ ——**本处是同一根因的第二处修正** ✓。
*
* ★★★ **2026-10-17 W23：本缺口**已收口 ✅**（`def` 本体逐字未动 ✓；收口定理在
  `Phylo/Stat/BunemanIndexBridge.lean`，两半均**无条件**）：
  **`⟸` 半** = `Split.fourPointCharacterization_gap_reverse`（W22）✓
  —— 靠 `Split.fourPoint_symm`（对称性由三条不等式**强制**推出，非第四要素 ✓）；
  **`⟹` 半** 三件齐备：(B1) `fourPointOfSplitMetricSum_gap_proof`（W22）·
  成员件 `isDSplit_splitMetricSum_of_mem`（W22）· (B2) `notIsDSplit_of_splitMetricSum_gap_holds`
  （W23，**(`★′`) 已证 ⇒ 无条件**）；
  **拼装** = `Split.fourPointCharacterization_gap_proof`（W23）✓ —— 与本 `def` **同陈述** ✓。
  ⇒ **(`★′`) `noWRealizer_exists_gap` 已在 W23 证成**（`Split.noWRealizer_exists_gap_proof`）✓，
  路线见同文件 §11.10。 -/
def fourPointCharacterization_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) ↔
      ∃ δ : α → α → ℝ, FourPointStd δ ∧
        ∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s

/-! ## 7.1 瓶颈 (B1)/(B2)（W12k 登记为**有名有姓的题**；均由协调侧指定）

`fourPointCharacterization_gap` 的 **`⟹`** 方向（两两相容 ⟹ 存在满足四点条件的 `δ`）归结为下面两条；
它们同时是 `weakCompatibilityRealization` / `canonicalSplitDecomposition` 的瓶颈。
取 `δ := Σ_{S ∈ F} w_S · δ_S`（`δ_S` = `SplitMetric S`，`w_S > 0`）：
**(B1)** 证明 `δ` 满足四点条件（「树度量」一侧）；
**(B2)** 证明**非成员**不是 `δ` 的 d-split（等价说法：隔离指数为 `0`；BdD Thm 1 的取正/凸性论证）。 -/

/-- ⬜ **瓶颈 (B1)（W12k 登记，未证）**：两两相容族 `F` 与正权重 `w` 的 split 度量组合
`δ := Σ_{S∈F} w_S · δ_S` 满足**四点条件**。

这是 `fourPointCharacterization_gap` 的 `⟹` 方向的**第一半**（「四点条件 ⟹ 树度量」一侧）：
两两相容的 split 系统恰是一棵树的边，正权重之和应为**树度量**，故四点条件成立。

⚠️ **弱**相容**不够**：`Fin 5` 上 `{0,1}|{2,3,4}` 与 `{0,2}|{1,3,4}` 弱相容，但
`δ := δ_S + δ_T` 在四元组 `(0,1,2,3)` 上的三对和为 `(δ(0,2)+δ(1,3), δ(0,1)+δ(2,3), δ(0,3)+δ(1,2)) = (3,1,4)`，
最大者只出现一次 ⇒ **不满足**四点条件。故本缺口**必须**用**强**（两两）相容。

⚠️ **W12k 更正：本缺口是假命题** ✗。理由：前提「`F` 两两相容 + `w > 0`」下 `δ := Σ w_S·δ_S` **恒为树（伪）度量**，
而**真实树度量几乎全都不满足本库 `def FourPoint`**（穷举：`n = 4` 的 3000 个随机树度量里仅 1 个满足，
`n = 5/6/7` 为 0/3000；`scripts/msc/w12d_b2_b1_search.py` 独立复核：两两相容族上本库形态违反 68/75 例、
标准形态违反 0 例）⇒ **前提真、结论假** ✓。
具体见证：`F := {δ_{0|123}} ∪ {δ_{01|23}}`（两两相容 ✓）、`w ≡ 1`，在四元组 `(0,0,1,2)` 上本库第三式给出
`LHS = 3 > RHS = 2` ⇒ 形式化反驳见 `Phylo/Stat/BunemanIndexBridge.lean` 的
`Split.not_fourPointOfSplitMetricSum` ✓。
**正确的（诚实）目标**：把结论换成 `FourPointStd`（文献形态，`Phylo/SplitWeak.lean` 的 `def FourPointStd`），
登记为本文件的 `fourPointOfSplitMetricSum_gap_correct_shape`（在 `BunemanIndexBridge.lean` 中，见下）。 -/
def fourPointOfSplitMetricSum_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) → (∀ s ∈ F, 0 < w s) →
      FourPoint (fun x y => ∑ s ∈ F, w s * SplitMetric s x y)

/-- ⬜ **瓶颈 (B2)（W12k 登记，未证）**：**非成员不是 d-split**（= 非成员的隔离指数为 `0`）。

`δ := Σ_{S∈F} w_S · δ_S`（`F` 两两相容、`w > 0`）时，任何与 `F` 的每个成员都**不同**
（含 `swap`）的 split `S` **不是** `δ` 的 `d`-split。这是 BdD Thm 1 的**取正/凸性论证**，
也是 `fourPointCharacterization_gap` 的 `⟹` 方向第二半与
`weakCompatibilityRealization` / `canonicalSplitDecomposition` 的**共同**瓶颈。

（隔离指数的精确形式见 `Phylo/BunemanTree.lean:107` 的 `bunemanIndex`，
「`α > 0` ⟺ 两配对都为正」的桥见 `Phylo/Stat/BunemanIndexBridge.lean`
的 `Split.bunemanIndex_pos_iff_isDSplitStrong`。）

⚠️ **W12l 措辞更正**：这里的「隔离指数为 `0`」应读作 **`α_S ≤ 0`** —— 穷举显示非成员的 `α` 可以是**负**的
（例：`F = { {0,1}|{2,3} }`、`S = {0,2}|{1,3}` 时 `α_S = −1`；见 `scripts/msc/w12d_b2_b1_search.py`）；
与库内 `IsDSplit`（`max` 形式）的否定对应的是 `α_S ≤ 0`，而**不是** `α_S = 0`。 -/
def notIsDSplit_of_splitMetricSum_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) → (∀ s ∈ F, 0 < w s) →
      ∀ s : Split α, (∀ t ∈ F, t ≠ s ∧ t.swap ≠ s) →
        ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) s.sideA s.sideB

/-! ## 7.2 ★★★ W26 泳道 d：**弱相容**下的「成员半边」（四元组计数机器在本文件内重建）

### 要证的东西

`F : Finset (Split α)` **弱相容**、`w > 0` 于 `F`、`t ∈ F`，取 `δ := Σ_{u∈F} w_u·δ_u`
（`δ_u = SplitMetric u`）。则 `t` 的两侧是 `δ` 的 **d-split**（`IsDSplit`）：
`∀ a,a' ∈ t.sideA, ∀ b,b' ∈ t.sideB, δaa' + δbb' < max (δab + δa'b') (δab' + δa'b)`
—— 这正是 `weakCompatibilityRealization_gap`（同文件 `:562`）结论里 `↔` 的 **`→` 半边**
（成员方向），也是 BdD Theorem 3（md `:1683-1699`）「隔离指数 `α_S = λ_S > 0`」的成员一侧。

### 为何必须在本文件内重建（W25 判定：import 方向不可达）

W22 的成员件 `Split.isDSplit_splitMetricSum_of_mem`（`Phylo/Stat/BunemanIndexBridge.lean:1949`）
只覆盖**两两相容**：它靠三种配对**两两**互斥 ⇒ `c_P = c_X = 0`。弱相容**只**禁止三者**同时**出现
（`F ⊇ {{aa'|bb'}, {ab|a'b'}, {ab'|a'b}}` 才冲突），故那条路子在弱相容下**不成立** ✗。
而 `BunemanIndexBridge.lean` **import 本文件** ⇒ 本文件的 `bSep`/`bPair*`/差分恒等式**取不到**
⇒ **计数机器在此重建**；全部判据加 `q`（quartet）前缀，避免与上游同名声明冲突。

### 计数核心（逐 split 五情形）

固定四元组 `(a,a',b,b')`，记
`I_u := δ_u(a,a') + δ_u(b,b')`、`P_u := δ_u(a,b) + δ_u(a',b')`、`X_u := δ_u(a,b') + δ_u(a',b)`；
`c_W := Σ_{u∈F, u 实现 {a,a'}|{b,b'}} w_u`，`c_P`、`c_X` 同理。按 4 点在 `u` 两侧的分布逐项核对得

| 分布 | `(I_u,P_u,X_u)` |
|---|---|
| 全在同一侧 | `(0,0,0)` |
| `1|3` 分布 | `(1,1,1)` |
| `{a,a'}|{b,b'}` | `(0,2,2)` |
| `{a,b}|{a',b'}` | `(2,0,2)` |
| `{a,b'}|{a',b}` | `(2,2,0)` |

⇒ 两条**差分恒等式**：`X̂ − Î = 2c_W − 2c_X`、`X̂ − P̂ = 2c_P − 2c_X`。

### 收口（★ 与 W22 的关键差别：`c_P·c_X = 0`，而非 `c_P = c_X = 0`）

`t ∈ F` 且 `a,a' ∈ t.sideA`、`b,b' ∈ t.sideB` ⇒ `t` 实现 W-配对 ⇒ `c_W ≥ w_t > 0`；
弱相容 ⇒ 三种配对**不同时**被实现 ⇒ `¬(0 < c_P ∧ 0 < c_X)`。反设 `max P̂ X̂ ≤ Î`：
`X̂ − Î = 2(c_W − c_X) ≤ 0` ⇒ `c_W ≤ c_X`；`P̂ − Î = 2(c_W − c_P) ≤ 0` ⇒ `c_W ≤ c_P`
⇒ `c_P > 0 ∧ c_X > 0` ⇒ 与弱相容**矛盾** ∎

★ **退化四元组**（`a = a'` 或 `b = b'`）**不需要**弱相容：此时 `P̂`、`X̂` 由同一批项组成，
上式给 `Î ≤ max P̂ X̂`，而 `t` 仍提供 `2w_t > 0` 的**严格余量** ⇒ 严格不等式照样成立；
本证明**自动覆盖**退化情形（差分恒等式对任意四元组成立，**不假设四点互异**）。

### 下一步（弱相容版 (B2)：非成员不是 d-split）—— ★ W26-d 已推进，见 §7.3

`weakCompatibilityRealization_gap` 的另一半 = 弱相容版 **(B2)**。它的**两两相容**版已收口
（`Split.notIsDSplit_of_splitMetricSum_gap_holds`，`Phylo/Stat/BunemanIndexBridge.lean:2268`），
但那条路线**不可直接搬**：它经 (★′) `noWRealizer_exists_gap` 用到 **cluster 的层析性**
（`laminar_sideNotMem` ← `laminar_of_compatible_clusters`），而弱相容**不给层析性** ——
反例正是本文件 `:382` 的 `exists_weaklyCompatible_not_pairwiseCompatible`。

⇒ **W26-d 已在 §7.3 把 (B2) 收成一条不含度量的纯计数命题 (B2-core)，并证成其 `2+2` 情形**；
本节的 `qPairW/qPairP/qPairX` 计数与 `splitMetricSum_diff_qW/qP`（`X̂ − Î = 2c_W − 2c_X`）
正是那里的计算落脚点（`splitMetricSum_isDSplit_iff`）。

-/

/-- `x`、`y` 是否被 `u` 分到两侧（`Bool` 形式，便于逐情形求值；`bSep` 的本文件重建版）。 -/
def qSep (u : Split α) (x y : α) : Bool :=
  decide (x ∈ u.sideA) != decide (y ∈ u.sideA)

/-- `SplitMetric` 的 `Bool` 形式（条件可判定 ⇒ 可逐情形化简）。 -/
theorem splitMetric_eq_qSep (u : Split α) (x y : α) :
    SplitMetric u x y = if qSep u x y = true then 1 else 0 := by
  by_cases hx : x ∈ u.sideA <;> by_cases hy : y ∈ u.sideA <;>
    simp only [SplitMetric, qSep, mem_sideB_iff_not_mem_sideA, hx, hy] <;> norm_num

/-- **W-配对**的布尔判据：`{a,a'}` 同侧、`{b,b'}` 同侧、`a` 与 `b` 异侧。 -/
abbrev qPairW (u : Split α) (a a' b b' : α) : Bool :=
  (qSep u a a' == false) && (qSep u b b' == false) && (qSep u a b == true)

/-- **P-配对**的布尔判据：`{a,b}` 同侧、`{a',b'}` 同侧、`a` 与 `a'` 异侧。 -/
abbrev qPairP (u : Split α) (a a' b b' : α) : Bool :=
  (qSep u a b == false) && (qSep u a' b' == false) && (qSep u a a' == true)

/-- **X-配对**的布尔判据：`{a,b'}` 同侧、`{a',b}` 同侧、`a` 与 `a'` 异侧。 -/
abbrev qPairX (u : Split α) (a a' b b' : α) : Bool :=
  (qSep u a b' == false) && (qSep u a' b == false) && (qSep u a a' == true)

/-- 布尔 W-判据 ⟺ `u` 在四元组上诱导 `{a,a'}|{b,b'}`。 -/
theorem qPairW_eq_true_iff (u : Split α) (a a' b b' : α) :
    qPairW u a a' b b' = true ↔ u.Separates a a' b b' := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [qPairW, qSep, Separates, mem_sideB_iff_not_mem_sideA, ha, ha', hb, hb'] <;> decide

/-- 布尔 P-判据 ⟺ `u` 在四元组上诱导 `{a,b}|{a',b'}`。 -/
theorem qPairP_eq_true_iff (u : Split α) (a a' b b' : α) :
    qPairP u a a' b b' = true ↔ u.Separates a b a' b' := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [qPairP, qSep, Separates, mem_sideB_iff_not_mem_sideA, ha, ha', hb, hb'] <;> decide

/-- 布尔 X-判据 ⟺ `u` 在四元组上诱导 `{a,b'}|{a',b}`。 -/
theorem qPairX_eq_true_iff (u : Split α) (a a' b b' : α) :
    qPairX u a a' b b' = true ↔ u.Separates a b' a' b := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [qPairX, qSep, Separates, mem_sideB_iff_not_mem_sideA, ha, ha', hb, hb'] <;> decide

/-- ★★★ **逐 split 差分恒等式（W 分量）**：`X_u − I_u = 2·[W] − 2·[X]`（五情形逐项核对）。
其中 `I_u = δ_u(a,a') + δ_u(b,b')`、`X_u = δ_u(a,b') + δ_u(a',b)`。 -/
theorem splitMetric_diff_qW (u : Split α) (a a' b b' : α) :
    (SplitMetric u a b' + SplitMetric u a' b) - (SplitMetric u a a' + SplitMetric u b b')
      = (if qPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if qPairX u a a' b b' = true then (2 : ℝ) else 0) := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [SplitMetric, qPairW, qPairX, qSep, mem_sideB_iff_not_mem_sideA, ha, ha', hb, hb'] <;>
    norm_num

/-- ★★★ **逐 split 差分恒等式（P 分量）**：`X_u − P_u = 2·[P] − 2·[X]`。 -/
theorem splitMetric_diff_qP (u : Split α) (a a' b b' : α) :
    (SplitMetric u a b' + SplitMetric u a' b) - (SplitMetric u a b + SplitMetric u a' b')
      = (if qPairP u a a' b b' = true then (2 : ℝ) else 0)
        - (if qPairX u a a' b b' = true then (2 : ℝ) else 0) := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [SplitMetric, qPairP, qPairX, qSep, mem_sideB_iff_not_mem_sideA, ha, ha', hb, hb'] <;>
    norm_num

/-- 指标和：`∑ w u · (if p u then c else 0) = c · ∑_{u ∈ F.filter p} w u`。 -/
theorem qSum_mul_ite_eq (F : Finset (Split α)) (w : Split α → ℝ) (p : Split α → Prop)
    [DecidablePred p] (c : ℝ) :
    (∑ u ∈ F, w u * (if p u then c else 0)) = c * ∑ u ∈ F.filter p, w u := by
  rw [Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun u _ => by by_cases h : p u <;> simp [h, mul_comm]

/-- ★★★ **拆和（W 分量）**：`X̂ − Î = 2c_W − 2c_X`（`X̂ = Σ_u w_u X_u` 等）。 -/
theorem splitMetricSum_diff_qW (F : Finset (Split α)) (w : Split α → ℝ) (a a' b b' : α) :
    (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
        - ((∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b'))
      = 2 * (∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
        - 2 * (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u) := by
  have h1 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      = ∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b) :=
    Finset.sum_add_distrib.symm
  have h2 : (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
      = ∑ u ∈ F, (w u * SplitMetric u a a' + w u * SplitMetric u b b') :=
    Finset.sum_add_distrib.symm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [show (∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b
        - (w u * SplitMetric u a a' + w u * SplitMetric u b b')))
      = ∑ u ∈ F, w u * ((if qPairW u a a' b b' = true then (2 : ℝ) else 0)
          - (if qPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by
      rw [show w u * SplitMetric u a b' + w u * SplitMetric u a' b
            - (w u * SplitMetric u a a' + w u * SplitMetric u b b')
          = w u * ((SplitMetric u a b' + SplitMetric u a' b)
            - (SplitMetric u a a' + SplitMetric u b b')) from by ring,
        splitMetric_diff_qW u a a' b b']]
  rw [show (∑ u ∈ F, w u * ((if qPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if qPairX u a a' b b' = true then (2 : ℝ) else 0)))
      = ∑ u ∈ F, (w u * (if qPairW u a a' b b' = true then (2 : ℝ) else 0)
        - w u * (if qPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by ring]
  rw [Finset.sum_sub_distrib,
    qSum_mul_ite_eq F w (fun u => qPairW u a a' b b' = true) 2,
    qSum_mul_ite_eq F w (fun u => qPairX u a a' b b' = true) 2]

/-- ★★★ **拆和（P 分量）**：`X̂ − P̂ = 2c_P − 2c_X`。 -/
theorem splitMetricSum_diff_qP (F : Finset (Split α)) (w : Split α → ℝ) (a a' b b' : α) :
    (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
        - ((∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b'))
      = 2 * (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u)
        - 2 * (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u) := by
  have h1 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      = ∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b) :=
    Finset.sum_add_distrib.symm
  have h2 : (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
      = ∑ u ∈ F, (w u * SplitMetric u a b + w u * SplitMetric u a' b') :=
    Finset.sum_add_distrib.symm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [show (∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b
        - (w u * SplitMetric u a b + w u * SplitMetric u a' b')))
      = ∑ u ∈ F, w u * ((if qPairP u a a' b b' = true then (2 : ℝ) else 0)
          - (if qPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by
      rw [show w u * SplitMetric u a b' + w u * SplitMetric u a' b
            - (w u * SplitMetric u a b + w u * SplitMetric u a' b')
          = w u * ((SplitMetric u a b' + SplitMetric u a' b)
            - (SplitMetric u a b + SplitMetric u a' b')) from by ring,
        splitMetric_diff_qP u a a' b b']]
  rw [show (∑ u ∈ F, w u * ((if qPairP u a a' b b' = true then (2 : ℝ) else 0)
        - (if qPairX u a a' b b' = true then (2 : ℝ) else 0)))
      = ∑ u ∈ F, (w u * (if qPairP u a a' b b' = true then (2 : ℝ) else 0)
        - w u * (if qPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by ring]
  rw [Finset.sum_sub_distrib,
    qSum_mul_ite_eq F w (fun u => qPairP u a a' b b' = true) 2,
    qSum_mul_ite_eq F w (fun u => qPairX u a a' b b' = true) 2]

/-- ★★★ **弱相容的互斥（弱相容版）**：三种配对**不同时**被实现。

★ 与两两相容版的差别：那里是「**任意两种**都互斥」（`not_compatible_of_separates`）；
弱相容**只**禁止**三者同时**被实现（`HasConflictingQuartet` 的定义要三个成员）。
正是这一处差别使 `c_P = c_X = 0` 失效，必须换成加权计数
（`c_W ≤ c_P`、`c_W ≤ c_X` ＋ `c_P·c_X = 0`）。 -/
theorem not_all_three_quartetPair_of_weaklyCompatible {F : Finset (Split α)}
    (hF : WeaklyCompatible (↑F : Set (Split α))) (a a' b b' : α) :
    ¬ ((∃ u ∈ F, qPairW u a a' b b' = true) ∧ (∃ v ∈ F, qPairP v a a' b b' = true) ∧
        (∃ z ∈ F, qPairX z a a' b b' = true)) := by
  rintro ⟨⟨u, huF, huW⟩, ⟨v, hvF, hvP⟩, ⟨z, hzF, hzX⟩⟩
  exact hF ⟨a, a', b, b', ⟨u, by simpa using huF, (qPairW_eq_true_iff u a a' b b').mp huW⟩,
    ⟨v, by simpa using hvF, (qPairP_eq_true_iff v a a' b b').mp hvP⟩,
    ⟨z, by simpa using hzF, (qPairX_eq_true_iff z a a' b b').mp hzX⟩⟩

/-- ★★★★ **弱相容下的「成员半边」**（W26 泳道 d，本文件 §7.2）：`F` **弱相容**、`w > 0` 于 `F`、
`t ∈ F` ⇒ `t` 的两侧是 `δ := Σ_{u∈F} w_u·δ_u` 的 **`d`-split**（`IsDSplit`）。

* **这是 `weakCompatibilityRealization_gap`（`SplitWeak.lean:562`）成员方向的第一次推进**：W22
  `Split.isDSplit_splitMetricSum_of_mem` 只对**两两相容**成立，弱相容版此前**空白**；
* **不需要**任何度量公理、对称性、`δ x x = 0`：纯组合计数；
* **退化四元组自动覆盖**（`a = a'` 或 `b = b'`：`P̂`、`X̂` 同批项，`t` 提供 `2w_t > 0` 的余量）。 -/
theorem isDSplit_splitMetricSum_of_mem_of_weaklyCompatible (F : Finset (Split α))
    (w : Split α → ℝ) (hF : WeaklyCompatible (↑F : Set (Split α)))
    (hw : ∀ s ∈ F, 0 < w s) {t : Split α} (ht : t ∈ F) :
    IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  classical
  intro a ha a' ha' b hb b' hb'
  have hba : b ∉ t.sideA := (t.mem_sideB_iff_not_mem_sideA b).mp hb
  have hb'a : b' ∉ t.sideA := (t.mem_sideB_iff_not_mem_sideA b').mp hb'
  have hWt : qPairW t a a' b b' = true := by
    simp [qPairW, qSep, ha, ha', hba, hb'a]
  set Iv : ℝ := (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
    with hIv
  set Pv : ℝ := (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
    with hPv
  set Xv : ℝ := (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
    with hXv
  have hcW : 0 < ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u := by
    have hle : ∀ u ∈ F.filter (fun u => qPairW u a a' b b' = true), 0 ≤ w u :=
      fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
    have h1 : w t ≤ ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u :=
      Finset.single_le_sum hle (Finset.mem_filter.mpr ⟨ht, hWt⟩)
    linarith [hw t ht]
  have hXW := splitMetricSum_diff_qW F w a a' b b'
  have hXP := splitMetricSum_diff_qP F w a a' b b'
  have hexc := not_all_three_quartetPair_of_weaklyCompatible hF a a' b b'
  refine not_le.mp ?_
  intro hle
  rw [max_le_iff] at hle
  obtain ⟨hPI, hXI⟩ := hle
  have hcX : (∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
      ≤ ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u := by linarith
  have hcP : (∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
      ≤ ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u := by linarith
  have hPpos : 0 < ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u := by linarith
  have hXpos : 0 < ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u := by linarith
  have hneP : (F.filter (fun u => qPairP u a a' b b' = true)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (F.filter (fun u => qPairP u a a' b b' = true)) with h | h
    · rw [h] at hPpos; simp at hPpos
    · exact h
  have hneX : (F.filter (fun u => qPairX u a a' b b' = true)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (F.filter (fun u => qPairX u a a' b b' = true)) with h | h
    · rw [h] at hXpos; simp at hXpos
    · exact h
  obtain ⟨v, hv⟩ := hneP
  obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
  obtain ⟨z, hz⟩ := hneX
  obtain ⟨hzF, hzX⟩ := Finset.mem_filter.mp hz
  exact hexc ⟨⟨t, ht, hWt⟩, ⟨v, hvF, hvP⟩, ⟨z, hzF, hzX⟩⟩

/-- `SplitMetric` 对两个自变量对称。 -/
theorem splitMetric_symm (u : Split α) (x y : α) : SplitMetric u x y = SplitMetric u y x := by
  by_cases hx : x ∈ u.sideA <;> by_cases hy : y ∈ u.sideA <;>
    simp only [SplitMetric, mem_sideB_iff_not_mem_sideA, hx, hy] <;> norm_num

/-- 加权和也对称（`isDSplit_comm` 的对称性前提）。 -/
theorem splitMetricSum_symm (F : Finset (Split α)) (w : Split α → ℝ) (x y : α) :
    (∑ u ∈ F, w u * SplitMetric u x y) = ∑ u ∈ F, w u * SplitMetric u y x :=
  Finset.sum_congr rfl fun u _ => by rw [splitMetric_symm u x y]

/-- ★★★★ **「成员半边」的最终形态（含 `swap`）**：`F` 弱相容、`w > 0` 于 `F`，
且 `t ∈ F` **或** `t.swap ∈ F` ⇒ `t` 的两侧是 `δ := Σ_{u∈F} w_u·δ_u` 的 `d`-split。

★ 前提 `t ∈ F ∨ t.swap ∈ F` **逐字**就是 `weakCompatibilityRealization_gap`（`SplitWeak.lean:562`）
结论右边 `∃ t ∈ F, t = s ∨ t.swap = s` 里**成员方向**的那一半 ⇒ 本定理给出该 `∃` 的第 **`→`** 半边
（★ 剩下的「非成员不是 d-split」即弱相容版 **(B2)**，仍缺 —— 见本文件 §7.1）。 -/
theorem isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible (F : Finset (Split α))
    (w : Split α → ℝ) (hF : WeaklyCompatible (↑F : Set (Split α)))
    (hw : ∀ s ∈ F, 0 < w s) {t : Split α} (ht : t ∈ F ∨ t.swap ∈ F) :
    IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  rcases ht with ht | ht
  · exact isDSplit_splitMetricSum_of_mem_of_weaklyCompatible F w hF hw ht
  · have h := isDSplit_splitMetricSum_of_mem_of_weaklyCompatible F w hF hw ht
    simp only [swap_sideA, swap_sideB] at h
    exact (isDSplit_comm (fun x y => splitMetricSum_symm F w x y)).mp h

/-! ## 7.3 ★★★★ W26 泳道 d：**(B2) 的计数判据 + `2+2` 情形证成**

### 本批证成什么

§7.2 只给了 `weakCompatibilityRealization_gap`（`:562`）的**成员**半边。缺口剩下的唯一一块 =
**非成员**方向：`t ∉ F` 且 `t.swap ∉ F` ⇒ `t` **不是** `δ := Σ_{u∈F} w_u δ_u` 的 `d`-split
（= 弱相容版 **(B2)**，即 `notIsDSplit_of_splitMetricSum_gap`（`:688`）去掉两两相容、换成弱相容）。

本批把 (B2) **精确归约成一条纯计数命题**，并**证成两个非平凡特化**：

1. ★★★ `splitMetricSum_isDSplit_iff`（计数判据）：`IsDSplit (Σ_{u∈F} w_u δ_u) A B` **⟺**
   对**每个**四元组 `a,a' ∈ A`、`b,b' ∈ B` 都有 `min c_P c_X < c_W`，其中
   `c_W = Σ_{u ∈ F: u 实现 {a,a'}|{b,b'}} w_u`（`c_P`、`c_X` 同理，即 `qPairW/qPairP/qPairX` 的加权和）。
   这是 §7.2 两条差分恒等式的直接推论：`X̂ − Î = 2(c_W − c_X)`、`X̂ − P̂ = 2(c_P − c_X)`
   ⇒ `max P̂ X̂ − Î = 2·max (c_W − c_P) (c_W − c_X)`。
2. ★★★ `not_isDSplit_splitMetricSum_of_quartet_le`：(B2) 的**见证式** ——
   只要**找到**一个四元组使 `c_W ≤ min c_P c_X`，(B2) 对**该** `t` 立刻成立（零额外假设）。
3. ★★★★ `not_isDSplit_splitMetricSum_of_no_qPairW`：更强的**充分条件**，且与 `w` **无关**：
   若某四元组上**没有** `F` 的成员实现 W-配对（`c_W = 0`），则 `t` 不是 `d`-split
   （= `not_isDSplit_splitMetricSum_of_quartet_le` 的「零权重」特例）。
4. ★★★★ `not_isDSplit_of_weaklyCompatible_of_sideA_card_two`：**(B2) 的 `2+2` 情形已证成**
   —— `t.sideA.card = 2`、`t.sideB.card = 2`（即 `n = 4` 的 2|2 split）、`t ∉ F`、`t.swap ∉ F`
   ⇒ `¬ IsDSplit`。证明只用 `eq_of_le_sides`：四元组只能是 `t` 的两侧本身，
   此时 `u` 实现 W-配对 ⇒ `u` 的两侧分别**包含** `t` 的两侧 ⇒ `u = t` 或 `u = t.swap` ⇒ 矛盾 ∎
   （★ 这一条**完全不用**弱相容 —— 是 (B2) 的「无假设」特化。）

### 精确卡点：(B2) 全一般情形还缺什么

由 (1)，(B2) **等价于**下面这条**纯组合计数**命题（不含 `IsDSplit`、不含任何度量）：

> **(B2-core)** 设 `F` 弱相容、`w > 0` 于 `F`、`t ∉ F`、`t.swap ∉ F`，则**存在**
> `a,a' ∈ t.sideA`、`b,b' ∈ t.sideB` 使 `c_W ≤ min c_P c_X`。

★ 两两相容版（`BunemanIndexBridge.lean:2268`）**绕开**了这条：那里 `c_P·c_X = 0`
＋ cluster 层析性直接给出。弱相容下**两个对手**（P、X）可**同时**为正 ⇒ 必须**显式构造**四元组。

★★ **手算反例否定了一条捷径**（即「`c_W = 0` 的加强版」为假；W26-d 手工核验，**未**形式化）：
取 `X = {a,1,2,3,4,5}`、`t = {a}|{1,2,3,4,5}`、
`F = {{a,4,5}|{1,2,3}, {a,3,5}|{1,2,4}, {a,3,4}|{1,2,5}, {a,1,2}|{3,4,5}}`，
四成员的「远侧」`{1,2,3}`、`{1,2,4}`、`{1,2,5}`、`{3,4,5}` **覆盖 `B` 的全部 `10` 个二元子集**
⇒ **每个**四元组都有 W-成员 ⇒ `not_isDSplit_splitMetricSum_of_no_qPairW` **不足以**证 (B2)；
必须用带权的 `c_W ≤ min c_P c_X`。★ 该 `F` 恰**不**弱相容：`{a,1,3,4}` 上三个成员分别诱导
`{a,4}|{1,3}`、`{a,3}|{1,4}`、`{a,1}|{3,4}` ⇒ 冲突四元组 —— 这正是 (B2) 真正需要的机制
（「远侧覆盖」＋ 弱相容性 ⇒ 冲突四元组）。★ 该机制在 `|t.sideB| = 3` 时**已形式化**（§7.3.1：
「每对都被覆盖 ⇒ 三个覆盖成员给出冲突四元组」），`|t.sideB| ≥ 4`（即 `|X| ≥ 5`）**仍开放**。 -/

/-- `sideA` 相同的两个 split 相等（`sideB = sideAᶜ` 由「不交 + 并 = 全集」决定）。 -/
theorem eq_of_sideA_eq {s t : Split α} (h : s.sideA = t.sideA) : s = t := by
  refine (KPartition.eq_iff_parts s t).mpr ?_
  funext i
  fin_cases i
  · exact h
  · show s.sideB = t.sideB
    rw [sideB_eq_sdiff, sideB_eq_sdiff, h]

/-- **两侧都被包含 ⟹ 相等**（(B2) 的 `2+2` 情形靠它把「包含」升级成「相同」）。 -/
theorem eq_of_le_sides {s t : Split α} (hA : t.sideA ⊆ s.sideA) (hB : t.sideB ⊆ s.sideB) :
    t = s := by
  refine eq_of_sideA_eq (Finset.Subset.antisymm hA ?_)
  intro x hx
  exact mem_sideA_of_not_mem_sideB t fun hc =>
    (Finset.disjoint_left.mp s.disjoint_sides) hx (hB hc)

/-- ★★★ **四元组计数判据（逐点形态）**。记
`Î = δ(a,a') + δ(b,b')`、`P̂ = δ(a,b) + δ(a',b')`、`X̂ = δ(a,b') + δ(a',b)`，
`c_W`、`c_P`、`c_X` 为三种配对在 `F` 上的**权重和**。则

`Î < max P̂ X̂  ⟺  min c_P c_X < c_W`。

**证明**：§7.2 的两条差分恒等式给 `X̂ − Î = 2(c_W − c_X)`、`X̂ − P̂ = 2(c_P − c_X)`，
两式相减得 `P̂ − Î = 2(c_W − c_P)`；于是
`max P̂ X̂ − Î = max (P̂ − Î) (X̂ − Î) = 2·max (c_W − c_P) (c_W − c_X)`，
而 `0 < max (c_W − c_P) (c_W − c_X) ⟺ c_W > c_P ∨ c_W > c_X ⟺ min c_P c_X < c_W` ∎
（★ **退化四元组**同样成立：恒等式不假设四点互异。） -/
theorem splitMetricSum_quartet_lt_iff (F : Finset (Split α)) (w : Split α → ℝ)
    (a a' b b' : α) :
    ((∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
        < max ((∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b'))
              ((∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)))
      ↔ min (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u)
            (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u)
          < ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u := by
  have hXW := splitMetricSum_diff_qW F w a a' b b'
  have hXP := splitMetricSum_diff_qP F w a a' b b'
  rw [lt_max_iff, min_lt_iff]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- ★★★ **`IsDSplit` 的计数判据**（★★★★ W26-d 的核心器材）：`Σ_{u∈F} w_u δ_u` 在 `A|B` 上是
`d`-split **⟺** 每个四元组的 W-权重**严格大于**两个对手权重的**较小者**。

★ 这把 (B2) 变成一条**不含度量**的计数命题：见本节头部的 **(B2-core)**。 -/
theorem splitMetricSum_isDSplit_iff (F : Finset (Split α)) (w : Split α → ℝ)
    (A B : Finset α) :
    IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) A B
      ↔ ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
          min (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u)
              (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u)
            < ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u := by
  unfold IsDSplit
  simp only [splitMetricSum_quartet_lt_iff]

/-- ★★★★ **(B2) 的见证式**（本批的**可执行卡点**）：只要找到**一个**四元组使 W-权重
不超过两个对手权重的较小者，(B2) 对该 `t` 就成立 —— **不需要**弱相容、不需要任何度量公理。

★ 与 §7.2 成员半边**对偶**：那里靠「`t ∈ F` ⇒ `c_W ≥ w_t > 0`」；这里靠「造一个 `c_W` 被打平的
四元组」。缺的正是「怎么造」（见 (B2-core) 与头部卡点分析）。 -/
theorem not_isDSplit_splitMetricSum_of_quartet_le (F : Finset (Split α)) (w : Split α → ℝ)
    {A B : Finset α} {a a' b b' : α} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : (∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
        ≤ min (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u)
            (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u)) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) A B := by
  intro hD
  have := (splitMetricSum_isDSplit_iff F w A B).mp hD a ha a' ha' b hb b' hb'
  linarith

/-- ★★★★ **(B2) 的充分条件**（与 `w` **无关**）：若某四元组上**没有** `F` 的成员实现 W-配对，
则 `t` 不是 `d`-split。

★ 手算已否掉「此条件总能满足」：见本节头部的 `F`（远侧覆盖 `B` 的全部二元子集，但**不**弱相容；W26-d 手工核验，**未**形式化）。 -/
theorem not_isDSplit_splitMetricSum_of_no_qPairW (F : Finset (Split α)) (w : Split α → ℝ)
    (hw : ∀ s ∈ F, 0 < w s)
    {A B : Finset α} {a a' b b' : α} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (hW : ∀ u ∈ F, qPairW u a a' b b' ≠ true) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) A B := by
  refine not_isDSplit_splitMetricSum_of_quartet_le F w ha ha' hb hb' ?_
  have hempty : F.filter (fun u => qPairW u a a' b b' = true) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun u hu => hW u hu
  rw [hempty]
  simp only [Finset.sum_empty]
  exact le_min (Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1))
    (Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1))

/-- ★★★★ **(B2) 的 `2+2` 情形**（`n = 4` 的 2|2 split；★ **不用**弱相容）：

`|t.sideA| = |t.sideB| = 2`、`t ∉ F`、`t.swap ∉ F` ⇒ `t` **不是** `δ = Σ_{u∈F} w_u δ_u` 的 `d`-split。

**证明**：`t` 的两侧就是**唯一**的四元组（`a,a'` 与 `b,b'` 两两取自两侧）。若 `u ∈ F` 在该四元组上
实现 W-配对，则 `u` 的两侧分别**包含** `t.sideA = {a,a'}` 与 `t.sideB = {b,b'}`；
`eq_of_le_sides` 给 `u = t`（或 `u = t.swap`，另一取向），与 `t ∉ F`、`t.swap ∉ F` 矛盾
⇒ 该四元组无 W-成员 ⇒ `not_isDSplit_splitMetricSum_of_no_qPairW` ∎ -/
theorem not_isDSplit_of_weaklyCompatible_of_sideA_card_two (F : Finset (Split α))
    (w : Split α → ℝ) (hw : ∀ s ∈ F, 0 < w s) {t : Split α}
    (ht : t ∉ F) (hts : t.swap ∉ F)
    (hA : t.sideA.card = 2) (hB : t.sideB.card = 2) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  classical
  obtain ⟨a, a', haa, hAeq⟩ := Finset.card_eq_two.mp hA
  obtain ⟨b, b', hbb, hBeq⟩ := Finset.card_eq_two.mp hB
  have ha : a ∈ t.sideA := by rw [hAeq]; simp
  have ha' : a' ∈ t.sideA := by rw [hAeq]; simp
  have hb : b ∈ t.sideB := by rw [hBeq]; simp
  have hb' : b' ∈ t.sideB := by rw [hBeq]; simp
  refine not_isDSplit_splitMetricSum_of_no_qPairW F w hw ha ha' hb hb' ?_
  intro u hu hW
  have hsep : u.Separates a a' b b' := (qPairW_eq_true_iff u a a' b b').mp hW
  rcases hsep with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine ht ?_
    have hAt : t.sideA ⊆ u.sideA := by
      intro z hz
      rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    have hBt : t.sideB ⊆ u.sideB := by
      intro z hz
      rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      · rw [h]; exact h3
      · rw [h]; exact h4
    rw [eq_of_le_sides hAt hBt]; exact hu
  · refine hts ?_
    have hAt : t.sideA ⊆ u.swap.sideA := by
      rw [swap_sideA]
      intro z hz
      rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    have hBt : t.sideB ⊆ u.swap.sideB := by
      rw [swap_sideB]
      intro z hz
      rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      · rw [h]; exact h3
      · rw [h]; exact h4
    rw [eq_of_le_sides hAt hBt, swap_swap]; exact hu

/-! ### 7.3.1 ★★★★ `1+3` 情形与「`|X| = 4` 上 (B2) 完全证成」

`1+3` 情形（`t = {a} | {b₁,b₂,b₃}`）是**唯一**必须真用弱相容性的特化：
`t.sideA` 只有一点 ⇒ 四元组必然退化（`a = a'`），此时 `c_P = c_X = 0`，要 `c_W = 0`，
即必须找到**一对** `b,b' ∈ t.sideB` 使 `F` 中**没有**成员把 `a` 与 `b,b'` 分开。

★ 反证：若**每一对**都被覆盖，取覆盖 `{b₁,b₂}`、`{b₁,b₃}`、`{b₂,b₃}` 的三个成员 `u₁₂,u₁₃,u₂₃`。
被 `u` 覆盖 ⇒ `u` 的「远侧」（不含 `a` 的那侧）**包含** `{bᵢ,bⱼ}`；远侧 `⊆ t.sideB`（因 `a` 不在其上）；
远侧 `≠ t.sideB`（否则 `u = t` 或 `u = t.swap`，与 `t ∉ F`、`t.swap ∉ F` 矛盾）
⇒ 远侧**恰是** `{bᵢ,bⱼ}`（`t.sideB` 只有三元）⇒ `u` 的另侧是 `{a, b_k}`
⇒ `uᵢⱼ.Separates a b_k bᵢ bⱼ`。三个成员在四点组 `(a, b₁, b₂, b₃)` 上分别诱导
`{a,b₃}|{b₁,b₂}`、`{a,b₂}|{b₁,b₃}`、`{a,b₁}|{b₂,b₃}` = **三个不同的 2|2 配对**
⇒ `HasConflictingQuartet` ⇒ 与**弱相容矛盾** ∎

⇒ 由此得到 `not_isDSplit_of_weaklyCompatible_of_sideA_card_one`，
并与 `2+2` 情形合并成 **`|X| = 4` 上 (B2) 的完整证明**
`not_isDSplit_of_weaklyCompatible_of_card_univ_four`（`2|2` 与 `1|3`／`3|1` 覆盖全部分拆方式）。
-/

/-- ★★★★ **(B2) 的 `1+3` 情形**（`|t.sideA| = 1`、`|t.sideB| = 3`；★ 这里**必须**用弱相容）：

`F` 弱相容、`w > 0` 于 `F`、`t ∉ F`、`t.swap ∉ F` ⇒ `t` **不是** `δ = Σ_{u∈F} w_u δ_u` 的 `d`-split。

**证明**（详见本节头）：退化四元组（`a = a'`）使 `c_P = c_X = 0`，故只需找到一对 `b,b' ∈ t.sideB`
不被任何成员「与 `a` 分开」；若每对都被覆盖，则三个覆盖成员在 `(a,b₁,b₂,b₃)` 上诱导三个不同 2|2
配对，与弱相容矛盾（`hF`）∎ -/
theorem not_isDSplit_of_weaklyCompatible_of_sideA_card_one (F : Finset (Split α))
    (w : Split α → ℝ) (hF : WeaklyCompatible (↑F : Set (Split α)))
    (hw : ∀ s ∈ F, 0 < w s) {t : Split α} (ht : t ∉ F) (hts : t.swap ∉ F)
    (hA : t.sideA.card = 1) (hB : t.sideB.card = 3) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  classical
  obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp hA
  obtain ⟨b1, b2, b3, _, _, _, hBeq⟩ := Finset.card_eq_three.mp hB
  have ha : a ∈ t.sideA := by rw [hAeq]; simp
  have hb1 : b1 ∈ t.sideB := by rw [hBeq]; simp
  have hb2 : b2 ∈ t.sideB := by rw [hBeq]; simp
  have hb3 : b3 ∈ t.sideB := by rw [hBeq]; simp
  -- ★ 关键：「第三点」必与 `a` 同侧（情形 `a ∈ u.sideA`）
  have keyA : ∀ {u : Split α} {p q r : α}, u ∈ F → t.sideB = {p, q, r} →
      a ∈ u.sideA → p ∈ u.sideB → q ∈ u.sideB → r ∈ u.sideA := by
    intro u p q r huF hBs hau hpu hqu
    by_contra hru
    have hru' : r ∈ u.sideB := mem_sideB_of_not_mem_sideA u hru
    have hBsub : t.sideB ⊆ u.sideB := by
      rw [hBs]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact hpu
      · rw [h]; exact hqu
      · rw [h]; exact hru'
    have hAsub : t.sideA ⊆ u.sideA := by
      rw [hAeq]
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact hau
    exact ht (by rw [eq_of_le_sides hAsub hBsub]; exact huF)
  -- ★ 对偶情形（`a ∈ u.sideB`）：换成与 `u.swap` 比
  have keyB : ∀ {u : Split α} {p q r : α}, u ∈ F → t.sideB = {p, q, r} →
      a ∈ u.sideB → p ∈ u.sideA → q ∈ u.sideA → r ∈ u.sideB := by
    intro u p q r huF hBs hau hpu hqu
    by_contra hru
    have hru' : r ∈ u.sideA := mem_sideA_of_not_mem_sideB u hru
    have hAsub : t.sideA ⊆ u.swap.sideA := by
      rw [swap_sideA, hAeq]
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact hau
    have hBsub : t.sideB ⊆ u.swap.sideB := by
      rw [swap_sideB, hBs]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact hpu
      · rw [h]; exact hqu
      · rw [h]; exact hru'
    have hts' : t = u.swap := eq_of_le_sides hAsub hBsub
    exact hts (by rw [hts', swap_swap]; exact huF)
  -- 由「被覆盖」得到 `Separates a r p q`
  have sep3 : ∀ {u : Split α} {p q r : α}, u ∈ F → qPairW u a a p q = true →
      t.sideB = {p, q, r} → u.Separates a r p q := by
    intro u p q r huF hW hBs
    have hsep : u.Separates a a p q := (qPairW_eq_true_iff u a a p q).mp hW
    rcases hsep with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, keyA huF hBs h1 h3 h4, h3, h4⟩
    · exact Or.inr ⟨h1, keyB huF hBs h1 h3 h4, h3, h4⟩
  have hBeq231 : t.sideB = {b2, b3, b1} := by
    rw [hBeq]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hBeq132 : t.sideB = {b1, b3, b2} := by
    rw [hBeq]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- 若每对都被覆盖 ⇒ 冲突四元组 ⇒ 与弱相容矛盾
  have hcontr : ¬ (∀ p ∈ t.sideB, ∀ q ∈ t.sideB, ∃ u ∈ F, qPairW u a a p q = true) := by
    intro hall
    obtain ⟨u12, hu12F, hu12⟩ := hall b1 hb1 b2 hb2
    obtain ⟨u13, hu13F, hu13⟩ := hall b1 hb1 b3 hb3
    obtain ⟨u23, hu23F, hu23⟩ := hall b2 hb2 b3 hb3
    exact hF ⟨a, b1, b2, b3,
      ⟨u23, by simpa using hu23F, sep3 hu23F hu23 hBeq231⟩,
      ⟨u13, by simpa using hu13F, sep3 hu13F hu13 hBeq132⟩,
      ⟨u12, by simpa using hu12F, sep3 hu12F hu12 hBeq⟩⟩
  -- 故存在未被覆盖的一对
  have hun : ∃ p ∈ t.sideB, ∃ q ∈ t.sideB, ∀ u ∈ F, qPairW u a a p q ≠ true := by
    by_contra hcon
    apply hcontr
    intro p hp q hq
    by_contra hex
    exact hcon ⟨p, hp, q, hq, fun u hu hW => hex ⟨u, hu, hW⟩⟩
  obtain ⟨p, hp, q, hq, huniv⟩ := hun
  exact not_isDSplit_splitMetricSum_of_no_qPairW F w hw ha ha hp hq huniv

/-- ★★★★★ **(B2) 在 `|X| = 4` 上**完全证成（`weakCompatibilityRealization_gap` 的非成员半边，
`Fintype.card α = 4` 情形）：

`F` 弱相容、`w > 0` 于 `F`、`t ∉ F`、`t.swap ∉ F` ⇒ `t` 不是 `δ = Σ_{u∈F} w_u δ_u` 的 `d`-split。

**证明**：`t` 的两侧非空且并为全集 ⇒ `(|t.sideA|, |t.sideB|) ∈ {(1,3), (2,2), (3,1)}`
⇒ 分别是 `not_isDSplit_of_weaklyCompatible_of_sideA_card_one`（`(3,1)` 用 `t.swap` ＋
`isDSplit_comm` 归约）与 `not_isDSplit_of_weaklyCompatible_of_sideA_card_two` ∎

⇒ 与 §7.2 的成员半边合并：**`|X| = 4` 时 `weakCompatibilityRealization_gap` 的 `↔` 两个方向都成立**
（全一般情形仍缺 `(B2-core)`，见 §7.3 结尾的卡点分析）。 -/
theorem not_isDSplit_of_weaklyCompatible_of_card_univ_four (F : Finset (Split α))
    (w : Split α → ℝ) (hF : WeaklyCompatible (↑F : Set (Split α)))
    (hw : ∀ s ∈ F, 0 < w s) {t : Split α} (ht : t ∉ F) (hts : t.swap ∉ F)
    (hcard : Fintype.card α = 4) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  classical
  have hApos : 0 < t.sideA.card := Finset.card_pos.mpr (t.nonempty 0)
  have hBpos : 0 < t.sideB.card := Finset.card_pos.mpr (t.nonempty 1)
  have hsum : t.sideA.card + t.sideB.card = 4 := by
    have h := Finset.card_union_of_disjoint t.disjoint_sides
    rw [t.union_sides, Finset.card_univ, hcard] at h
    omega
  have hcases : t.sideA.card = 1 ∨ t.sideA.card = 2 ∨ t.sideA.card = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · exact not_isDSplit_of_weaklyCompatible_of_sideA_card_one F w hF hw ht hts h1 (by omega)
  · exact not_isDSplit_of_weaklyCompatible_of_sideA_card_two F w hw ht hts h2 (by omega)
  · have hB3 : t.sideB.card = 1 := by omega
    have hsw := not_isDSplit_of_weaklyCompatible_of_sideA_card_one F w hF hw
      (t := t.swap) (by simpa using hts) (by simpa using ht) (by simpa using hB3) (by simpa using h3)
    intro hD
    refine hsw ?_
    simpa only [swap_sideA, swap_sideB] using
      (isDSplit_comm (A := t.sideA) (B := t.sideB) (fun x y => splitMetricSum_symm F w x y)).mp hD

/-! ### 7.3.2 ★★★★★ `weakCompatibilityRealization_gap` 在 `|X| = 4` 上**整体收口**

把 §7.2 的**成员**半边与 §7.3.1 的**非成员**半边（`not_isDSplit_of_weaklyCompatible_of_card_univ_four`）
合成 `∃ δ` 的**完整**双向刻画 —— 即 `weakCompatibilityRealization_gap`（`:562`）在 `|X| = 4` 时**逐字成立**：

`F` 弱相容、`w > 0` 于 `F` ⇒ 取 `δ := Σ_{u∈F} w_u·δ_u`，则
`∀ s, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s`（**两个方向都证**）。

★ 全一般 `α` 仍缺 `(B2-core)`（§7.3 头部）；本定理把「缺哪一件」与「已到哪一步」
压到同一句话上：**`n = 4` 已无缺口，`n ≥ 5` 只差 `(B2-core)`**。 -/
theorem weakCompatibilityRealization_gap_card_four {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 4) (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ s ∈ F, 0 < w s) :
    ∃ δ : α → α → ℝ, (∀ x y, δ x y = δ y x) ∧
      ∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s := by
  classical
  refine ⟨fun x y => ∑ u ∈ F, w u * SplitMetric u x y, fun x y => splitMetricSum_symm F w x y,
    fun s => ?_⟩
  constructor
  · intro hD
    by_contra hcon
    have hs : s ∉ F := fun h => hcon ⟨s, h, Or.inl rfl⟩
    have hss : s.swap ∉ F := fun h => hcon ⟨s.swap, h, Or.inr (by simp)⟩
    exact not_isDSplit_of_weaklyCompatible_of_card_univ_four F w hF hw hs hss hcard hD
  · rintro ⟨t, htF, h | h⟩
    · exact isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible F w hF hw
        (Or.inl (h ▸ htF))
    · exact isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible F w hF hw
        (Or.inr (by rw [show s.swap = t by rw [← h, swap_swap]]; exact htF))

end Split

/-! ## 8. 树的 split 系统弱相容（`Phylo/Split.lean:894` 的接口） -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★ **树的 split 系统弱相容**：`pairwiseCompatible`（`Phylo/Split.lean:894`）+ 强 ⟹ 弱。

⚠️ 这是**树特例**；`RootedTree.DisplaysSplit` 侧的两两相容引理库内尚无
（见报告「诚实边界」）。 -/
theorem weaklyCompatible_splits (T : Cladogram X) : Split.WeaklyCompatible T.splits :=
  Split.weaklyCompatible_of_pairwiseCompatible fun s hs t ht => pairwiseCompatible T s hs t ht

end Cladogram
