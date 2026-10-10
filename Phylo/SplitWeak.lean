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

（隔离指数取 `min`，故「`min > 0`」⟺「逐对全为正」。） -/
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

/-- **split-prime**：对**每个** split 的隔离指数都是 `0`（文献 673–684 行）。 -/
def SplitPrime (δ : α → α → ℝ) : Prop := ∀ A B : Finset α, ¬ IsDSplit δ A B

/-- **四点条件**（文献 503–509 行）：三个表达式中**最大者至少取到两次**。

即 `d(a,a')+d(b,b')`、`d(a,b)+d(a',b')`、`d(a,b')+d(a',b)` 中最大者不唯一。 -/
def FourPoint (δ : α → α → ℝ) : Prop :=
  ∀ a a' b b' : α,
    δ a a' + δ b b' ≤ max (δ a b + δ a' b') (δ a b' + δ a' b) ∧
      δ a b + δ a' b' ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) ∧
        δ a b' + δ a' b ≤ max (δ a a' + δ b b') (δ a b + δ a' b)

/-- ⬜ **缺口 1（Theorem 3 的逆，1683–1699 行）**：弱相容 ⟹ `Σ` 恰是某个对称 `δ` 的
`d`-split 全体（取 `δ := Σ_{S∈Σ} λ_S δ_S`，`λ_S > 0`，且隔离指数 `α_S = λ_S`）。

本文件已证其**一半**（`weaklyCompatible_of_isDSplit` 的逆否：`Σ ⊆ Σ_δ`）；
「`Σ_δ ⊆ Σ`」（非成员的隔离指数为 `0`）需要隔离指数的层析论证，未落。 -/
def weakCompatibilityRealization_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    WeaklyCompatible (↑F : Set (Split α)) → (∀ s ∈ F, 0 < w s) →
      ∃ δ : α → α → ℝ, (∀ x y, δ x y = δ y x) ∧
        ∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s

/-- ⬜ **缺口 2（典范分解，1651–1655 行 Theorem 2 + 673–684 行）**：
任一对称 `δ` 可写成 `δ = δ₀ + Σ_{S ∈ Σ} c_S · δ_S`，其中 `c_S > 0`、残差 `δ₀` **split-prime**。

未落原因：需要先把「度量」「四点条件」与树的边权（`Phylogram.dist`）接起来，
并证明残差的 split-prime 性（隔离指数为 0）。 -/
def canonicalSplitDecomposition_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrime δ₀ ∧
        ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

/-- ⬜ **缺口 3（强相容 ⟺ 树度量，539–544 行）**：两两相容 ⟺ `Σ` 恰是某个**满足四点条件**的
`δ` 的 `d`-split 全体。

「⟸」方向由本文件的 ★★（强 ⟹ 弱）配合 `not_all_three_deficit_pos` 给出**弱**结论；
完整刻画还需「四点条件 ⟹ 树度量（`Phylogram.dist`）」一侧（`Phylo/BunemanTree.lean` 的 F6/T-6 接口）。 -/
def fourPointCharacterization_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) ↔
      ∃ δ : α → α → ℝ, FourPoint δ ∧
        ∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s

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
