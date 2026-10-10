/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SplitWeak

/-!
# `Phylo.Algorithm.NeighborNet` —— Neighbor-Net 与环形 split 系统（W11d / X4）

文献：D. Bryant & V. Moulton, *Neighbor-Net: an agglomerative method for the construction of
phylogenetic networks*, Molecular Biology and Evolution **21**(2) (2004) 255–265。
文本见 `references/md/BryantMoulton2004_NeighborNetAgglomerativePhylogeneticNetworks.md`；
**下文行号一律指该 md 的行号**（OCR 有损；逐字引用处以 `>` 标出）。

> ⚠️ **无新增 import**：本文件只 `import Phylo.SplitWeak`（`Phylo.Split` 由它带入）；
> 证明用到的 `omega` 来自其已带的 `Mathlib.Tactic`。这样单文件 `lean` 与 `lake build`
> 都**不产生**「Mathlib 模块系统」告警（那是每个直接 import Mathlib 的文件都会有的既有噪音）。

## 0. 文献要素与形态

| 文献行 | 内容 | 本文件 |
|---|---|---|
| 121–122 | split 的定义 | `Phylo.Split`（既有） |
| 249–253 | **相容** = 含于某棵树的 split 集 | `Split.Compatible`（既有，`Phylo/Split.lean:238`） |
| 288–328 | Neighbor-Net 的 agglomeration 迭代 | ⬜ **未形式化**（见 §P 缺口 2） |
| 321–329 | **环形 split 系统**的定义 | ★ `IsCyclicArc` / `Circular`（§1） |
| 328–337 | 环形 ⟹ splits graph **可平面**（Dress–Huson） | ⬜ 未形式化（缺口 3 的注） |
| 469–498 | 选择式 (1)(2)(3) | ⬜ 未形式化 |
| 543–565 | 约化式 (4)(5) | ⬜ 未形式化 |
| 569–845 | 最小二乘权重（含非负约束） | ⬜ 缺口 1（`A` 满秩） |
| 1058–1078 | 环形（Kalmanson）距离与一致性 | ⬜ 缺口 1 / 注 |

### 文献逐字（行号 = md 行号）

split 与相容（121–122、249–253 行）：

> "A split is a partition of the set of taxa into two disjoint, non-empty groups."
> "A collection of splits is compatible if it is contained within the set of splits of some
> phylogenetic tree; otherwise it is incompatible."

**环形族**（321–329 行）——本文件的中心定义：

> "The end-product of the Neighbor-Net process is a circular collection of splits, as can be
> proved using mathematical induction. Circular collections of splits are a mathematical
> generalization of compatible collections of splits. Formally, a collection of splits of X is
> **circular** if there is an ordering x₁, x₂, . . . , xₙ of the taxa such that every split is of
> the form {xᵢ, xᵢ₊₁, . . . , xⱼ} | X \\ {xᵢ, . . . , xⱼ} for some i and j satisfying 1 ≤ i ≤ j < n."

可平面性（328–337 行）：

> "Most importantly, Andreas Dress and Daniel Huson (personal communication) have proved that
> circular collections of splits always have a planar splits graph representation."

系统发生距离（~260–270 行）：

> "This formulation of phyletic distance extends directly to collections of splits that are not
> compatible. The phyletic distance between two taxa, with respect to a collection of weighted
> splits, equals the sum of the weights of the splits separating them."

满秩与权重（805–812、838–841 行）：

> "Neighbor-Net produces a circular collection of splits, so the corresponding matrix A has full
> rank (Bandelt and Dress 1992). The ordinary least squares (OLS) estimates for b can therefore be
> computed from the observed distance vector d using the standard formula b = (A′A)⁻¹A′d"
> "For this reason, we always compute optimal least squares estimates with a non-negativity
> constraint."

环形（Kalmanson）距离与一致性（1058–1078 行）：

> "A distance matrix is **circular** (also called Kalmanson) if it equals the phyletic distances
> for a circular collection of splits with positive weights. … If the input distance matrix is
> circular, Neighbor-Net is guaranteed to return the corresponding circular splits with their
> split weights."

## 1. 本文件证出（零 `sorry` / `axiom` / `native_decide`）

* ★★★ `weaklyCompatible_of_circular` —— **环形 ⟹ 弱相容**（文献 321–329 行给定义，
  "circular … is a mathematical generalization of compatible" 的**严格**内容：
  相容 ⟹ 弱相容是库内已有的 `Split.weaklyCompatible_of_pairwiseCompatible`，
  而环形的**反向**结构约束由本定理补上）。
  证明骨架：任意三个成员与四点在环上诱导三个 2|2 划分；由弧的区间性，每一对点
  （含共同点 `a`）在四点中**环形相邻**；但四点上至多两个这样的对
  （`not_three_cycAdj`）——矛盾。全部组合内容由 `omega` 收束。
* ★★ `cycAdj_of_arc`（传递引理）· `not_three_cycAdj`（核心组合引理）· `ne_of_separates`（四点互异）。
* ★ `Circular` 对子族封闭（`circular_mono`）、余集封闭（`isCyclicArc_iff_compl`）、
  平凡 split 族环形（`circular_of_trivial`）。
* ★B **反例检查**：`exists_circular_not_pairwiseCompatible` —— `Fin 4` 上
  `{0,1}|{2,3}` 与 `{0,2}|{1,3}` **环形但不两两相容** ⇒ 环形是相容的**严格**推广
  （文献 249–253 行的相容类真含于环形类）。`not_circular_four_quartets` ——
  `Fin 4` 上**三个** 2|2 split 全体**不是**环形（由主定理 + `Split.not_weaklyCompatible_four`）。
* ★C **最小例子**：4 taxon（`Fin 4`）上环形族、相容族、以及「至多两个 quartets」的端到端陈述；
  穷举脚本 `scripts/msc/w11d_x4_neighbor_net.py`（纯标准库、精确有理数、无 Monte Carlo）。
* ⬜ 缺口（文件末 `def … : Prop`）：Kalmanson 距离的环形实现 + `A` 满秩 + 算法主体。

⚠️ **本文件不含 Neighbor-Net 算法本体**（agglomeration 迭代 / 选择式 / 约化式 / 权重求解）。
它承载的是算法**输出类**（环形族）的组合理论：这正是文献 321–329 行用来保证一致性的那一层。
-/

namespace NeighborNet

open Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. 环形序、环形弧、环形 split 系统（文献 321–329 行） -/

/-- **非环绕弧**：位置映射 `f` 下落在下标区间 `[i,j]` 中的 taxon 全体。

文献 324–327 行的 `{xᵢ, xᵢ₊₁, …, xⱼ}`；`f` 把 taxon 送到圆上的位置。 -/
def cycArc {n : ℕ} (f : α ≃ Fin n) (i j : Fin n) : Finset α :=
  Finset.univ.filter (fun x => f x ∈ Finset.Icc i j)

omit [DecidableEq α] in
@[simp] theorem mem_cycArc {n : ℕ} (f : α ≃ Fin n) (i j : Fin n) (x : α) :
    x ∈ cycArc f i j ↔ f x ∈ Finset.Icc i j := by
  simp [cycArc]

/-- **环形弧**（cyclic arc）：`cycArc f i j` 或其余集。

⚠️ 与文献 324–327 行等价：圆上的弧与其补都是弧，故「某一侧是 `cycArc`」
（`IsCyclicArc`）与「某一侧是 `{xᵢ,…,xⱼ}`」（文献原文，另一侧取其补）刻画同一类。 -/
def IsCyclicArc {n : ℕ} (f : α ≃ Fin n) (A : Finset α) : Prop :=
  ∃ i j : Fin n, i ≤ j ∧ (A = cycArc f i j ∨ A = (cycArc f i j)ᶜ)

/-- **环形 split 系统**（文献 321–329 行）：存在一个环形序，使每个成员至少有一侧是环形弧。 -/
def Circular (F : Set (Split α)) : Prop :=
  ∃ n : ℕ, ∃ f : α ≃ Fin n, ∀ s ∈ F, IsCyclicArc f s.sideA ∨ IsCyclicArc f s.sideB

/-- 环形弧的**余集**仍是环形弧。 -/
theorem isCyclicArc_compl {n : ℕ} {f : α ≃ Fin n} {A : Finset α} (h : IsCyclicArc f A) :
    IsCyclicArc f Aᶜ := by
  rcases h with ⟨i, j, hij, h | h⟩
  · exact ⟨i, j, hij, Or.inr (by rw [h])⟩
  · exact ⟨i, j, hij, Or.inl (by rw [h, compl_compl])⟩

/-- 环形弧对**取余集封闭**（两个方向）。 -/
theorem isCyclicArc_iff_compl {n : ℕ} (f : α ≃ Fin n) {A : Finset α} :
    IsCyclicArc f A ↔ IsCyclicArc f Aᶜ :=
  ⟨isCyclicArc_compl, fun h => by simpa using isCyclicArc_compl h⟩

/-- **单点是环形弧**（取 `i = j = f x`）：文献 324–327 行的 `i = j` 情形。 -/
theorem isCyclicArc_singleton {n : ℕ} (f : α ≃ Fin n) (x : α) : IsCyclicArc f {x} := by
  refine ⟨f x, f x, le_rfl, Or.inl ?_⟩
  ext y
  simp only [mem_cycArc, Finset.mem_singleton, Finset.mem_Icc]
  exact ⟨fun h => by rw [h]; exact ⟨le_rfl, le_rfl⟩,
    fun h => f.injective (le_antisymm h.2 h.1)⟩

/-- 环形族对**子族**封闭。 -/
theorem circular_mono {F G : Set (Split α)} (h : Circular F) (hsub : G ⊆ F) : Circular G := by
  obtain ⟨n, f, hf⟩ := h
  exact ⟨n, f, fun s hs => hf s (hsub hs)⟩

/-- **平凡 split 族必环形**（每个成员有一侧是单点 ⟹ 单点是弧）。

文献 249–253 行「compatible ⟹ 含于某棵树的 split 集」的**最简特例**：
平凡 split 族相容，也环形。 -/
theorem circular_of_trivial (F : Set (Split α))
    (h : ∀ s ∈ F, (∃ x : α, s.sideA = {x}) ∨ (∃ x : α, s.sideB = {x})) : Circular F := by
  refine ⟨Fintype.card α, Fintype.equivFin α, fun s hs => ?_⟩
  rcases h s hs with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact Or.inl (hx ▸ isCyclicArc_singleton _ x)
  · exact Or.inr (hx ▸ isCyclicArc_singleton _ x)

/-! ## 2. 四点的环形相邻（核心组合引理） -/

/-- `y` **严格夹在** `x` 与 `z` 之间（`Fin n` 的线性序 = 固定一个割点后的圆周序）。 -/
def Betw {n : ℕ} (x y z : Fin n) : Prop := (x < y ∧ y < z) ∨ (z < y ∧ y < x)

/-- **`{u,v}` 在四点 `{u,v,x,y}` 中环形相邻**：另两点 `x,y` 同在或同不在 `u,v` 之间。

圆上四点：`{u,v}` 相邻 ⟺ 另两点不恰有一个落在 `u,v` 之间。 -/
def CycAdj {n : ℕ} (x u v y : Fin n) : Prop :=
  (Betw u x v ∧ Betw u y v) ∨ (¬ Betw u x v ∧ ¬ Betw u y v)

/-- ★ **核心组合引理**：过同一点 `A` 的**三对**不可能在四点中**都**环形相邻。

（四个位置互异；在圆上，一个点只有两个邻居。全部情形由 `omega` 收束。） -/
theorem not_three_cycAdj {n : ℕ} (A B C E : Fin n)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAE : A ≠ E) (hBC : B ≠ C) (hBE : B ≠ E) (hCE : C ≠ E) :
    ¬ (CycAdj C A B E ∧ CycAdj B A C E ∧ CycAdj B A E C) := by
  rintro ⟨h1, h2, h3⟩
  simp only [CycAdj, Betw] at h1 h2 h3
  omega

/-- ★★ **传递引理**：环形弧 `A` 把 `a,b` 与 `c,e` 分开 ⟹ `{a,b}` 在四点上环形相邻。

证明：`A` 是 `cycArc f i j` 时 `f a, f b ∈ [i,j]` 而 `f c, f e ∉ [i,j]`，
夹在中间者必仍在 `[i,j]` 内 —— 矛盾；`A` 是其余集时对偶。（两个分支都由 `omega` 收束。） -/
theorem cycAdj_of_arc {n : ℕ} (f : α ≃ Fin n) {A : Finset α} (hA : IsCyclicArc f A)
    {a b c e : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A) (he : e ∉ A) :
    CycAdj (f c) (f a) (f b) (f e) := by
  rcases hA with ⟨i, j, hij, h | h⟩
  · rw [h] at ha hb hc he
    simp only [mem_cycArc, Finset.mem_Icc] at ha hb hc he
    simp only [CycAdj, Betw]
    omega
  · rw [h] at ha hb hc he
    simp only [Finset.mem_compl, mem_cycArc, Finset.mem_Icc] at ha hb hc he
    simp only [CycAdj, Betw]
    omega

/-! ## 3. ★★★ 环形 ⟹ 弱相容（文献 321–329 行的核心推论） -/

/-- 不在 `sideA` 的证明给出不在 `sideB` 的证明（两侧不交）。 -/
theorem notMem_sideB_of_mem_sideA (s : Split α) {x : α} (h : x ∈ s.sideA) : x ∉ s.sideB :=
  fun h' => (Finset.disjoint_left.mp s.disjoint_sides) h h'

/-- 不在 `sideB` 的证明给出不在 `sideA` 的证明（两侧不交）。 -/
theorem notMem_sideA_of_mem_sideB (s : Split α) {x : α} (h : x ∈ s.sideB) : x ∉ s.sideA :=
  fun h' => (Finset.disjoint_left.mp s.disjoint_sides) h' h

/-- 由「成员的一侧是环形弧」与「`s` 在四点上的 2|2 诱导」抽出**一个把两侧分开的环形弧**。

（`Separates` 的两个方向都只需取相应的那一侧；见 §1 的余集封闭。） -/
theorem exists_arc {n : ℕ} {f : α ≃ Fin n} {s : Split α}
    (h : IsCyclicArc f s.sideA ∨ IsCyclicArc f s.sideB)
    {a b c e : α} (hsep : s.Separates a b c e) :
    ∃ A : Finset α, IsCyclicArc f A ∧ a ∈ A ∧ b ∈ A ∧ c ∉ A ∧ e ∉ A := by
  rcases hsep with ⟨ha, hb, hc, he⟩ | ⟨ha, hb, hc, he⟩
  · rcases h with h | h
    · exact ⟨s.sideA, h, ha, hb, notMem_sideA_of_mem_sideB s hc,
        notMem_sideA_of_mem_sideB s he⟩
    · refine ⟨s.sideA, ?_, ha, hb, notMem_sideA_of_mem_sideB s hc,
        notMem_sideA_of_mem_sideB s he⟩
      rw [sideB_eq_compl] at h
      simpa using isCyclicArc_compl h
  · rcases h with h | h
    · refine ⟨s.sideB, ?_, ha, hb, notMem_sideB_of_mem_sideA s hc,
        notMem_sideB_of_mem_sideA s he⟩
      rw [sideB_eq_compl]
      exact isCyclicArc_compl h
    · exact ⟨s.sideB, h, ha, hb, notMem_sideB_of_mem_sideA s hc,
        notMem_sideB_of_mem_sideA s he⟩

/-- 两侧不交：同一元素不可能同时在 `sideA` 与 `sideB`。 -/
theorem not_mem_both_sides (s : Split α) {x : α} : ¬ (x ∈ s.sideA ∧ x ∈ s.sideB) :=
  fun h => (Finset.disjoint_left.mp s.disjoint_sides) h.1 h.2
/-- **冲突四点必互异**：`Split.Separates` 的三条假设在任两点重合时立即与「两侧不交」矛盾。 -/
theorem ne_of_separates {s t u : Split α} {a b c e : α}
    (hs : s.Separates a b c e) (ht : t.Separates a c b e) (hu : u.Separates a e b c) :
    a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    rcases ht with ⟨h1, -, h3, -⟩ | ⟨h3, -, h1, -⟩
    · exact not_mem_both_sides t ⟨h1, h3⟩
    · exact not_mem_both_sides t ⟨h1, h3⟩
  · rintro rfl
    rcases hu with ⟨h1, -, -, h4⟩ | ⟨h4, -, -, h1⟩
    · exact not_mem_both_sides u ⟨h1, h4⟩
    · exact not_mem_both_sides u ⟨h1, h4⟩
  · rintro rfl
    rcases ht with ⟨h1, -, -, h4⟩ | ⟨h4, -, -, h1⟩
    · exact not_mem_both_sides t ⟨h1, h4⟩
    · exact not_mem_both_sides t ⟨h1, h4⟩
  · rintro rfl
    rcases hs with ⟨-, h2, h3, -⟩ | ⟨-, h3, h2, -⟩
    · exact not_mem_both_sides s ⟨h2, h3⟩
    · exact not_mem_both_sides s ⟨h2, h3⟩
  · rintro rfl
    rcases hs with ⟨-, h2, -, h4⟩ | ⟨-, h4, -, h2⟩
    · exact not_mem_both_sides s ⟨h2, h4⟩
    · exact not_mem_both_sides s ⟨h2, h4⟩
  · rintro rfl
    rcases ht with ⟨-, h2, -, h4⟩ | ⟨-, h4, -, h2⟩
    · exact not_mem_both_sides t ⟨h2, h4⟩
    · exact not_mem_both_sides t ⟨h2, h4⟩

/-- ★★★ **主定理：环形 split 系统弱相容**（文献 321–329 行；「circular … generalization of
compatible」的严格内容 —— 相容族两两相容（`Split.pairwiseCompatible`），环形族只保证**弱**相容）。

证明：设 `s,t,u ∈ F` 在四点 `a,b,c,e` 上分别诱导 `ab|ce`、`ac|be`、`ae|bc`
（即 `HasConflictingQuartet`）。由 `Circular` 取环形序 `f`，每个成员抽出一个环形弧
（`exists_arc`），得三个把 `{a,b}`、`{a,c}`、`{a,e}` 与另两点分开的弧；
`cycAdj_of_arc` 给出三对「环形相邻」，与 `not_three_cycAdj`（四点互异由 `ne_of_separates`）
矛盾。 -/
theorem weaklyCompatible_of_circular (F : Set (Split α)) (h : Circular F) :
    WeaklyCompatible F := by
  obtain ⟨n, f, hf⟩ := h
  rintro ⟨a, b, c, e, ⟨s, hs, hsa⟩, ⟨t, ht, hta⟩, ⟨u, hu, hua⟩⟩
  obtain ⟨hab, hac, hae, hbc, hbe, hce⟩ := ne_of_separates hsa hta hua
  obtain ⟨A₁, hA₁, ha₁, hb₁, hc₁, he₁⟩ := exists_arc (hf s hs) hsa
  obtain ⟨A₂, hA₂, ha₂, hc₂, hb₂, he₂⟩ := exists_arc (hf t ht) hta
  obtain ⟨A₃, hA₃, ha₃, he₃, hb₃, hc₃⟩ := exists_arc (hf u hu) hua
  refine not_three_cycAdj (f a) (f b) (f c) (f e)
    (fun hh => hab (f.injective hh)) (fun hh => hac (f.injective hh))
    (fun hh => hae (f.injective hh)) (fun hh => hbc (f.injective hh))
    (fun hh => hbe (f.injective hh)) (fun hh => hce (f.injective hh)) ?_
  exact ⟨cycAdj_of_arc f hA₁ ha₁ hb₁ hc₁ he₁,
    cycAdj_of_arc f hA₂ ha₂ hc₂ hb₂ he₂,
    cycAdj_of_arc f hA₃ ha₃ he₃ hb₃ hc₃⟩

/-! ## 4. ★B / ★C：`Fin 4` 上的最小例子 -/

/-- `Fin 4` 的**环形位置**：`x₀,x₁,x₂,x₃ = 1,0,2,3`（`Equiv.swap 0 1`）。

圆上顺序 `0,2,3,1`：使 `{0,1}` 与 `{0,2}` 同时是弧（`{0,1} = [0,1]`、`{0,2} = [1,2]`）。 -/
def quadPos : Fin 4 ≃ Fin 4 := Equiv.swap 0 1

/-- `fourA = {0,1}|{2,3}` 在 `quadPos` 下是弧（`[0,1]`）。 -/
theorem isCyclicArc_quadA : IsCyclicArc quadPos (fourA : Split (Fin 4)).sideA := by
  refine ⟨0, 1, by decide, Or.inl ?_⟩
  ext x
  fin_cases x <;> decide

/-- `fourB = {0,2}|{1,3}` 在 `quadPos` 下是弧（`[1,2]`）。 -/
theorem isCyclicArc_quadB : IsCyclicArc quadPos (fourB : Split (Fin 4)).sideA := by
  refine ⟨1, 2, by decide, Or.inl ?_⟩
  ext x
  fin_cases x <;> decide

/-- ★C **最小例子（4 taxon）**：`{fourA, fourB}` 是**环形**族（位置 `quadPos`）。 -/
theorem circular_pair_fourAB : Circular ({fourA, fourB} : Set (Split (Fin 4))) := by
  refine ⟨4, quadPos, fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · exact Or.inl isCyclicArc_quadA
  · exact Or.inl isCyclicArc_quadB

/-- `fourA` 与 `fourB` **不**相容（四个交全非空；`Phylo/SplitWeak.lean` 的分离判据）。 -/
theorem not_compatible_fourAB : ¬ (fourA : Split (Fin 4)).Compatible fourB := by
  have h1 : (fourA : Split (Fin 4)).Separates 0 1 2 3 := by simp [Separates, fourA]
  have h2 : (fourB : Split (Fin 4)).Separates 0 2 1 3 := by simp [Separates, fourB]
  exact fun h => not_compatible_of_separates h1 h2 h

/-- ★B **反例检查（环形 ⇏ 两两相容）**：`Fin 4` 上存在**环形却不两两相容**的族。

⇒ 环形类是相容类的**严格**推广（文献 321–323 行 "a mathematical generalization of
compatible collections of splits"）；这也说明主定理**不能**强化为「环形 ⟹ 两两相容」。 -/
theorem exists_circular_not_pairwiseCompatible :
    ∃ F : Set (Split (Fin 4)),
      Circular F ∧ ¬ (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) :=
  ⟨{fourA, fourB}, circular_pair_fourAB,
    fun h => not_compatible_fourAB (h fourA (by simp) fourB (by simp))⟩

/-- ★B **反面（最小非环形构形）**：`Fin 4` 上**三个** 2|2 split 全体**不是**环形。

由主定理（环形 ⟹ 弱相容）与 `Split.not_weaklyCompatible_four`（三点冲突 ⟹ 非弱相容）立得。
这正对应文献 Fig. 5/Fig. 6 中「三个两两不相容的 split 生成非平面立方体」的情形。 -/
theorem not_circular_four_quartets :
    ¬ Circular ({fourA, fourB, fourC} : Set (Split (Fin 4))) :=
  fun h => not_weaklyCompatible_four (weaklyCompatible_of_circular _ h)

/-- ★C **4 taxon 端到端**：环形族**不可能**同时含三个 2|2 split（quintet 判据的 n = 4 特例）。

即：`Fin 4` 上三个 quartet split 中至多两个能出现在同一个环形族里
（`{fourA, fourB}` 已在上面的 ★B 中实现，故界是**紧**的）。 -/
theorem circular_not_all_three_quartets (F : Set (Split (Fin 4)))
    (hsub : F ⊆ ({fourA, fourB, fourC} : Set (Split (Fin 4)))) (h : Circular F) :
    ¬ (fourA ∈ F ∧ fourB ∈ F ∧ fourC ∈ F) := by
  rintro ⟨h1, h2, h3⟩
  have heq : F = ({fourA, fourB, fourC} : Set (Split (Fin 4))) := by
    refine Set.Subset.antisymm hsub ?_
    intro s hs
    rcases hs with rfl | rfl | rfl <;> assumption
  exact not_circular_four_quartets (heq ▸ h)

/-- ★C 另一侧（相容族）：`{0}|{1,2,3}` 与 `{0,1}|{2,3}` 在**恒等**环形序下都是弧。

（文献 321–323 行：相容族是环形族的特例。） -/
theorem circular_tree_four :
    Circular ({ofSideA ({0} : Finset (Fin 4)) (by decide) (by decide), fourA} :
      Set (Split (Fin 4))) := by
  refine ⟨4, Equiv.refl (Fin 4), fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · refine Or.inl ⟨0, 0, le_rfl, Or.inl ?_⟩
    ext x
    fin_cases x <;> decide
  · refine Or.inl ⟨0, 1, by decide, Or.inl ?_⟩
    ext x
    fin_cases x <;> decide

/-! ## 5. 非空真（防空真） -/

/-- ★ **非空真**：`Fin 4` 上真的存在环形族（非空集合）。 -/
theorem circular_nonempty : ∃ F : Set (Split (Fin 4)), F.Nonempty ∧ Circular F :=
  ⟨{fourA, fourB}, ⟨fourA, by simp⟩, circular_pair_fourAB⟩

/-- ★ **非空真**：环形族可以真的含**不相容**的成员（`fourA`、`fourB`）。 -/
theorem circular_has_incompatible_pair :
    ∃ F : Set (Split (Fin 4)), Circular F ∧ ∃ s ∈ F, ∃ t ∈ F, ¬ s.Compatible t :=
  ⟨{fourA, fourB}, circular_pair_fourAB, fourA, by simp, fourB, by simp, not_compatible_fourAB⟩

/-- ★ `IsCyclicArc` 非空真：`cycArc` 本身是弧，且 `Fin 4` 上 `{0,1,2}` 也是弧。 -/
theorem quad_arc_three : IsCyclicArc (Equiv.refl (Fin 4)) ({0, 1, 2} : Finset (Fin 4)) := by
  refine ⟨0, 2, by decide, Or.inl ?_⟩
  ext x
  fin_cases x <;> decide

/-! ## 6. 缺口（显式 `Prop`；未证） -/

/-- **系统发生距离**（文献 ~260–270 行）：加权 split 族下两 taxon 的距离 =
把它们分开的 split 的权重之和。 -/
def phyleticDist (F : Finset (Split α)) (w : Split α → ℝ) (x y : α) : ℝ :=
  ∑ s ∈ F, w s * (if (x ∈ s.sideA ∧ y ∈ s.sideB) ∨ (x ∈ s.sideB ∧ y ∈ s.sideA) then 1 else 0)

/-- **环形（Kalmanson）距离矩阵**（文献 1058–1062 行）：存在环形序 `f`，使下标序下
`i ≤ j ≤ k ≤ l` 的四个点满足两条 Kalmanson 不等式（「不交叉」配对之和 ≤ 「交叉」配对之和）。 -/
def IsCircularDist {n : ℕ} (f : α ≃ Fin n) (d : α → α → ℝ) : Prop :=
  ∀ i j k l : Fin n, i ≤ j → j ≤ k → k ≤ l →
    d (f.symm i) (f.symm j) + d (f.symm k) (f.symm l) ≤
        d (f.symm i) (f.symm k) + d (f.symm j) (f.symm l) ∧
      d (f.symm i) (f.symm l) + d (f.symm j) (f.symm k) ≤
        d (f.symm i) (f.symm k) + d (f.symm j) (f.symm l)

/-- ⬜ **缺口 1（环形距离的实现 + `A` 满秩，文献 805–812、1058–1078 行）**：
每个环形（Kalmanson）距离矩阵都是某个**非负**加权环形 split 族的系统发生距离。

未落原因：这需要 Bandelt–Dress (1992) 的孤立指数/分裂分解理论（本库 `Phylo/SplitWeak.lean`
只做到「d-split 全体弱相容」），以及「环形 ⟹ `A` 列满秩（`b ↦ Ab` 单射）」
——后者又需要本文件的 `IsCyclicArc` 与「每个 split 的分裂指标独立性」。
**这是本库离「Neighbor-Net 一致性」最近的一块未铺路段。** -/
def circularDistanceRealization_gap : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X] (d : X → X → ℝ),
    (∃ n : ℕ, ∃ f : X ≃ Fin n, IsCircularDist f d) →
      ∃ (F : Finset (Split X)) (w : Split X → ℝ),
        Circular (↑F : Set (Split X)) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
          ∀ x y : X, x ≠ y → phyleticDist F w x y = d x y

/-- ⬜ **缺口 2（选择式 `b ↦ Ab` 单射，文献 805–806 行）**：
环形族的指示矩阵 `A` **列满秩**，即权重向量 `b` 由系统发生距离唯一确定。

（要求族内无重复——`Split.swap` 给出的两侧互换算同一 split，故需显式排除。） -/
def circularIndicatorFullRank_gap : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X] {ι : Type*} [Fintype ι] (S : ι → Split X),
    Function.Injective S →
      (∀ i j : ι, S i = (S j).swap → i = j) →
        (∃ n : ℕ, ∃ f : X ≃ Fin n,
          ∀ i : ι, IsCyclicArc f (S i).sideA ∨ IsCyclicArc f (S i).sideB) →
          Function.Injective (fun b : ι → ℝ => fun p : X × X =>
            ∑ i, b i * (if (p.1 ∈ (S i).sideA ∧ p.2 ∈ (S i).sideB) ∨
              (p.1 ∈ (S i).sideB ∧ p.2 ∈ (S i).sideA) then 1 else 0))

/-- ⬜ **缺口 3（算法主体，文献 288–328、469–565 行）**：Neighbor-Net 的
agglomeration 迭代（聚类对 `Cᵢ`、选择式 (1)(2)(3) 的 `Q` 极小化、约化式 (4)(5) 的
「三节点 → 两节点」、反演展开出 split）**本库完全未形式化**。

此 `Prop` 记录形式化目标：**对任意对称相异度，存在一个由 (2)(3) 极小化与 (4)(5) 约化
驱动的归并运行，其反演展开产出环形 split 族**（文献 321–324 行称「可用数学归纳法证明」）。
「存在」不能加强为库内可证的命题，因为 `Step`（归并关系）本身缺失。 -/
def neighborNetAgglomeration_gap : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X],
    1 < Fintype.card X →
      ∃ Step : (X → X → ℝ) → Finset (Split X) → Prop,
        (∀ (d : X → X → ℝ) (F : Finset (Split X)), Step d F →
          Circular (↑F : Set (Split X)) ∧ ∀ x : X, ∃ s ∈ F, s.sideA = {x} ∨ s.sideB = {x}) ∧
          ∀ (d : X → X → ℝ), (∀ x y, d x y = d y x) → ∃ F, Step d F

end NeighborNet
