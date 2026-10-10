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

/-! ## 7. 缺口 2 **已证**（W12g）：环形族指示矩阵列满秩

文献 805–812 行：「Neighbor-Net produces a circular collection of splits, so the corresponding
matrix `A` has full rank (Bandelt and Dress 1992)」。本节给出该满秩性的**显式逆矩阵**：
对每个环形 arc `[i,j]`，用一个四（或三）点组合从系统发生距离里**直接解出**该 split 的权重
（`quad_sepInd_d` / `quad_sepInd_h` / `tri_sepInd_l`）。于是 `circularIndicatorFullRank_gap`
不再是缺口（`circularIndicatorFullRank_gap_proved`）。

数值核对（穷举 `n = 4,5,6` 的全部环形弧族与子族；含「不排除两侧互换则命题为假」的对照组）：
`scripts/msc/w12g_circular_indicator_rank.py`。 -/

section IndicatorFullRank

/-! ### 7.1 位组合核（纯算术，与 `Split` 无关） -/

/-- 区间 `[i',j']` 在位置 `t` 上的 `0/1` 指示（`ℝ` 值）。 -/
def bitN (i' j' t : ℕ) : ℝ := if i' ≤ t ∧ t ≤ j' then 1 else 0

theorem bitN_eq_one_iff (i' j' t : ℕ) : bitN i' j' t = 1 ↔ i' ≤ t ∧ t ≤ j' := by
  unfold bitN
  by_cases h : i' ≤ t ∧ t ≤ j' <;> simp [h]

theorem bitN_eq_zero_iff (i' j' t : ℕ) : bitN i' j' t = 0 ↔ ¬(i' ≤ t ∧ t ≤ j') := by
  unfold bitN
  by_cases h : i' ≤ t ∧ t ≤ j' <;> simp [h]

theorem bitN_zero_or_one (i' j' t : ℕ) : bitN i' j' t = 0 ∨ bitN i' j' t = 1 := by
  unfold bitN; split <;> simp

/-- ★ **代数核**：四个 `0/1` 位的四点组合 `= 2·(bu−bw)·(bz−bv)`。 -/
theorem quad_bit_eq (bu bw bv bz : ℝ) (hu : bu = 0 ∨ bu = 1) (hw : bw = 0 ∨ bw = 1)
    (hv : bv = 0 ∨ bv = 1) (hz : bz = 0 ∨ bz = 1) :
    |bu - bv| - |bw - bv| - |bu - bz| + |bw - bz| = 2 * ((bu - bw) * (bz - bv)) := by
  have h01 : ∀ x y : ℝ, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → |x - y| = x + y - 2 * x * y := by
    rintro x y (rfl | rfl) <;> rintro (rfl | rfl) <;> norm_num
  rw [h01 bu bv hu hv, h01 bw bv hw hv, h01 bu bz hu hz, h01 bw bz hw hz]
  ring

/-- ★ **D-核**（线性四点；`t2 = t1+1`、`t4 = t3+1`、`t2 ≤ t3`）：
四点位组合恰在区间 `= [t2,t3]` 时等于 `2`。

⚠️ 不需要 `i' ≤ j'`：区间为空时组合恒为 `0`，与结论一致。 -/
theorem dcore (i' j' t1 t2 t3 t4 : ℕ) (h12 : t2 = t1 + 1) (h23 : t2 ≤ t3)
    (h34 : t4 = t3 + 1) :
    |bitN i' j' t1 - bitN i' j' t3| - |bitN i' j' t2 - bitN i' j' t3|
      - |bitN i' j' t1 - bitN i' j' t4| + |bitN i' j' t2 - bitN i' j' t4|
      = if (i' = t2 ∧ j' = t3) then 2 else 0 := by
  have hprod : (bitN i' j' t1 - bitN i' j' t2) * (bitN i' j' t4 - bitN i' j' t3)
      = if (i' = t2 ∧ j' = t3) then 1 else 0 := by
    by_cases hP : i' = t2 ∧ j' = t3
    · rw [ite_eq_left hP]
      obtain ⟨e1, e2⟩ := hP
      have b1 : bitN i' j' t1 = 0 := by rw [bitN_eq_zero_iff]; omega
      have b2 : bitN i' j' t2 = 1 := by rw [bitN_eq_one_iff]; omega
      have b3 : bitN i' j' t3 = 1 := by rw [bitN_eq_one_iff]; omega
      have b4 : bitN i' j' t4 = 0 := by rw [bitN_eq_zero_iff]; omega
      rw [b1, b2, b3, b4]; norm_num
    · rw [ite_eq_right hP]
      rcases bitN_zero_or_one i' j' t1 with b1 | b1 <;> rcases bitN_zero_or_one i' j' t2 with b2 | b2
      · rw [b1, b2]; ring
      · have hi : i' = t2 := by
          rw [bitN_eq_zero_iff] at b1; rw [bitN_eq_one_iff] at b2; omega
        have h43 : bitN i' j' t4 = bitN i' j' t3 := by
          by_cases hle : t3 ≤ j'
          · have e3 : bitN i' j' t3 = 1 := by rw [bitN_eq_one_iff]; omega
            have e4 : bitN i' j' t4 = 1 := by rw [bitN_eq_one_iff]; omega
            rw [e3, e4]
          · have e3 : bitN i' j' t3 = 0 := by rw [bitN_eq_zero_iff]; omega
            have e4 : bitN i' j' t4 = 0 := by rw [bitN_eq_zero_iff]; omega
            rw [e3, e4]
        rw [h43]; ring
      · have hj : j' < t2 := by
          rw [bitN_eq_one_iff] at b1; rw [bitN_eq_zero_iff] at b2; omega
        have e3 : bitN i' j' t3 = 0 := by rw [bitN_eq_zero_iff]; omega
        have e4 : bitN i' j' t4 = 0 := by rw [bitN_eq_zero_iff]; omega
        rw [e3, e4]; ring
      · rw [b1, b2]; ring
  rw [quad_bit_eq (bitN i' j' t1) (bitN i' j' t2) (bitN i' j' t3) (bitN i' j' t4)
    (bitN_zero_or_one ..) (bitN_zero_or_one ..) (bitN_zero_or_one ..) (bitN_zero_or_one ..)]
  rw [hprod]
  split <;> ring

/-- ★ **H-核**（环形四点 `(nn−1, 0, j, j+1)`）：四点位组合恰在区间是前缀 `[0,j]`
或其补 `[j+1,nn−1]` 时等于 `2`。 -/
theorem hcore (i' j' nn j : ℕ) (hij : i' ≤ j') (hj1 : 1 ≤ j) (hjn : j + 1 < nn)
    (hj'n : j' < nn) :
    |bitN i' j' (nn - 1) - bitN i' j' j| - |bitN i' j' 0 - bitN i' j' j|
      - |bitN i' j' (nn - 1) - bitN i' j' (j + 1)| + |bitN i' j' 0 - bitN i' j' (j + 1)|
      = if ((i' = 0 ∧ j' = j) ∨ (i' = j + 1 ∧ j' = nn - 1)) then 2 else 0 := by
  have hprod : (bitN i' j' (nn - 1) - bitN i' j' 0) * (bitN i' j' (j + 1) - bitN i' j' j)
      = if ((i' = 0 ∧ j' = j) ∨ (i' = j + 1 ∧ j' = nn - 1)) then 1 else 0 := by
    by_cases hP : (i' = 0 ∧ j' = j) ∨ (i' = j + 1 ∧ j' = nn - 1)
    · rw [ite_eq_left hP]
      rcases hP with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have b0 : bitN i' j' 0 = 1 := by rw [bitN_eq_one_iff]; omega
        have bj : bitN i' j' j = 1 := by rw [bitN_eq_one_iff]; omega
        have bj1 : bitN i' j' (j + 1) = 0 := by rw [bitN_eq_zero_iff]; omega
        have bn : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
        rw [bn, b0, bj1, bj]; norm_num
      · have b0 : bitN i' j' 0 = 0 := by rw [bitN_eq_zero_iff]; omega
        have bj : bitN i' j' j = 0 := by rw [bitN_eq_zero_iff]; omega
        have bj1 : bitN i' j' (j + 1) = 1 := by rw [bitN_eq_one_iff]; omega
        have bn : bitN i' j' (nn - 1) = 1 := by rw [bitN_eq_one_iff]; omega
        rw [bn, b0, bj1, bj]; norm_num
    · rw [ite_eq_right hP]
      suffices h : (bitN i' j' (nn - 1) - bitN i' j' 0) * (bitN i' j' (j + 1) - bitN i' j' j) = 0
        by rw [h]
      rcases bitN_zero_or_one i' j' j with bj | bj <;>
        rcases bitN_zero_or_one i' j' (j + 1) with bj1 | bj1
      · rw [bj, bj1]; ring
      · have hi : i' = j + 1 := by
          rw [bitN_eq_zero_iff] at bj; rw [bitN_eq_one_iff] at bj1; omega
        have hj' : j' ≠ nn - 1 := fun h => hP (Or.inr ⟨hi, h⟩)
        have b0 : bitN i' j' 0 = 0 := by rw [bitN_eq_zero_iff]; omega
        have bn : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
        rw [b0, bn]; ring
      · have hj' : j' = j := by
          rw [bitN_eq_one_iff] at bj; rw [bitN_eq_zero_iff] at bj1; omega
        have h0 : i' ≠ 0 := fun h => hP (Or.inl ⟨h, hj'⟩)
        have b0 : bitN i' j' 0 = 0 := by rw [bitN_eq_zero_iff]; omega
        have bn : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
        rw [b0, bn]; ring
      · rw [bj, bj1]; ring
  rw [quad_bit_eq (bitN i' j' (nn - 1)) (bitN i' j' 0) (bitN i' j' j) (bitN i' j' (j + 1))
    (bitN_zero_or_one ..) (bitN_zero_or_one ..) (bitN_zero_or_one ..) (bitN_zero_or_one ..)]
  rw [hprod]
  split <;> ring

/-- ★ **L-核**（三点 `(0, 1, nn−1)`，`nn ≥ 3`）：三点位组合恰在区间是 `{p₀}`（`[0,0]`）
或其补 `[1,nn−1]` 时等于 `2`。 -/
theorem lcore (i' j' nn : ℕ) (hij : i' ≤ j') (hj'n : j' < nn) (hnn : 3 ≤ nn) :
    |bitN i' j' 0 - bitN i' j' 1| + |bitN i' j' 0 - bitN i' j' (nn - 1)|
      - |bitN i' j' 1 - bitN i' j' (nn - 1)|
      = if ((i' = 0 ∧ j' = 0) ∨ (i' = 1 ∧ j' = nn - 1)) then 2 else 0 := by
  by_cases hP : (i' = 0 ∧ j' = 0) ∨ (i' = 1 ∧ j' = nn - 1)
  · rw [ite_eq_left hP]
    rcases hP with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have b0 : bitN i' j' 0 = 1 := by rw [bitN_eq_one_iff]; omega
      have b1 : bitN i' j' 1 = 0 := by rw [bitN_eq_zero_iff]; omega
      have bl : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
      rw [b0, b1, bl]; norm_num
    · have b0 : bitN i' j' 0 = 0 := by rw [bitN_eq_zero_iff]; omega
      have b1 : bitN i' j' 1 = 1 := by rw [bitN_eq_one_iff]; omega
      have bl : bitN i' j' (nn - 1) = 1 := by rw [bitN_eq_one_iff]; omega
      rw [b0, b1, bl]; norm_num
  · rw [ite_eq_right hP]
    rcases Nat.eq_zero_or_pos i' with hi0 | hi0
    · have b0 : bitN i' j' 0 = 1 := by rw [bitN_eq_one_iff]; omega
      have b1 : bitN i' j' 1 = 1 := by rw [bitN_eq_one_iff]; omega
      rw [b0, b1, sub_self, abs_zero]; ring
    · have b0 : bitN i' j' 0 = 0 := by rw [bitN_eq_zero_iff]; omega
      by_cases hi1 : i' = 1
      · have hj' : j' < nn - 1 := by
          by_contra h
          exact hP (Or.inr ⟨hi1, by omega⟩)
        have b1 : bitN i' j' 1 = 1 := by rw [bitN_eq_one_iff]; omega
        have bl : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
        rw [b0, b1, bl]; norm_num
      · have b1 : bitN i' j' 1 = 0 := by rw [bitN_eq_zero_iff]; omega
        by_cases hj' : j' = nn - 1
        · have bl : bitN i' j' (nn - 1) = 1 := by rw [bitN_eq_one_iff]; omega
          rw [b0, b1, bl]; norm_num
        · have bl : bitN i' j' (nn - 1) = 0 := by rw [bitN_eq_zero_iff]; omega
          rw [b0, b1, bl]; norm_num

end IndicatorFullRank

/-! ## 7.2 从位组合到 split 族：显式逆矩阵与主定理 -/

section IndicatorApplication

variable {X : Type*} [Fintype X] [DecidableEq X] {ι : Type*} [Fintype ι]

/-- **分离指示**（`0/1`，`ℝ` 值）：`s` 是否把 `u, v` 分在两侧。

（与 `circularIndicatorFullRank_gap` 里的 `if` 逐字相同，只是起了名字。） -/
def sepInd (s : Split X) (u v : X) : ℝ :=
  if (u ∈ s.sideA ∧ v ∈ s.sideB) ∨ (u ∈ s.sideB ∧ v ∈ s.sideA) then 1 else 0

/-- 单点 `0/1` 指示。 -/
def arcBit (A : Finset X) (u : X) : ℝ := if u ∈ A then 1 else 0

/-- 四点泛函 `φ u v − φ w v − φ u z + φ w z`。 -/
def quad (φ : X → X → ℝ) (u w v z : X) : ℝ := φ u v - φ w v - φ u z + φ w z

/-- 三点泛函 `φ u v + φ u w − φ v w`。 -/
def tri (φ : X → X → ℝ) (u v w : X) : ℝ := φ u v + φ u w - φ v w

omit [DecidableEq X] in
/-- `f.symm a` 落在环形弧 `[i,j]` 中 ⟺ 其下标落在区间内。 -/
theorem symm_mem_cycArc {n : ℕ} (f : X ≃ Fin n) (i j a : Fin n) :
    f.symm a ∈ cycArc f i j ↔ i.val ≤ a.val ∧ a.val ≤ j.val := by
  rw [mem_cycArc, Equiv.apply_symm_apply, Finset.mem_Icc]
  constructor <;> intro h <;> exact ⟨by omega, by omega⟩

theorem arcBit_cycArc_eq_bitN {n : ℕ} (f : X ≃ Fin n) (i j a : Fin n) :
    arcBit (cycArc f i j) (f.symm a) = bitN i.val j.val a.val := by
  unfold arcBit bitN
  by_cases h : f.symm a ∈ cycArc f i j
  · rw [ite_eq_left h, ite_eq_left ((symm_mem_cycArc f i j a).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h ((symm_mem_cycArc f i j a).mpr hh))]

/-- 若 `s` 的一侧是 `J` 或 `Jᶜ`，则分离指示是 `J` 的位差的绝对值。 -/
theorem sepInd_eq_abs_arcBit {s : Split X} {J : Finset X}
    (h : s.sideA = J ∨ s.sideA = Jᶜ) (u v : X) :
    sepInd s u v = |arcBit J u - arcBit J v| := by
  have hB : (s.sideA = J → s.sideB = Jᶜ) ∧ (s.sideA = Jᶜ → s.sideB = J) :=
    ⟨fun hh => by rw [sideB_eq_compl, hh], fun hh => by rw [sideB_eq_compl, hh, compl_compl]⟩
  rcases h with h | h
  · rw [sepInd, h, hB.1 h]
    unfold arcBit
    by_cases hu : u ∈ J <;> by_cases hv : v ∈ J <;> simp [hu, hv, Finset.mem_compl]
  · rw [sepInd, h, hB.2 h]
    unfold arcBit
    by_cases hu : u ∈ J <;> by_cases hv : v ∈ J <;> simp [hu, hv, Finset.mem_compl]

/-- ★ **D 情形**：`quad` 在四点 `(a, b, c, d)`（`b = a+1`、`c = d−1` 处的 `c`、`d = c+1`）
上恰在区间 `= [b, c]` 时等于 `2`。 -/
theorem quad_sepInd_d {n : ℕ} (f : X ≃ Fin n) {s : Split X} {i' j' : Fin n}
    (hs : s.sideA = cycArc f i' j' ∨ s.sideA = (cycArc f i' j')ᶜ)
    (a b c d : Fin n) (h1 : b.val = a.val + 1) (h2 : b.val ≤ c.val) (h3 : d.val = c.val + 1) :
    quad (sepInd s) (f.symm a) (f.symm b) (f.symm c) (f.symm d)
      = 2 * (if (i'.val = b.val ∧ j'.val = c.val) then (1 : ℝ) else 0) := by
  have hq : quad (sepInd s) (f.symm a) (f.symm b) (f.symm c) (f.symm d)
      = |bitN i'.val j'.val a.val - bitN i'.val j'.val c.val|
        - |bitN i'.val j'.val b.val - bitN i'.val j'.val c.val|
        - |bitN i'.val j'.val a.val - bitN i'.val j'.val d.val|
        + |bitN i'.val j'.val b.val - bitN i'.val j'.val d.val| := by
    unfold quad
    rw [sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs,
      sepInd_eq_abs_arcBit hs, arcBit_cycArc_eq_bitN f i' j' a, arcBit_cycArc_eq_bitN f i' j' b,
      arcBit_cycArc_eq_bitN f i' j' c, arcBit_cycArc_eq_bitN f i' j' d]
  rw [hq, dcore i'.val j'.val a.val b.val c.val d.val h1 h2 h3]
  split <;> ring

/-- ★ **H 情形（前缀/后缀）**：`quad` 在四点 `(last, 0, j, j+1)`（`nn` 个位置）上恰在
区间是前缀 `[0,j]` 或其补 `[j+1,nn−1]` 时等于 `2`。 -/
theorem quad_sepInd_h {n : ℕ} (f : X ≃ Fin n) {s : Split X} {i' j' : Fin n} (hij : i' ≤ j')
    (hs : s.sideA = cycArc f i' j' ∨ s.sideA = (cycArc f i' j')ᶜ)
    (q0 qj qj1 ql : Fin n) (h0 : q0.val = 0) (hj1 : 1 ≤ qj.val) (hjl : qj1.val = qj.val + 1)
    (hl : ql.val = n - 1) :
    quad (sepInd s) (f.symm ql) (f.symm q0) (f.symm qj) (f.symm qj1)
      = 2 * (if ((i'.val = 0 ∧ j'.val = qj.val) ∨ (i'.val = qj.val + 1 ∧ j'.val = n - 1))
        then (1 : ℝ) else 0) := by
  have hq : quad (sepInd s) (f.symm ql) (f.symm q0) (f.symm qj) (f.symm qj1)
      = |bitN i'.val j'.val (n - 1) - bitN i'.val j'.val qj.val|
        - |bitN i'.val j'.val 0 - bitN i'.val j'.val qj.val|
        - |bitN i'.val j'.val (n - 1) - bitN i'.val j'.val (qj.val + 1)|
        + |bitN i'.val j'.val 0 - bitN i'.val j'.val (qj.val + 1)| := by
    unfold quad
    rw [sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs,
      sepInd_eq_abs_arcBit hs, arcBit_cycArc_eq_bitN f i' j' ql, arcBit_cycArc_eq_bitN f i' j' q0,
      arcBit_cycArc_eq_bitN f i' j' qj, arcBit_cycArc_eq_bitN f i' j' qj1, hl, h0, hjl]
  rw [hq, hcore i'.val j'.val n qj.val hij (by omega) (by omega) (by omega)]
  split <;> ring

/-- ★ **L 情形（单元素前缀）**：`tri` 在三点 `(0, 1, last)`（`n ≥ 3`）上恰在区间是
`{p₀}`（`[0,0]`）或其补 `[1,n−1]` 时等于 `2`。 -/
theorem tri_sepInd_l {n : ℕ} (f : X ≃ Fin n) {s : Split X} {i' j' : Fin n} (hij : i' ≤ j')
    (hs : s.sideA = cycArc f i' j' ∨ s.sideA = (cycArc f i' j')ᶜ) (hn : 3 ≤ n)
    (q0 q1 ql : Fin n) (h0 : q0.val = 0) (h1 : q1.val = 1) (hl : ql.val = n - 1) :
    tri (sepInd s) (f.symm q0) (f.symm q1) (f.symm ql)
      = 2 * (if ((i'.val = 0 ∧ j'.val = 0) ∨ (i'.val = 1 ∧ j'.val = n - 1))
        then (1 : ℝ) else 0) := by
  have hq : tri (sepInd s) (f.symm q0) (f.symm q1) (f.symm ql)
      = |bitN i'.val j'.val 0 - bitN i'.val j'.val 1|
        + |bitN i'.val j'.val 0 - bitN i'.val j'.val (n - 1)|
        - |bitN i'.val j'.val 1 - bitN i'.val j'.val (n - 1)| := by
    unfold tri
    rw [sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs, sepInd_eq_abs_arcBit hs,
      arcBit_cycArc_eq_bitN f i' j' q0, arcBit_cycArc_eq_bitN f i' j' q1,
      arcBit_cycArc_eq_bitN f i' j' ql, h0, h1, hl]
  rw [hq, lcore i'.val j'.val n hij (by omega) hn]
  split <;> ring

omit [Fintype X] [DecidableEq X] in
/-- `quad` 对权重求和线性。 -/
theorem quad_sum (b : ι → ℝ) (g : ι → X → X → ℝ) (u w v z : X) :
    quad (fun p q => ∑ i, b i * g i p q) u w v z = ∑ i, b i * quad (g i) u w v z := by
  have h1 : quad (fun p q => ∑ i, b i * g i p q) u w v z
      = (∑ i, b i * g i u v) - (∑ i, b i * g i w v) - (∑ i, b i * g i u z)
        + (∑ i, b i * g i w z) := by
    simp only [quad]
  have h2 : (∑ i, b i * quad (g i) u w v z)
      = (∑ i, b i * g i u v) - (∑ i, b i * g i w v) - (∑ i, b i * g i u z)
        + (∑ i, b i * g i w z) := by
    rw [show (∑ i, b i * quad (g i) u w v z)
        = ∑ i, (b i * g i u v - b i * g i w v - b i * g i u z + b i * g i w z) from
      Finset.sum_congr rfl fun i _ => by simp only [quad]; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [h1, h2]

omit [Fintype X] [DecidableEq X] in
/-- `tri` 对权重求和线性。 -/
theorem tri_sum (b : ι → ℝ) (g : ι → X → X → ℝ) (u v w : X) :
    tri (fun p q => ∑ i, b i * g i p q) u v w = ∑ i, b i * tri (g i) u v w := by
  have h1 : tri (fun p q => ∑ i, b i * g i p q) u v w
      = (∑ i, b i * g i u v) + (∑ i, b i * g i u w) - (∑ i, b i * g i v w) := by
    simp only [tri]
  have h2 : (∑ i, b i * tri (g i) u v w)
      = (∑ i, b i * g i u v) + (∑ i, b i * g i u w) - (∑ i, b i * g i v w) := by
    rw [show (∑ i, b i * tri (g i) u v w)
        = ∑ i, (b i * g i u v + b i * g i u w - b i * g i v w) from
      Finset.sum_congr rfl fun i _ => by simp only [tri]; ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2]

/-- **相等 ⟺ 两侧都相等**（`Split` 只由 `sideA`/`sideB` 决定）。 -/
theorem eq_iff_sides (s t : Split X) : s = t ↔ s.sideA = t.sideA ∧ s.sideB = t.sideB := by
  constructor
  · intro h; exact ⟨by rw [h], by rw [h]⟩
  · rintro ⟨h1, h2⟩
    refine (KPartition.eq_iff_parts _ _).mpr (funext fun i => ?_)
    fin_cases i
    · exact h1
    · exact h2

/-- 两条 split 的同一侧都等于 `J` 或 `Jᶜ` ⇒ 相等或互为 `swap`。 -/
theorem eq_or_swap_of_sides {s t : Split X} {J : Finset X}
    (hs : s.sideA = J ∨ s.sideA = Jᶜ) (ht : t.sideA = J ∨ t.sideA = Jᶜ) :
    s = t ∨ s = t.swap := by
  have hsB : (s.sideA = J → s.sideB = Jᶜ) ∧ (s.sideA = Jᶜ → s.sideB = J) :=
    ⟨fun h => by rw [sideB_eq_compl, h], fun h => by rw [sideB_eq_compl, h, compl_compl]⟩
  have htB : (t.sideA = J → t.sideB = Jᶜ) ∧ (t.sideA = Jᶜ → t.sideB = J) :=
    ⟨fun h => by rw [sideB_eq_compl, h], fun h => by rw [sideB_eq_compl, h, compl_compl]⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · left; exact (eq_iff_sides s t).mpr ⟨by rw [hs, ht], by rw [hsB.1 hs, htB.1 ht]⟩
  · right
    exact (eq_iff_sides s t.swap).mpr
      ⟨by rw [swap_sideA, htB.2 ht, hs], by rw [swap_sideB, ht, hsB.1 hs]⟩
  · right
    exact (eq_iff_sides s t.swap).mpr
      ⟨by rw [swap_sideA, htB.1 ht, hs], by rw [swap_sideB, ht, hsB.2 hs]⟩
  · left; exact (eq_iff_sides s t).mpr ⟨by rw [hs, ht], by rw [hsB.2 hs, htB.2 ht]⟩

/-- **`card X ≤ 2` 时两侧都是单点**。 -/
theorem side_card_eq_one_of_card_le_two (hX : Fintype.card X ≤ 2) (s : Split X) :
    s.sideA.card = 1 ∧ s.sideB.card = 1 := by
  have h1 : s.sideA.card + s.sideB.card = Fintype.card X := by
    rw [← Finset.card_union_of_disjoint s.disjoint_sides, s.union_sides]
    simp
  have h2 : 1 ≤ s.sideA.card := Finset.card_pos.mpr (s.nonempty 0)
  have h3 : 1 ≤ s.sideB.card := Finset.card_pos.mpr (s.nonempty 1)
  omega

/-- **`card X ≤ 2` 时任意两条 split 相等或互为 `swap`**（只有一条 partition）。 -/
theorem eq_or_swap_of_card_le_two (hX : Fintype.card X ≤ 2) (s t : Split X) :
    s = t ∨ s = t.swap := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (side_card_eq_one_of_card_le_two hX s).1
  obtain ⟨x', hx'⟩ := Finset.card_eq_one.mp (side_card_eq_one_of_card_le_two hX t).1
  by_cases hxx : x = x'
  · left
    refine (eq_iff_sides s t).mpr ⟨by rw [hx, hx', hxx], ?_⟩
    rw [sideB_eq_compl, sideB_eq_compl, hx, hx', hxx]
  · right
    have huniv : (Finset.univ : Finset X) = {x, x'} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ ({x, x'} : Finset X)) ?_).symm
      rw [Finset.card_pair hxx]
      exact hX
    have hxc : ({x} : Finset X)ᶜ = {x'} := by
      ext z
      rw [Finset.mem_compl, Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · intro hz
        have hzu : z ∈ ({x, x'} : Finset X) := huniv ▸ Finset.mem_univ z
        rcases Finset.mem_insert.mp hzu with h | h
        · exact absurd h hz
        · exact Finset.mem_singleton.mp h
      · rintro rfl
        exact fun h => hxx h.symm
    refine (eq_iff_sides s t.swap).mpr ⟨?_, ?_⟩
    · rw [swap_sideA, sideB_eq_compl, hx', hx, ← hxc, compl_compl]
    · rw [swap_sideB, hx', sideB_eq_compl, hx, hxc]

/-- ★ **收口引理**：把「泛函线性 + 逐 split 取值 + 唯一性」化成 `b₁ idx = b₂ idx`。 -/
theorem weights_eq_of_functional (S : ι → Split X) (b₁ b₂ : ι → ℝ) (idx : ι)
    (F : (X → X → ℝ) → ℝ) (Φ : ι → Prop) [DecidablePred Φ]
    (hlin : F (fun p q => ∑ i, (b₁ i - b₂ i) * sepInd (S i) p q)
      = ∑ i, (b₁ i - b₂ i) * F (sepInd (S i)))
    (hz : F (fun p q => ∑ i, (b₁ i - b₂ i) * sepInd (S i) p q) = 0)
    (hper : ∀ i, F (sepInd (S i)) = 2 * (if Φ i then (1 : ℝ) else 0))
    (huniq : ∀ i, Φ i → i = idx) (hidx : Φ idx) : b₁ idx = b₂ idx := by
  have hsingle : (∑ i, (b₁ i - b₂ i) * (2 * (if Φ i then (1 : ℝ) else 0)))
      = 2 * (b₁ idx - b₂ idx) := by
    rw [Finset.sum_eq_single idx]
    · rw [ite_eq_left hidx]; ring
    · intro i _ hi; rw [ite_eq_right (fun h => hi (huniq i h))]; ring
    · intro h; exact absurd (Finset.mem_univ idx) h
  have hsum0 : (∑ i, (b₁ i - b₂ i) * (2 * (if Φ i then (1 : ℝ) else 0))) = 0 := by
    have h1 : (∑ i, (b₁ i - b₂ i) * (2 * (if Φ i then (1 : ℝ) else 0)))
        = ∑ i, (b₁ i - b₂ i) * F (sepInd (S i)) :=
      Finset.sum_congr rfl fun i _ => by rw [hper i]
    rw [h1, ← hlin, hz]
  rw [hsingle] at hsum0
  linarith

/-- 后缀弧 `[j+1, n−1]` 是前缀弧 `[0, j]` 的补。 -/
theorem suffix_eq_compl_of_prefix {n : ℕ} (f : X ≃ Fin n) (q0 qj qj1 ql : Fin n)
    (h0 : q0.val = 0) (hjl : qj1.val = qj.val + 1) (hl : ql.val = n - 1) :
    cycArc f qj1 ql = (cycArc f q0 qj)ᶜ := by
  ext x
  rw [mem_cycArc, Finset.mem_compl, mem_cycArc, Finset.mem_Icc, Finset.mem_Icc]
  have hx := (f x).isLt
  constructor
  · rintro ⟨h1, h2⟩ ⟨h3, h4⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

omit [DecidableEq X] in
/-- 位置 `[0, n−1]` 全取到时 `cycArc` 是全集。 -/
theorem cycArc_univ_of_bounds {n : ℕ} (f : X ≃ Fin n) {i j : Fin n} (hi : i.val = 0)
    (hj : j.val = n - 1) : cycArc f i j = Finset.univ := by
  have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
  have hj' : j = ⟨n - 1, by omega⟩ := Fin.ext hj
  ext x
  rw [hi', hj', mem_cycArc, Finset.mem_Icc]
  exact ⟨fun _ => Finset.mem_univ x, fun _ => ⟨by omega, by omega⟩⟩

/-- ★★★ **主定理（缺口 2 已证）**：环形 split 族（去重、排除两侧互换重复）的指示矩阵
**列满秩**，即权重向量 `b` 由系统发生距离唯一确定。

证明用**显式逆矩阵**：每个环形 arc `[i,j]` 的权重由四点（或三点）组合直接解出
（`quad_sepInd_d` / `quad_sepInd_h` / `tri_sepInd_l`），三类泛函覆盖全部弧。 -/
theorem circularIndicator_injective {X : Type*} [Fintype X] [DecidableEq X] {ι : Type*}
    [Fintype ι] (S : ι → Split X) (hS : Function.Injective S)
    (hswap : ∀ i j : ι, S i = (S j).swap → i = j)
    (harc : ∃ n : ℕ, ∃ f : X ≃ Fin n,
      ∀ i : ι, IsCyclicArc f (S i).sideA ∨ IsCyclicArc f (S i).sideB) :
    Function.Injective (fun b : ι → ℝ => fun p : X × X =>
      ∑ i, b i * (if (p.1 ∈ (S i).sideA ∧ p.2 ∈ (S i).sideB) ∨
        (p.1 ∈ (S i).sideB ∧ p.2 ∈ (S i).sideA) then 1 else 0)) := by
  classical
  obtain ⟨n, f, hf⟩ := harc
  intro b₁ b₂ hEq
  have hpoint : ∀ p q : X,
      (∑ i, b₁ i * sepInd (S i) p q) = ∑ i, b₂ i * sepInd (S i) p q := by
    intro p q
    have h := congrFun hEq (p, q)
    simpa only [sepInd] using h
  by_cases hsmall : Fintype.card X ≤ 2
  · -- |X| ≤ 2：每个 split 的一侧是单点 ⇒ 至多一个 swap 类 ⇒ ι 至多一个元素
    have hsub : Subsingleton ι := ⟨fun x y => by
      rcases eq_or_swap_of_card_le_two hsmall (S x) (S y) with h | h
      · exact hS h
      · exact hswap x y h⟩
    by_cases hne : Nonempty ι
    · obtain ⟨y⟩ := hne
      have hx : ∀ x : ι, x = y := fun x => hsub.elim x y
      obtain ⟨p, hp⟩ := (S y).nonempty 0
      obtain ⟨q, hq⟩ := (S y).nonempty 1
      have hind : sepInd (S y) p q = 1 := by
        rw [sepInd, ite_eq_left]
        exact Or.inl ⟨hp, hq⟩
      have hy : b₁ y = b₂ y := by
        have h := hpoint p q
        have h1 : (∑ i, b₁ i * sepInd (S i) p q) = b₁ y * sepInd (S y) p q := by
          refine Finset.sum_eq_single y ?_ ?_
          · intro i _ hi; exact absurd (hx i) hi
          · intro hh; exact absurd (Finset.mem_univ y) hh
        have h2 : (∑ i, b₂ i * sepInd (S i) p q) = b₂ y * sepInd (S y) p q := by
          refine Finset.sum_eq_single y ?_ ?_
          · intro i _ hi; exact absurd (hx i) hi
          · intro hh; exact absurd (Finset.mem_univ y) hh
        rw [h1, h2, hind, mul_one, mul_one] at h
        exact h
      funext x
      rw [hx x]
      exact hy
    · exact funext fun x => absurd ⟨x⟩ hne
  · -- |X| ≥ 3：显式逆矩阵
    have hn : 3 ≤ n := by
      have hc : Fintype.card X = n := by
        rw [← Fintype.card_fin n]
        exact Fintype.card_congr f
      omega
    have hex : ∀ x : ι, ∃ p : Fin n × Fin n, p.1 ≤ p.2 ∧
        ((S x).sideA = cycArc f p.1 p.2 ∨ (S x).sideA = (cycArc f p.1 p.2)ᶜ) := by
      intro x
      rcases hf x with h | h
      · obtain ⟨i, j, hij, h'⟩ := h
        exact ⟨(i, j), hij, h'⟩
      · obtain ⟨i, j, hij, h'⟩ := h
        refine ⟨(i, j), hij, ?_⟩
        rcases h' with h' | h'
        · right
          have hb : (S x).sideAᶜ = cycArc f i j := by rw [← sideB_eq_compl (S x), h']
          rw [← hb, compl_compl]
        · left
          have hb : (S x).sideAᶜ = (cycArc f i j)ᶜ := by rw [← sideB_eq_compl (S x), h']
          exact compl_inj_iff.mp hb
    let W : ι → Fin n × Fin n := fun x => Classical.choose (hex x)
    have hWle : ∀ x, (W x).1 ≤ (W x).2 := fun x => (Classical.choose_spec (hex x)).1
    have hWside : ∀ x, (S x).sideA = cycArc f (W x).1 (W x).2 ∨
        (S x).sideA = (cycArc f (W x).1 (W x).2)ᶜ := fun x => (Classical.choose_spec (hex x)).2
    have hc0 : ∀ p q : X, (∑ i, (b₁ i - b₂ i) * sepInd (S i) p q) = 0 := by
      intro p q
      have hstep : (∑ i, (b₁ i - b₂ i) * sepInd (S i) p q)
          = (∑ i, b₁ i * sepInd (S i) p q) - (∑ i, b₂ i * sepInd (S i) p q) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hstep, hpoint p q, sub_self]
    funext idx
    have key_eq : ∀ x : ι, cycArc f (W x).1 (W x).2 = cycArc f (W idx).1 (W idx).2 → x = idx :=
      fun x hJ => by
        have hx : (S x).sideA = cycArc f (W idx).1 (W idx).2 ∨
            (S x).sideA = (cycArc f (W idx).1 (W idx).2)ᶜ := by
          rcases hWside x with h | h
          · exact Or.inl (by rw [h, hJ])
          · exact Or.inr (by rw [h, hJ])
        rcases eq_or_swap_of_sides hx (hWside idx) with h | h
        · exact hS h
        · exact hswap x idx h
    have key_compl : ∀ x : ι,
        cycArc f (W x).1 (W x).2 = (cycArc f (W idx).1 (W idx).2)ᶜ → x = idx :=
      fun x hJ => by
        have hx : (S x).sideA = cycArc f (W idx).1 (W idx).2 ∨
            (S x).sideA = (cycArc f (W idx).1 (W idx).2)ᶜ := by
          rcases hWside x with h | h
          · exact Or.inr (by rw [h, hJ])
          · exact Or.inl (by rw [h, hJ, compl_compl])
        rcases eq_or_swap_of_sides hx (hWside idx) with h | h
        · exact hS h
        · exact hswap x idx h
    have hnotlast : ¬((W idx).1.val = 0 ∧ (W idx).2.val = n - 1) := by
      rintro ⟨ha, hb⟩
      have huniv := cycArc_univ_of_bounds f ha hb
      rcases hWside idx with h | h
      · rw [huniv] at h
        have hB : (S idx).sideB = ∅ := by rw [sideB_eq_compl, h, Finset.compl_univ]
        exact absurd (hB ▸ (show (S idx).sideB.Nonempty from (S idx).nonempty 1)) (by simp)
      · rw [huniv, Finset.compl_univ] at h
        exact absurd (h ▸ (show (S idx).sideA.Nonempty from (S idx).nonempty 0)) (by simp)
    rcases Nat.eq_zero_or_pos (W idx).1.val with ha | ha
    · rcases Nat.eq_zero_or_pos (W idx).2.val with hb | hb
      · -- (0, 0)：单元素前缀 split（L 泛函）
        have h0n : 0 < n := by omega
        have h1n : 1 < n := by omega
        have hlast : n - 1 < n := by omega
        set q0 : Fin n := ⟨0, h0n⟩ with hq0
        set q1 : Fin n := ⟨1, h1n⟩ with hq1
        set ql : Fin n := ⟨n - 1, hlast⟩ with hql
        have hq0v : q0.val = 0 := rfl
        have hq1v : q1.val = 1 := rfl
        have hqlv : ql.val = n - 1 := rfl
        have hsuf : cycArc f q1 ql = (cycArc f q0 q0)ᶜ :=
          suffix_eq_compl_of_prefix f q0 q0 q1 ql hq0v (by omega) hqlv
        have hJ0 : cycArc f (W idx).1 (W idx).2 = cycArc f q0 q0 := by
          have e1 : (W idx).1 = q0 := Fin.ext (by omega)
          have e2 : (W idx).2 = q0 := Fin.ext (by omega)
          rw [e1, e2]
        refine weights_eq_of_functional S b₁ b₂ idx
          (fun φ => tri φ (f.symm q0) (f.symm q1) (f.symm ql))
          (fun i => ((W i).1.val = 0 ∧ (W i).2.val = 0) ∨
            ((W i).1.val = 1 ∧ (W i).2.val = n - 1)) ?_ ?_ ?_ ?_ ?_
        · exact tri_sum (fun i => b₁ i - b₂ i) (fun i p q => sepInd (S i) p q) _ _ _
        · simp only [tri]; rw [hc0, hc0, hc0]; ring
        · intro i
          exact tri_sepInd_l f (hWle i) (hWside i) hn q0 q1 ql hq0v hq1v hqlv
        · intro i hi
          rcases hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · refine key_eq i ?_
            have h1 : (W i).1 = q0 := Fin.ext (by omega)
            have h2 : (W i).2 = q0 := Fin.ext (by omega)
            rw [h1, h2, hJ0]
          · refine key_compl i ?_
            have h1 : (W i).1 = q1 := Fin.ext (by omega)
            have h2 : (W i).2 = ql := Fin.ext (by omega)
            rw [h1, h2, hsuf, hJ0]
        · exact Or.inl ⟨ha, hb⟩
      · -- (0, b)（b ≥ 1）：前缀 `[0,b]`（H 泛函）
        have hbn : (W idx).2.val + 1 < n := by
          have hnot := hnotlast
          omega
        have h0n : 0 < n := by omega
        have hlast : n - 1 < n := by omega
        set q0 : Fin n := ⟨0, h0n⟩ with hq0
        set qj : Fin n := ⟨(W idx).2.val, (W idx).2.isLt⟩ with hqj
        set qj1 : Fin n := ⟨(W idx).2.val + 1, hbn⟩ with hqj1
        set ql : Fin n := ⟨n - 1, hlast⟩ with hql
        have hq0v : q0.val = 0 := rfl
        have hqjv : qj.val = (W idx).2.val := rfl
        have hqj1v : qj1.val = (W idx).2.val + 1 := rfl
        have hqlv : ql.val = n - 1 := rfl
        have hP : cycArc f (W idx).1 (W idx).2 = cycArc f q0 qj := by
          have e1 : (W idx).1 = q0 := Fin.ext (by omega)
          have e2 : (W idx).2 = qj := Fin.ext (by omega)
          rw [e1, e2]
        refine weights_eq_of_functional S b₁ b₂ idx
          (fun φ => quad φ (f.symm ql) (f.symm q0) (f.symm qj) (f.symm qj1))
          (fun i => ((W i).1.val = 0 ∧ (W i).2.val = qj.val) ∨
            ((W i).1.val = qj.val + 1 ∧ (W i).2.val = n - 1)) ?_ ?_ ?_ ?_ ?_
        · exact quad_sum (fun i => b₁ i - b₂ i) (fun i p q => sepInd (S i) p q) _ _ _ _
        · simp only [quad]; rw [hc0, hc0, hc0, hc0]; ring
        · intro i
          exact quad_sepInd_h f (hWle i) (hWside i) q0 qj qj1 ql hq0v (by omega) (by omega) hqlv
        · intro i hi
          rcases hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · refine key_eq i ?_
            have h1 : (W i).1 = q0 := Fin.ext (by omega)
            have h2 : (W i).2 = qj := Fin.ext (by omega)
            rw [h1, h2, hP]
          · refine key_compl i ?_
            have h1 : (W i).1 = qj1 := Fin.ext (by omega)
            have h2 : (W i).2 = ql := Fin.ext (by omega)
            have hsuf : cycArc f qj1 ql = (cycArc f q0 qj)ᶜ :=
              suffix_eq_compl_of_prefix f q0 qj qj1 ql hq0v (by omega) hqlv
            rw [h1, h2, hsuf, hP]
        · exact Or.inl ⟨ha, by omega⟩
    · by_cases hb : (W idx).2.val = n - 1
      · by_cases ha1 : (W idx).1.val = 1
        · -- (1, n−1)：`{p₀}|rest` 的另一表示（L 泛函）
          have h0n : 0 < n := by omega
          have h1n : 1 < n := by omega
          have hlast : n - 1 < n := by omega
          set q0 : Fin n := ⟨0, h0n⟩ with hq0
          set q1 : Fin n := ⟨1, h1n⟩ with hq1
          set ql : Fin n := ⟨n - 1, hlast⟩ with hql
          have hq0v : q0.val = 0 := rfl
          have hq1v : q1.val = 1 := rfl
          have hqlv : ql.val = n - 1 := rfl
          have hsuf : cycArc f q1 ql = (cycArc f q0 q0)ᶜ :=
            suffix_eq_compl_of_prefix f q0 q0 q1 ql hq0v (by omega) hqlv
          have hJ0 : cycArc f (W idx).1 (W idx).2 = cycArc f q1 ql := by
            have e1 : (W idx).1 = q1 := Fin.ext (by omega)
            have e2 : (W idx).2 = ql := Fin.ext (by omega)
            rw [e1, e2]
          refine weights_eq_of_functional S b₁ b₂ idx
            (fun φ => tri φ (f.symm q0) (f.symm q1) (f.symm ql))
            (fun i => ((W i).1.val = 0 ∧ (W i).2.val = 0) ∨
              ((W i).1.val = 1 ∧ (W i).2.val = n - 1)) ?_ ?_ ?_ ?_ ?_
          · exact tri_sum (fun i => b₁ i - b₂ i) (fun i p q => sepInd (S i) p q) _ _ _
          · simp only [tri]; rw [hc0, hc0, hc0]; ring
          · intro i
            exact tri_sepInd_l f (hWle i) (hWside i) hn q0 q1 ql hq0v hq1v hqlv
          · intro i hi
            rcases hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · refine key_compl i ?_
              have h1 : (W i).1 = q0 := Fin.ext (by omega)
              have h2 : (W i).2 = q0 := Fin.ext (by omega)
              rw [h1, h2, hJ0, hsuf, compl_compl]
            · refine key_eq i ?_
              have h1 : (W i).1 = q1 := Fin.ext (by omega)
              have h2 : (W i).2 = ql := Fin.ext (by omega)
              rw [h1, h2, hJ0]
          · exact Or.inr ⟨ha1, hb⟩
        · -- (a, n−1)（a ≥ 2）：前缀 `[0,a−1]`（H 泛函）
          have hjn : (W idx).1.val - 1 < n := by omega
          have h0n : 0 < n := by omega
          have hlast : n - 1 < n := by omega
          set q0 : Fin n := ⟨0, h0n⟩ with hq0
          set qj : Fin n := ⟨(W idx).1.val - 1, hjn⟩ with hqj
          set qj1 : Fin n := ⟨(W idx).1.val, (W idx).1.isLt⟩ with hqj1
          set ql : Fin n := ⟨n - 1, hlast⟩ with hql
          have hq0v : q0.val = 0 := rfl
          have hqjv : qj.val = (W idx).1.val - 1 := rfl
          have hqj1v : qj1.val = (W idx).1.val := rfl
          have hqlv : ql.val = n - 1 := rfl
          have hP : cycArc f q0 qj = (cycArc f (W idx).1 (W idx).2)ᶜ := by
            have hsuf : cycArc f qj1 ql = (cycArc f q0 qj)ᶜ :=
              suffix_eq_compl_of_prefix f q0 qj qj1 ql hq0v (by omega) hqlv
            have e1 : qj1 = (W idx).1 := Fin.ext (by omega)
            have e2 : ql = (W idx).2 := Fin.ext (by omega)
            rw [e1, e2] at hsuf
            rw [hsuf, compl_compl]
          refine weights_eq_of_functional S b₁ b₂ idx
            (fun φ => quad φ (f.symm ql) (f.symm q0) (f.symm qj) (f.symm qj1))
            (fun i => ((W i).1.val = 0 ∧ (W i).2.val = qj.val) ∨
              ((W i).1.val = qj.val + 1 ∧ (W i).2.val = n - 1)) ?_ ?_ ?_ ?_ ?_
          · exact quad_sum (fun i => b₁ i - b₂ i) (fun i p q => sepInd (S i) p q) _ _ _ _
          · simp only [quad]; rw [hc0, hc0, hc0, hc0]; ring
          · intro i
            exact quad_sepInd_h f (hWle i) (hWside i) q0 qj qj1 ql hq0v (by omega) (by omega) hqlv
          · intro i hi
            rcases hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · refine key_compl i ?_
              have h1 : (W i).1 = q0 := Fin.ext (by omega)
              have h2 : (W i).2 = qj := Fin.ext (by omega)
              rw [h1, h2, hP]
            · refine key_eq i ?_
              have h1 : (W i).1 = qj1 := Fin.ext (by omega)
              have h2 : (W i).2 = ql := Fin.ext (by omega)
              have hsuf : cycArc f qj1 ql = (cycArc f q0 qj)ᶜ :=
                suffix_eq_compl_of_prefix f q0 qj qj1 ql hq0v (by omega) hqlv
              rw [h1, h2, hsuf, hP, compl_compl]
          · exact Or.inr ⟨by omega, hb⟩
      · -- (a, b)（a ≥ 1、b ≤ n−2）：D 泛函
        have hbn : (W idx).2.val + 1 < n := by omega
        have han : (W idx).1.val - 1 < n := by omega
        set a' : Fin n := ⟨(W idx).1.val - 1, han⟩ with ha'
        have h1' : (W idx).1.val = a'.val + 1 := by
          have h : a'.val = (W idx).1.val - 1 := by rw [ha']
          omega
        have h3' : (⟨(W idx).2.val + 1, hbn⟩ : Fin n).val = (W idx).2.val + 1 := rfl
        refine weights_eq_of_functional S b₁ b₂ idx
          (fun φ => quad φ (f.symm a') (f.symm (W idx).1) (f.symm (W idx).2)
            (f.symm ⟨(W idx).2.val + 1, hbn⟩))
          (fun i => ((W i).1.val = (W idx).1.val ∧ (W i).2.val = (W idx).2.val)) ?_ ?_ ?_ ?_ ?_
        · exact quad_sum (fun i => b₁ i - b₂ i) (fun i p q => sepInd (S i) p q) _ _ _ _
        · simp only [quad]; rw [hc0, hc0, hc0, hc0]; ring
        · intro i
          exact quad_sepInd_d f (hWside i) a' (W idx).1 (W idx).2 ⟨(W idx).2.val + 1, hbn⟩
            h1' (Fin.le_iff_val_le_val.mp (hWle idx)) h3'
        · intro i hi
          have h1 : (W i).1 = (W idx).1 := Fin.ext hi.1
          have h2 : (W i).2 = (W idx).2 := Fin.ext hi.2
          exact key_eq i (by rw [h1, h2])
        · exact ⟨rfl, rfl⟩

/-- ★★★ **缺口 2 收口**：`circularIndicatorFullRank_gap`（陈述逐字不变）**已证**。 -/
theorem circularIndicatorFullRank_gap_proved : circularIndicatorFullRank_gap :=
  fun S hS hswap harc => circularIndicator_injective S hS hswap harc

end IndicatorApplication

/-! ## 8. 缺口 1 / 3 的处置（W12g）

### 8.1 缺口 3（`neighborNetAgglomeration_gap`）：★E **空账目** ⇒ **保留缺口**

派单要求先核对退化见证。取 `Step d F := (F = trivialSplitSet X)`（全部「有一侧是单点」的
split）：注册 `Prop` 的两个合取项**都成立**（下一条 `example`）—— 故该 `Prop` 可被
**退化见证**平凡满足，**是空账目**。

⚠️ 按 ★E，本文件**不**把该 `Prop` 登记为已证：`neighborNetAgglomeration_gap` 保持 `def` 原样、
**没有**对应定理。真正的目标（文献 288–328、469–565 行）是定义**真实的** agglomeration `Step`
（聚类对 `Cᵢ`、选择式 (1)(2)(3) 的 `Q` 极小化、约化式 (4)(5) 的「三节点 → 两节点」、反演展开），
并证明「存在由极小化 + 约化驱动的运行，其展开产出环形 split 族」（文献 321–324 行称可用归纳法证明）。
**缺的器材**：聚类对 / 约化的归纳定义 + 反演展开的组合引理 —— 本库完全没有。

### 8.2 缺口 1（`circularDistanceRealization_gap`）：⚠️ **按形式陈述为假** ⇒ 保留缺口

`IsCircularDist` 只约束**上三角**（`i ≤ j ≤ k ≤ l` 的四元组），既不要求 `d` 对称、也不要求零对角；
而 `phyleticDist` **恒对称**、且对角为 `0`。于是取「`d 1 0 = 1`、其余全 `0`」即得反例
（`circularDistanceRealization_gap_false`）。修复形态（对称 + 零对角）另立 `def` 并给出非空见证；
一般 `n` 仍需 Bandelt–Dress 的**孤立指数 / 分裂分解**（本库无；`Phylo/SplitWeak.lean` 只到
「d-split 全体弱相容」），故**如实保留缺口**。 -/

/-- 退化见证用的 `F`：全部「有一侧是单点」的 split（含全部平凡 split）。 -/
noncomputable def trivialSplitSet (X : Type*) [Fintype X] [DecidableEq X] : Finset (Split X) :=
  Finset.univ.filter fun s => (∃ x : X, s.sideA = {x}) ∨ (∃ x : X, s.sideB = {x})

/-- ★E **退化见证（空账目）**：`Step d F := (F = trivialSplitSet X)` 使注册 `Prop` 的
**两个合取项都成立**。⚠️ 它与 Neighbor-Net 的 agglomeration 毫无关系 ⇒ **不**作为缺口的证明。 -/
example (X : Type*) [Fintype X] [DecidableEq X] (hX : 1 < Fintype.card X) :
    (∀ (_d : X → X → ℝ) (F : Finset (Split X)), F = trivialSplitSet X →
        Circular (↑F : Set (Split X)) ∧ ∀ x : X, ∃ s ∈ F, s.sideA = {x} ∨ s.sideB = {x}) ∧
      (∀ (_d : X → X → ℝ), (∀ x y, _d x y = _d y x) →
        ∃ F : Finset (Split X), F = trivialSplitSet X) := by
  constructor
  · rintro _d F rfl
    constructor
    · refine circular_of_trivial _ ?_
      intro s hs
      have hs' : s ∈ trivialSplitSet X := hs
      simp only [trivialSplitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs'
      exact hs'
    · intro x
      have hcomp : ({x} : Finset X)ᶜ.Nonempty := by
        refine Finset.card_pos.mp ?_
        rw [Finset.card_compl, Finset.card_singleton]
        omega
      refine ⟨ofSideA {x} (Finset.singleton_nonempty x) hcomp, ?_, Or.inl (ofSideA_sideA _ _ _)⟩
      simp only [trivialSplitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨x, ofSideA_sideA _ _ _⟩
  · intro _d _
    exact ⟨trivialSplitSet X, rfl⟩

/-- ★D 反例用的 `d`：`d 1 0 = 1`，其余全 `0`（**不对称**，对角为 `0`）。 -/
def dtest3 : Fin 3 → Fin 3 → ℝ := fun x y => if x = 1 ∧ y = 0 then 1 else 0

theorem dtest3_zero_of_le {a b : Fin 3} (hab : a ≤ b) : dtest3 a b = 0 := by
  simp only [dtest3]
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  rw [h1, h2] at hab
  exact absurd hab (by decide)

/-- ★D：`dtest3` **是环形（Kalmanson）距离** —— `IsCircularDist` 只约束上三角，全为 `0`。 -/
theorem dtest3_isCircularDist : IsCircularDist (Equiv.refl (Fin 3)) dtest3 := by
  intro i j k l hij hjk hkl
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  rw [dtest3_zero_of_le hij, dtest3_zero_of_le hkl, dtest3_zero_of_le (hij.trans hjk),
    dtest3_zero_of_le (hjk.trans hkl), dtest3_zero_of_le (hij.trans (hjk.trans hkl)),
    dtest3_zero_of_le hjk]
  norm_num

/-- `phyleticDist` 对称（指示函数的对称性）。 -/
theorem phyleticDist_comm {X : Type*} [Fintype X] [DecidableEq X]
    (F : Finset (Split X)) (w : Split X → ℝ) (x y : X) :
    phyleticDist F w x y = phyleticDist F w y x := by
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  by_cases h : (x ∈ s.sideA ∧ y ∈ s.sideB) ∨ (x ∈ s.sideB ∧ y ∈ s.sideA)
  · rw [ite_eq_left h, ite_eq_left]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  · rw [ite_eq_right h, ite_eq_right]
    intro hh
    exact h (by
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩)

/-- ★D **缺口 1 按形式陈述为假（实例级反驳）**：注册 `Prop` 在 `X = Fin 3`、
`d = dtest3` 处的实例**不成立** —— 若成立，则 `dtest3 1 0 = 1` 与 `phyleticDist` 的**对称性**
（`dtest3 0 1 = 0`）矛盾。这正是「`IsCircularDist` 不要求 `d` 对称」的后果。 -/
theorem circularDistanceRealization_gap_false_at_fin3 :
    ¬ ((∃ n : ℕ, ∃ f : Fin 3 ≃ Fin n, IsCircularDist f dtest3) →
        ∃ (F : Finset (Split (Fin 3))) (w : Split (Fin 3) → ℝ),
          Circular (↑F : Set (Split (Fin 3))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
            ∀ x y : Fin 3, x ≠ y → phyleticDist F w x y = dtest3 x y) := by
  intro h3
  obtain ⟨F, w, _hcirc, _hnn, hdw⟩ :=
    h3 ⟨3, ⟨Equiv.refl (Fin 3), dtest3_isCircularDist⟩⟩
  have h01 : phyleticDist F w 0 1 = 0 := hdw 0 1 (by decide)
  have h10 : phyleticDist F w 1 0 = 1 := hdw 1 0 (by decide)
  rw [phyleticDist_comm F w 1 0, h01] at h10
  norm_num at h10

/-- ⬜ **修复形态（W12g）**：环形距离的实现 —— 加**对称 + 零对角**（否则见
`circularDistanceRealization_gap_false`）。一般 `n` 仍缺 Bandelt–Dress 分裂分解。 -/
def circularDistanceRealization_gap_corrected : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X] (d : X → X → ℝ),
    (∀ x : X, d x x = 0) → (∀ x y : X, d x y = d y x) →
      (∃ n : ℕ, ∃ f : X ≃ Fin n, IsCircularDist f d) →
        ∃ (F : Finset (Split X)) (w : Split X → ℝ),
          Circular (↑F : Set (Split X)) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
            ∀ x y : X, x ≠ y → phyleticDist F w x y = d x y

/-- ★B **修复形态的非空见证**：常零距离由**空族 + 零权重**实现
（`Circular ∅`、非负性、逐点等式都真的被验证，不是空转）。 -/
theorem zeroDist_realized (X : Type*) [Fintype X] [DecidableEq X] :
    ∃ (F : Finset (Split X)) (w : Split X → ℝ),
      Circular (↑F : Set (Split X)) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
        ∀ x y : X, x ≠ y → phyleticDist F w x y = 0 := by
  classical
  refine ⟨∅, fun _ => 0, ⟨Fintype.card X, Fintype.equivFin X, fun s hs => absurd hs (by simp)⟩,
    fun s hs => absurd hs (by simp), ?_⟩
  intro x y _
  simp [phyleticDist]

/-! ## 9. 缺口 1 的推进（W12g-3）：**非负性（一般 `n`）** + `n = 3, 4` 实例

§7 已证「权重由距离**唯一确定**」（显式逆矩阵 `M`）—— 实现方向最难的一半。剩下两件事：

* **(i) 非负性 `w ≥ 0`**：由 Kalmanson 不等式**逐条**给出（`kalmanson_triangle/H/D`，**一般 `n`**，
  不依赖 Bandelt–Dress）：内部弧 `[i,j]`（`i ≥ 1`）↔ 不等式 (2) 于 `(i−1,i,j,j+1)`；
  前缀弧 `[0,j]` ↔ 不等式 (1) 于 `(0,j,j+1,n−1)`；单元素弧 ↔ 三角不等式（`i = j` 情形）。
* **(ii) 恒等 `phyleticDist F w = d`**：本节对 `n = 3, 4` 逐点验证
  （`circularRealization_fin3/fin4`）；一般 `n` 另立 `circularWeights_realization_gap`。

数值核对（逆矩阵还原、**筛选式**非负性/恒等、非负性的四元组路线图）：
`scripts/msc/w12g_circular_realization_small_n.py`。 -/

section CircularRealization

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- ★ **非负性（三角不等式）**：Kalmanson 的 `i = j` 情形。 -/
theorem kalmanson_triangle {n : ℕ} (f : X ≃ Fin n) (d : X → X → ℝ)
    (hdiag : ∀ x, d x x = 0) (hd : IsCircularDist f d)
    (a b c : Fin n) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ d (f.symm a) (f.symm b) + d (f.symm a) (f.symm c) - d (f.symm b) (f.symm c) := by
  have h := (hd a a b c le_rfl hab hbc).1
  rw [hdiag (f.symm a)] at h
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★ **非负性（前缀弧 `[0,j]`）**：Kalmanson 不等式 (1) 于四元组 `(a,b,c,e)`。 -/
theorem kalmanson_H {n : ℕ} (f : X ≃ Fin n) (d : X → X → ℝ) (hsym : ∀ x y, d x y = d y x)
    (hd : IsCircularDist f d) (a b c e : Fin n) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) :
    0 ≤ d (f.symm e) (f.symm b) + d (f.symm a) (f.symm c)
      - d (f.symm a) (f.symm b) - d (f.symm e) (f.symm c) := by
  have h := (hd a b c e hab hbc hce).1
  rw [hsym (f.symm e) (f.symm b), hsym (f.symm e) (f.symm c)]
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★ **非负性（内部弧 `[i,j]`，`i ≥ 1`）**：Kalmanson 不等式 (2) 于四元组 `(a,b,c,e)`。 -/
theorem kalmanson_D {n : ℕ} (f : X ≃ Fin n) (d : X → X → ℝ)
    (hd : IsCircularDist f d) (a b c e : Fin n) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) :
    0 ≤ d (f.symm a) (f.symm c) + d (f.symm b) (f.symm e)
      - d (f.symm b) (f.symm c) - d (f.symm a) (f.symm e) := by
  have h := (hd a b c e hab hbc hce).2
  linarith

/-! ### 9.1 `n = 3` 实例（`X = Fin 3`，环序 = 恒等） -/

/-- 平凡 split `{0} | {1,2}`（`Fin 3`）。 -/
def c₀ : Split (Fin 3) := ofSideA {0} (by decide) (by decide)

/-- 平凡 split `{1} | {0,2}`（`Fin 3`）。 -/
def c₁ : Split (Fin 3) := ofSideA {1} (by decide) (by decide)

/-- 平凡 split `{2} | {0,1}`（`Fin 3`）。 -/
def c₂ : Split (Fin 3) := ofSideA {2} (by decide) (by decide)

/-- ★ 环形族（`Fin 3`：恒等环序下的全部三条 split）。 -/
def G₃ : Finset (Split (Fin 3)) := {c₀, c₁, c₂}

/-- ★ **显式解出的权重**（§7 的逆矩阵行：L / D / H）。 -/
noncomputable def v₃ (d : Fin 3 → Fin 3 → ℝ) : Split (Fin 3) → ℝ := fun s =>
  if s = c₀ then (d 0 1 + d 0 2 - d 1 2) / 2
  else if s = c₁ then (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2
  else if s = c₂ then (d 2 1 - d 0 1 - d 2 2 + d 0 2) / 2
  else 0

@[simp] theorem c₀_ne_c₁ : c₀ ≠ c₁ := by decide

@[simp] theorem c₀_ne_c₂ : c₀ ≠ c₂ := by decide

@[simp] theorem c₁_ne_c₂ : c₁ ≠ c₂ := by decide

@[simp] theorem c₁_ne_c₀ : c₁ ≠ c₀ := fun h => c₀_ne_c₁ h.symm

@[simp] theorem c₂_ne_c₀ : c₂ ≠ c₀ := fun h => c₀_ne_c₂ h.symm

@[simp] theorem c₂_ne_c₁ : c₂ ≠ c₁ := fun h => c₁_ne_c₂ h.symm

@[simp] theorem v₃_c₀ (d : Fin 3 → Fin 3 → ℝ) : v₃ d c₀ = (d 0 1 + d 0 2 - d 1 2) / 2 := by
  simp [v₃]

@[simp] theorem v₃_c₁ (d : Fin 3 → Fin 3 → ℝ) :
    v₃ d c₁ = (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2 := by
  simp [v₃]

@[simp] theorem v₃_c₂ (d : Fin 3 → Fin 3 → ℝ) :
    v₃ d c₂ = (d 2 1 - d 0 1 - d 2 2 + d 0 2) / 2 := by
  simp [v₃]

theorem phyleticDist_triple (a b c : Split (Fin 3)) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : Split (Fin 3) → ℝ) (x y : Fin 3) :
    phyleticDist ({a, b, c} : Finset (Split (Fin 3))) w x y
      = w a * sepInd a x y + (w b * sepInd b x y + w c * sepInd c x y) := by
  simp only [phyleticDist, sepInd]
  rw [Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, hab, hac]),
    Finset.sum_insert (by simp [Finset.mem_singleton, hbc]), Finset.sum_singleton]

/-- ★★★ **`n = 3` 的恒等**（干净上下文：只带具体的对称/对角等式）。 -/
theorem v₃_realizes (d : Fin 3 → Fin 3 → ℝ)
    (h01 : d 0 1 = d 1 0) (h02 : d 0 2 = d 2 0) (h12 : d 1 2 = d 2 1)
    (hd1 : d 1 1 = 0) (hd2 : d 2 2 = 0) :
    ∀ x y : Fin 3, x ≠ y → phyleticDist G₃ (v₃ d) x y = d x y := by
  intro x y hxy
  rw [show G₃ = ({c₀, c₁, c₂} : Finset (Split (Fin 3))) from rfl,
    phyleticDist_triple c₀ c₁ c₂ c₀_ne_c₁ c₀_ne_c₂ c₁_ne_c₂ (v₃ d) x y]
  simp only [v₃_c₀, v₃_c₁, v₃_c₂]
  fin_cases x <;> fin_cases y <;>
    simp_all [sepInd, c₀, c₁, c₂] <;>
    linarith [h01, h02, h12, hd1, hd2]

/-- ★★★ **`n = 3` 实例（修复形态）**：环形（Kalmanson）+ 对称 + 零对角 `d` 由**非负**加权
环形族实现 —— 权重恰是 §7 逆矩阵的行（`v₃`）；非负性用一般 `n` 的 `kalmanson_*` 引理。 -/
theorem circularRealization_fin3 (d : Fin 3 → Fin 3 → ℝ) (hdiag : ∀ x, d x x = 0)
    (hsym : ∀ x y, d x y = d y x) (hd : IsCircularDist (Equiv.refl (Fin 3)) d) :
    ∃ (F : Finset (Split (Fin 3))) (w : Split (Fin 3) → ℝ),
      Circular (↑F : Set (Split (Fin 3))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
        ∀ x y : Fin 3, x ≠ y → phyleticDist F w x y = d x y := by
  refine ⟨G₃, v₃ d, ?_, ?_, ?_⟩
  · refine circular_of_trivial _ ?_
    intro s hs
    have hs' : s ∈ G₃ := hs
    simp only [G₃, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [c₀]⟩
    · exact Or.inl ⟨1, by simp [c₁]⟩
    · exact Or.inl ⟨2, by simp [c₂]⟩
  · intro s hs
    have hs' : s ∈ G₃ := hs
    simp only [G₃, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl
    · rw [v₃_c₀]
      have h := kalmanson_triangle (Equiv.refl (Fin 3)) d hdiag hd 0 1 2 (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₃_c₁]
      have h := kalmanson_D (Equiv.refl (Fin 3)) d hd 0 1 1 2 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₃_c₂]
      have h := kalmanson_H (Equiv.refl (Fin 3)) d hsym hd 0 1 2 2 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
  · exact v₃_realizes d (hsym 0 1) (hsym 0 2) (hsym 1 2) (hdiag 1) (hdiag 2)

/-! ### 9.2 `n = 4` 实例（`X = Fin 4`，环序 = 恒等） -/

/-- 代表弧 `[0,0]` 的 split：`{0} | {1,2,3}`。 -/
def e₀₀ : Split (Fin 4) := ofSideA {0} (by decide) (by decide)

/-- 代表弧 `[0,1]` 的 split：`{0,1} | {2,3}`。 -/
def e₀₁ : Split (Fin 4) := ofSideA {0, 1} (by decide) (by decide)

/-- 代表弧 `[0,2]` 的 split：`{0,1,2} | {3}`。 -/
def e₀₂ : Split (Fin 4) := ofSideA {0, 1, 2} (by decide) (by decide)

/-- 代表弧 `[1,1]` 的 split：`{1} | {0,2,3}`。 -/
def e₁₁ : Split (Fin 4) := ofSideA {1} (by decide) (by decide)

/-- 代表弧 `[1,2]` 的 split：`{1,2} | {0,3}`。 -/
def e₁₂ : Split (Fin 4) := ofSideA {1, 2} (by decide) (by decide)

/-- 代表弧 `[2,2]` 的 split：`{2} | {0,1,3}`。 -/
def e₂₂ : Split (Fin 4) := ofSideA {2} (by decide) (by decide)

/-- ★ 环形族（`Fin 4`：环序 `0,1,2,3` 的代表弧 `[i,j]`，`j ≤ 2`；共 `binom 4 2 = 6` 条）。 -/
def G₄ : Finset (Split (Fin 4)) := {e₀₀, e₀₁, e₀₂, e₁₁, e₁₂, e₂₂}

/-- ★ **显式解出的权重**（§7 的逆矩阵行：L / H / D）。 -/
noncomputable def v₄ (d : Fin 4 → Fin 4 → ℝ) : Split (Fin 4) → ℝ := fun s =>
  if s = e₀₀ then (d 0 1 + d 0 3 - d 1 3) / 2
  else if s = e₀₁ then (d 3 1 - d 0 1 - d 3 2 + d 0 2) / 2
  else if s = e₀₂ then (d 3 2 - d 0 2 - d 3 3 + d 0 3) / 2
  else if s = e₁₁ then (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2
  else if s = e₁₂ then (d 0 2 - d 1 2 - d 0 3 + d 1 3) / 2
  else if s = e₂₂ then (d 1 2 - d 2 2 - d 1 3 + d 2 3) / 2
  else 0

@[simp] theorem e₀₀_sideA : e₀₀.sideA = ({0} : Finset (Fin 4)) := by simp [e₀₀]

@[simp] theorem e₀₁_sideA : e₀₁.sideA = ({0, 1} : Finset (Fin 4)) := by simp [e₀₁]

@[simp] theorem e₀₂_sideA : e₀₂.sideA = ({0, 1, 2} : Finset (Fin 4)) := by simp [e₀₂]

@[simp] theorem e₁₁_sideA : e₁₁.sideA = ({1} : Finset (Fin 4)) := by simp [e₁₁]

@[simp] theorem e₁₂_sideA : e₁₂.sideA = ({1, 2} : Finset (Fin 4)) := by simp [e₁₂]

@[simp] theorem e₂₂_sideA : e₂₂.sideA = ({2} : Finset (Fin 4)) := by simp [e₂₂]

theorem isCyclicArc_e₀₀ : IsCyclicArc (Equiv.refl (Fin 4)) e₀₀.sideA := by
  refine ⟨0, 0, by decide, Or.inl ?_⟩
  rw [e₀₀_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_e₀₁ : IsCyclicArc (Equiv.refl (Fin 4)) e₀₁.sideA := by
  refine ⟨0, 1, by decide, Or.inl ?_⟩
  rw [e₀₁_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_e₀₂ : IsCyclicArc (Equiv.refl (Fin 4)) e₀₂.sideA := by
  refine ⟨0, 2, by decide, Or.inl ?_⟩
  rw [e₀₂_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_e₁₁ : IsCyclicArc (Equiv.refl (Fin 4)) e₁₁.sideA := by
  refine ⟨1, 1, by decide, Or.inl ?_⟩
  rw [e₁₁_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_e₁₂ : IsCyclicArc (Equiv.refl (Fin 4)) e₁₂.sideA := by
  refine ⟨1, 2, by decide, Or.inl ?_⟩
  rw [e₁₂_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_e₂₂ : IsCyclicArc (Equiv.refl (Fin 4)) e₂₂.sideA := by
  refine ⟨2, 2, by decide, Or.inl ?_⟩
  rw [e₂₂_sideA]; ext x; fin_cases x <;> decide

@[simp] theorem e₀₁_ne_e₀₀ : e₀₁ ≠ e₀₀ := by decide
@[simp] theorem e₀₂_ne_e₀₀ : e₀₂ ≠ e₀₀ := by decide
@[simp] theorem e₀₂_ne_e₀₁ : e₀₂ ≠ e₀₁ := by decide
@[simp] theorem e₁₁_ne_e₀₀ : e₁₁ ≠ e₀₀ := by decide
@[simp] theorem e₁₁_ne_e₀₁ : e₁₁ ≠ e₀₁ := by decide
@[simp] theorem e₁₁_ne_e₀₂ : e₁₁ ≠ e₀₂ := by decide
@[simp] theorem e₁₂_ne_e₀₀ : e₁₂ ≠ e₀₀ := by decide
@[simp] theorem e₁₂_ne_e₀₁ : e₁₂ ≠ e₀₁ := by decide
@[simp] theorem e₁₂_ne_e₀₂ : e₁₂ ≠ e₀₂ := by decide
@[simp] theorem e₁₂_ne_e₁₁ : e₁₂ ≠ e₁₁ := by decide
@[simp] theorem e₂₂_ne_e₀₀ : e₂₂ ≠ e₀₀ := by decide
@[simp] theorem e₂₂_ne_e₀₁ : e₂₂ ≠ e₀₁ := by decide
@[simp] theorem e₂₂_ne_e₀₂ : e₂₂ ≠ e₀₂ := by decide
@[simp] theorem e₂₂_ne_e₁₁ : e₂₂ ≠ e₁₁ := by decide
@[simp] theorem e₂₂_ne_e₁₂ : e₂₂ ≠ e₁₂ := by decide

@[simp] theorem v₄_e₀₀ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₀₀ = (d 0 1 + d 0 3 - d 1 3) / 2 := by simp [v₄]

@[simp] theorem v₄_e₀₁ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₀₁ = (d 3 1 - d 0 1 - d 3 2 + d 0 2) / 2 := by simp [v₄]

@[simp] theorem v₄_e₀₂ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₀₂ = (d 3 2 - d 0 2 - d 3 3 + d 0 3) / 2 := by simp [v₄]

@[simp] theorem v₄_e₁₁ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₁₁ = (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2 := by simp [v₄]

@[simp] theorem v₄_e₁₂ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₁₂ = (d 0 2 - d 1 2 - d 0 3 + d 1 3) / 2 := by simp [v₄]

@[simp] theorem v₄_e₂₂ (d : Fin 4 → Fin 4 → ℝ) :
    v₄ d e₂₂ = (d 1 2 - d 2 2 - d 1 3 + d 2 3) / 2 := by simp [v₄]

theorem phyleticDist_six (w : Split (Fin 4) → ℝ) (x y : Fin 4) :
    phyleticDist G₄ w x y
      = w e₀₀ * sepInd e₀₀ x y + (w e₀₁ * sepInd e₀₁ x y + (w e₀₂ * sepInd e₀₂ x y
        + (w e₁₁ * sepInd e₁₁ x y + (w e₁₂ * sepInd e₁₂ x y + w e₂₂ * sepInd e₂₂ x y)))) := by
  simp only [phyleticDist, sepInd, G₄]
  rw [Finset.sum_insert (by
        simp [Finset.mem_insert, Finset.mem_singleton, (e₀₁_ne_e₀₀).symm, (e₀₂_ne_e₀₀).symm,
          (e₁₁_ne_e₀₀).symm, (e₁₂_ne_e₀₀).symm, (e₂₂_ne_e₀₀).symm]),
    Finset.sum_insert (by
        simp [Finset.mem_insert, Finset.mem_singleton, (e₀₂_ne_e₀₁).symm, (e₁₁_ne_e₀₁).symm,
          (e₁₂_ne_e₀₁).symm, (e₂₂_ne_e₀₁).symm]),
    Finset.sum_insert (by
        simp [Finset.mem_insert, Finset.mem_singleton, (e₁₁_ne_e₀₂).symm, (e₁₂_ne_e₀₂).symm,
          (e₂₂_ne_e₀₂).symm]),
    Finset.sum_insert (by
        simp [Finset.mem_insert, Finset.mem_singleton, (e₁₂_ne_e₁₁).symm, (e₂₂_ne_e₁₁).symm]),
    Finset.sum_insert (by simp [Finset.mem_singleton, (e₂₂_ne_e₁₂).symm]),
    Finset.sum_singleton]
  try ring

/-- ★★★ **`n = 4` 的恒等**（干净上下文：只带具体的对称/对角等式）。 -/
theorem v₄_realizes (d : Fin 4 → Fin 4 → ℝ)
    (h01 : d 0 1 = d 1 0) (h02 : d 0 2 = d 2 0) (h03 : d 0 3 = d 3 0)
    (h12 : d 1 2 = d 2 1) (h13 : d 1 3 = d 3 1) (h23 : d 2 3 = d 3 2)
    (hd1 : d 1 1 = 0) (hd2 : d 2 2 = 0) (hd3 : d 3 3 = 0) :
    ∀ x y : Fin 4, x ≠ y → phyleticDist G₄ (v₄ d) x y = d x y := by
  intro x y hxy
  rw [phyleticDist_six (v₄ d) x y]
  simp only [v₄_e₀₀, v₄_e₀₁, v₄_e₀₂, v₄_e₁₁, v₄_e₁₂, v₄_e₂₂]
  fin_cases x <;> fin_cases y <;>
    simp_all [sepInd, e₀₀, e₀₁, e₀₂, e₁₁, e₁₂, e₂₂] <;>
    linarith [h01, h02, h03, h12, h13, h23, hd1, hd2, hd3]

/-- ★★★ **`n = 4` 实例（修复形态）**：环形（Kalmanson）+ 对称 + 零对角 `d` 由**非负**加权
环形族实现；权重是 §7 逆矩阵的行（`v₄`），非负性用一般 `n` 的 `kalmanson_*` 引理。 -/
theorem circularRealization_fin4 (d : Fin 4 → Fin 4 → ℝ) (hdiag : ∀ x, d x x = 0)
    (hsym : ∀ x y, d x y = d y x) (hd : IsCircularDist (Equiv.refl (Fin 4)) d) :
    ∃ (F : Finset (Split (Fin 4))) (w : Split (Fin 4) → ℝ),
      Circular (↑F : Set (Split (Fin 4))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
        ∀ x y : Fin 4, x ≠ y → phyleticDist F w x y = d x y := by
  refine ⟨G₄, v₄ d, ?_, ?_, ?_⟩
  · refine ⟨4, Equiv.refl (Fin 4), fun s hs => ?_⟩
    have hs' : s ∈ G₄ := hs
    simp only [G₄, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl isCyclicArc_e₀₀
    · exact Or.inl isCyclicArc_e₀₁
    · exact Or.inl isCyclicArc_e₀₂
    · exact Or.inl isCyclicArc_e₁₁
    · exact Or.inl isCyclicArc_e₁₂
    · exact Or.inl isCyclicArc_e₂₂
  · intro s hs
    have hs' : s ∈ G₄ := hs
    simp only [G₄, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [v₄_e₀₀]
      have h := kalmanson_triangle (Equiv.refl (Fin 4)) d hdiag hd 0 1 3 (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₄_e₀₁]
      have h := kalmanson_H (Equiv.refl (Fin 4)) d hsym hd 0 1 2 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₄_e₀₂]
      have h := kalmanson_H (Equiv.refl (Fin 4)) d hsym hd 0 2 3 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₄_e₁₁]
      have h := kalmanson_D (Equiv.refl (Fin 4)) d hd 0 1 1 2 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₄_e₁₂]
      have h := kalmanson_D (Equiv.refl (Fin 4)) d hd 0 1 2 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v₄_e₂₂]
      have h := kalmanson_D (Equiv.refl (Fin 4)) d hd 1 2 2 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
  · exact v₄_realizes d (hsym 0 1) (hsym 0 2) (hsym 0 3) (hsym 1 2) (hsym 1 3) (hsym 2 3)
      (hdiag 1) (hdiag 2) (hdiag 3)

/-! ### 9.3 一般 `n` 的剩余缺口：**恒等**（非负性已证） -/

/-- ⬜ **新登记缺口（W12g-3/4）**：一般 `n` 的**权重–距离恒等**
`phyleticDist F w = d`（`n = 3,4,5` 已证：`circularRealization_fin3/fin4/fin5`，
并合并为 `circularWeights_realization_gap_fin_le_five`）。

⚠️ **非负性不再是缺口**（`kalmanson_triangle/H/D` 对一般 `n` 已证）。剩下的只是恒等，
其正路是**线性代数**：把 §7 的逆矩阵 `M`（三行泛函）与 `A`（弧 ↔ 点对指示）都写成线性映射，
`M ∘ A = id` 由 §7 的隔离引理给出，而「弧族权空间」与「对称零对角点对函数空间」维数都是
`binom n 2` ⇒ `A ∘ M = id` ⇒ 恒等。本库尚缺的是这两空间的**维数簿记**（`finrank`）。
（BdD 1992 的孤立指数 `α_S ≥ 0` 与本库的 `w ≥ 0` 等价，⚠️ 该文**未入库** ⇒ 只作待核实归属。）

**W12g-5 现状**：§10 已落**维数那一半**（`Arc n` / `Pair n`、`arcPairEquiv`、
`card_arc_eq_card_pair`、`finrank_arc_eq_finrank_pair`；⚠️ `Arc` 的护栏必须是 `j+1 < n`
而不是 `j ≤ n−2`，否则 `n = 1` 时双射为假 —— `Arc 1 = {(0,0)}` 而 `Pair 1 = ∅`）。
**剩余三步**：(1) `Alm : (Arc n → ℝ) →ₗ (Pair n → ℝ)`（`phyleticDist` 的线性版）与
`Mlm : (Pair n → ℝ) →ₗ (Arc n → ℝ)`（§7 三行泛函；因要在分支里拿到算术前提，
定义需用 `dite` 而非 `ite`）；(2) `Mlm ∘ Alm = id`（§7 隔离引理 `quad_sepInd_d/h`、
`tri_sepInd_l` 逐弧 + `Finset.sum_ite_eq'` 塌缩）⇒ `Alm` 单射 ⇒ 用 `finrank` 相等 +
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` 得**满射** ⇒ `Alm ∘ Mlm = id`；
(3) 把 `Arc` 权重打包成 `Finset (Split (Fin n))`（`arcSplit` + `Finset.image` + 逆像求和）
并用 §9 的 `kalmanson_*` 给非负性。 -/
def circularWeights_realization_gap (n : ℕ) : Prop :=
  ∀ (d : Fin n → Fin n → ℝ), (∀ x, d x x = 0) → (∀ x y, d x y = d y x) →
    IsCircularDist (Equiv.refl (Fin n)) d →
      ∃ (F : Finset (Split (Fin n))) (w : Split (Fin n) → ℝ),
        Circular (↑F : Set (Split (Fin n))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
          ∀ x y : Fin n, x ≠ y → phyleticDist F w x y = d x y

/-! ### 9.4 `n = 5` 实例（`X = Fin 5`，环序 = 恒等）

代表弧 `[i,j]`（`j ≤ 3`）共 `binom 5 2 = 10` 条；权重由 §7 逆矩阵的行给出。
本节的 boilerplate（45 条 pairwise 互异、10 条弧见证、10 条权重公式）由
`scripts/msc/w12g_fin5_instance_gen.py` 机械生成。 -/

/-- 代表弧 `[0,0]` 的 split：`{0} | 其余`。 -/
def f₀₀ : Split (Fin 5) := ofSideA {0} (by decide) (by decide)

/-- 代表弧 `[0,1]` 的 split：`{0, 1} | 其余`。 -/
def f₀₁ : Split (Fin 5) := ofSideA {0, 1} (by decide) (by decide)

/-- 代表弧 `[0,2]` 的 split：`{0, 1, 2} | 其余`。 -/
def f₀₂ : Split (Fin 5) := ofSideA {0, 1, 2} (by decide) (by decide)

/-- 代表弧 `[0,3]` 的 split：`{0, 1, 2, 3} | 其余`。 -/
def f₀₃ : Split (Fin 5) := ofSideA {0, 1, 2, 3} (by decide) (by decide)

/-- 代表弧 `[1,1]` 的 split：`{1} | 其余`。 -/
def f₁₁ : Split (Fin 5) := ofSideA {1} (by decide) (by decide)

/-- 代表弧 `[1,2]` 的 split：`{1, 2} | 其余`。 -/
def f₁₂ : Split (Fin 5) := ofSideA {1, 2} (by decide) (by decide)

/-- 代表弧 `[1,3]` 的 split：`{1, 2, 3} | 其余`。 -/
def f₁₃ : Split (Fin 5) := ofSideA {1, 2, 3} (by decide) (by decide)

/-- 代表弧 `[2,2]` 的 split：`{2} | 其余`。 -/
def f₂₂ : Split (Fin 5) := ofSideA {2} (by decide) (by decide)

/-- 代表弧 `[2,3]` 的 split：`{2, 3} | 其余`。 -/
def f₂₃ : Split (Fin 5) := ofSideA {2, 3} (by decide) (by decide)

/-- 代表弧 `[3,3]` 的 split：`{3} | 其余`。 -/
def f₃₃ : Split (Fin 5) := ofSideA {3} (by decide) (by decide)

/-- ★ 环形族（`Fin 5`：代表弧 `[i,j]`，`j ≤ 3`）。 -/
def G5 : Finset (Split (Fin 5)) := {f₀₀, f₀₁, f₀₂, f₀₃, f₁₁, f₁₂, f₁₃, f₂₂, f₂₃, f₃₃}

/-- ★ **显式解出的权重**（§7 的逆矩阵行：L / H / D）。 -/
noncomputable def v5 (d : Fin 5 → Fin 5 → ℝ) : Split (Fin 5) → ℝ := fun s =>
  if s = f₀₀ then (d 0 1 + d 0 4 - d 1 4) / 2
  else if s = f₀₁ then (d 4 1 - d 0 1 - d 4 2 + d 0 2) / 2
  else if s = f₀₂ then (d 4 2 - d 0 2 - d 4 3 + d 0 3) / 2
  else if s = f₀₃ then (d 4 3 - d 0 3 - d 4 4 + d 0 4) / 2
  else if s = f₁₁ then (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2
  else if s = f₁₂ then (d 0 2 - d 1 2 - d 0 3 + d 1 3) / 2
  else if s = f₁₃ then (d 0 3 - d 1 3 - d 0 4 + d 1 4) / 2
  else if s = f₂₂ then (d 1 2 - d 2 2 - d 1 3 + d 2 3) / 2
  else if s = f₂₃ then (d 1 3 - d 2 3 - d 1 4 + d 2 4) / 2
  else if s = f₃₃ then (d 2 3 - d 3 3 - d 2 4 + d 3 4) / 2
  else 0

@[simp] theorem f₀₀_sideA : f₀₀.sideA = ({0} : Finset (Fin 5)) := by
  simp [f₀₀]

@[simp] theorem f₀₁_sideA : f₀₁.sideA = ({0, 1} : Finset (Fin 5)) := by
  simp [f₀₁]

@[simp] theorem f₀₂_sideA : f₀₂.sideA = ({0, 1, 2} : Finset (Fin 5)) := by
  simp [f₀₂]

@[simp] theorem f₀₃_sideA : f₀₃.sideA = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  simp [f₀₃]

@[simp] theorem f₁₁_sideA : f₁₁.sideA = ({1} : Finset (Fin 5)) := by
  simp [f₁₁]

@[simp] theorem f₁₂_sideA : f₁₂.sideA = ({1, 2} : Finset (Fin 5)) := by
  simp [f₁₂]

@[simp] theorem f₁₃_sideA : f₁₃.sideA = ({1, 2, 3} : Finset (Fin 5)) := by
  simp [f₁₃]

@[simp] theorem f₂₂_sideA : f₂₂.sideA = ({2} : Finset (Fin 5)) := by
  simp [f₂₂]

@[simp] theorem f₂₃_sideA : f₂₃.sideA = ({2, 3} : Finset (Fin 5)) := by
  simp [f₂₃]

@[simp] theorem f₃₃_sideA : f₃₃.sideA = ({3} : Finset (Fin 5)) := by
  simp [f₃₃]

theorem isCyclicArc_f₀₀ : IsCyclicArc (Equiv.refl (Fin 5)) f₀₀.sideA := by
  refine ⟨0, 0, by decide, Or.inl ?_⟩
  rw [f₀₀_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₀₁ : IsCyclicArc (Equiv.refl (Fin 5)) f₀₁.sideA := by
  refine ⟨0, 1, by decide, Or.inl ?_⟩
  rw [f₀₁_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₀₂ : IsCyclicArc (Equiv.refl (Fin 5)) f₀₂.sideA := by
  refine ⟨0, 2, by decide, Or.inl ?_⟩
  rw [f₀₂_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₀₃ : IsCyclicArc (Equiv.refl (Fin 5)) f₀₃.sideA := by
  refine ⟨0, 3, by decide, Or.inl ?_⟩
  rw [f₀₃_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₁₁ : IsCyclicArc (Equiv.refl (Fin 5)) f₁₁.sideA := by
  refine ⟨1, 1, by decide, Or.inl ?_⟩
  rw [f₁₁_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₁₂ : IsCyclicArc (Equiv.refl (Fin 5)) f₁₂.sideA := by
  refine ⟨1, 2, by decide, Or.inl ?_⟩
  rw [f₁₂_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₁₃ : IsCyclicArc (Equiv.refl (Fin 5)) f₁₃.sideA := by
  refine ⟨1, 3, by decide, Or.inl ?_⟩
  rw [f₁₃_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₂₂ : IsCyclicArc (Equiv.refl (Fin 5)) f₂₂.sideA := by
  refine ⟨2, 2, by decide, Or.inl ?_⟩
  rw [f₂₂_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₂₃ : IsCyclicArc (Equiv.refl (Fin 5)) f₂₃.sideA := by
  refine ⟨2, 3, by decide, Or.inl ?_⟩
  rw [f₂₃_sideA]; ext x; fin_cases x <;> decide

theorem isCyclicArc_f₃₃ : IsCyclicArc (Equiv.refl (Fin 5)) f₃₃.sideA := by
  refine ⟨3, 3, by decide, Or.inl ?_⟩
  rw [f₃₃_sideA]; ext x; fin_cases x <;> decide

@[simp] theorem f₀₁_ne_f₀₀ : f₀₁ ≠ f₀₀ := by decide
@[simp] theorem f₀₂_ne_f₀₀ : f₀₂ ≠ f₀₀ := by decide
@[simp] theorem f₀₂_ne_f₀₁ : f₀₂ ≠ f₀₁ := by decide
@[simp] theorem f₀₃_ne_f₀₀ : f₀₃ ≠ f₀₀ := by decide
@[simp] theorem f₀₃_ne_f₀₁ : f₀₃ ≠ f₀₁ := by decide
@[simp] theorem f₀₃_ne_f₀₂ : f₀₃ ≠ f₀₂ := by decide
@[simp] theorem f₁₁_ne_f₀₀ : f₁₁ ≠ f₀₀ := by decide
@[simp] theorem f₁₁_ne_f₀₁ : f₁₁ ≠ f₀₁ := by decide
@[simp] theorem f₁₁_ne_f₀₂ : f₁₁ ≠ f₀₂ := by decide
@[simp] theorem f₁₁_ne_f₀₃ : f₁₁ ≠ f₀₃ := by decide
@[simp] theorem f₁₂_ne_f₀₀ : f₁₂ ≠ f₀₀ := by decide
@[simp] theorem f₁₂_ne_f₀₁ : f₁₂ ≠ f₀₁ := by decide
@[simp] theorem f₁₂_ne_f₀₂ : f₁₂ ≠ f₀₂ := by decide
@[simp] theorem f₁₂_ne_f₀₃ : f₁₂ ≠ f₀₃ := by decide
@[simp] theorem f₁₂_ne_f₁₁ : f₁₂ ≠ f₁₁ := by decide
@[simp] theorem f₁₃_ne_f₀₀ : f₁₃ ≠ f₀₀ := by decide
@[simp] theorem f₁₃_ne_f₀₁ : f₁₃ ≠ f₀₁ := by decide
@[simp] theorem f₁₃_ne_f₀₂ : f₁₃ ≠ f₀₂ := by decide
@[simp] theorem f₁₃_ne_f₀₃ : f₁₃ ≠ f₀₃ := by decide
@[simp] theorem f₁₃_ne_f₁₁ : f₁₃ ≠ f₁₁ := by decide
@[simp] theorem f₁₃_ne_f₁₂ : f₁₃ ≠ f₁₂ := by decide
@[simp] theorem f₂₂_ne_f₀₀ : f₂₂ ≠ f₀₀ := by decide
@[simp] theorem f₂₂_ne_f₀₁ : f₂₂ ≠ f₀₁ := by decide
@[simp] theorem f₂₂_ne_f₀₂ : f₂₂ ≠ f₀₂ := by decide
@[simp] theorem f₂₂_ne_f₀₃ : f₂₂ ≠ f₀₃ := by decide
@[simp] theorem f₂₂_ne_f₁₁ : f₂₂ ≠ f₁₁ := by decide
@[simp] theorem f₂₂_ne_f₁₂ : f₂₂ ≠ f₁₂ := by decide
@[simp] theorem f₂₂_ne_f₁₃ : f₂₂ ≠ f₁₃ := by decide
@[simp] theorem f₂₃_ne_f₀₀ : f₂₃ ≠ f₀₀ := by decide
@[simp] theorem f₂₃_ne_f₀₁ : f₂₃ ≠ f₀₁ := by decide
@[simp] theorem f₂₃_ne_f₀₂ : f₂₃ ≠ f₀₂ := by decide
@[simp] theorem f₂₃_ne_f₀₃ : f₂₃ ≠ f₀₃ := by decide
@[simp] theorem f₂₃_ne_f₁₁ : f₂₃ ≠ f₁₁ := by decide
@[simp] theorem f₂₃_ne_f₁₂ : f₂₃ ≠ f₁₂ := by decide
@[simp] theorem f₂₃_ne_f₁₃ : f₂₃ ≠ f₁₃ := by decide
@[simp] theorem f₂₃_ne_f₂₂ : f₂₃ ≠ f₂₂ := by decide
@[simp] theorem f₃₃_ne_f₀₀ : f₃₃ ≠ f₀₀ := by decide
@[simp] theorem f₃₃_ne_f₀₁ : f₃₃ ≠ f₀₁ := by decide
@[simp] theorem f₃₃_ne_f₀₂ : f₃₃ ≠ f₀₂ := by decide
@[simp] theorem f₃₃_ne_f₀₃ : f₃₃ ≠ f₀₃ := by decide
@[simp] theorem f₃₃_ne_f₁₁ : f₃₃ ≠ f₁₁ := by decide
@[simp] theorem f₃₃_ne_f₁₂ : f₃₃ ≠ f₁₂ := by decide
@[simp] theorem f₃₃_ne_f₁₃ : f₃₃ ≠ f₁₃ := by decide
@[simp] theorem f₃₃_ne_f₂₂ : f₃₃ ≠ f₂₂ := by decide
@[simp] theorem f₃₃_ne_f₂₃ : f₃₃ ≠ f₂₃ := by decide

@[simp] theorem v5_f₀₀ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₀₀ = (d 0 1 + d 0 4 - d 1 4) / 2 := by simp [v5]

@[simp] theorem v5_f₀₁ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₀₁ = (d 4 1 - d 0 1 - d 4 2 + d 0 2) / 2 := by simp [v5]

@[simp] theorem v5_f₀₂ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₀₂ = (d 4 2 - d 0 2 - d 4 3 + d 0 3) / 2 := by simp [v5]

@[simp] theorem v5_f₀₃ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₀₃ = (d 4 3 - d 0 3 - d 4 4 + d 0 4) / 2 := by simp [v5]

@[simp] theorem v5_f₁₁ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₁₁ = (d 0 1 - d 1 1 - d 0 2 + d 1 2) / 2 := by simp [v5]

@[simp] theorem v5_f₁₂ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₁₂ = (d 0 2 - d 1 2 - d 0 3 + d 1 3) / 2 := by simp [v5]

@[simp] theorem v5_f₁₃ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₁₃ = (d 0 3 - d 1 3 - d 0 4 + d 1 4) / 2 := by simp [v5]

@[simp] theorem v5_f₂₂ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₂₂ = (d 1 2 - d 2 2 - d 1 3 + d 2 3) / 2 := by simp [v5]

@[simp] theorem v5_f₂₃ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₂₃ = (d 1 3 - d 2 3 - d 1 4 + d 2 4) / 2 := by simp [v5]

@[simp] theorem v5_f₃₃ (d : Fin 5 → Fin 5 → ℝ) :
    v5 d f₃₃ = (d 2 3 - d 3 3 - d 2 4 + d 3 4) / 2 := by simp [v5]

theorem phyleticDist_ten (w : Split (Fin 5) → ℝ) (x y : Fin 5) :
    phyleticDist G5 w x y = (((((((((w f₀₀ * sepInd f₀₀ x y + w f₀₁ * sepInd f₀₁ x y + w f₀₂ * sepInd f₀₂ x y + w f₀₃ * sepInd f₀₃ x y + w f₁₁ * sepInd f₁₁ x y + w f₁₂ * sepInd f₁₂ x y + w f₁₃ * sepInd f₁₃ x y + w f₂₂ * sepInd f₂₂ x y + w f₂₃ * sepInd f₂₃ x y + w f₃₃ * sepInd f₃₃ x y))))))))) := by
  simp only [phyleticDist, sepInd, G5]
  rw [    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₀₁_ne_f₀₀).symm, (f₀₂_ne_f₀₀).symm, (f₀₃_ne_f₀₀).symm, (f₁₁_ne_f₀₀).symm, (f₁₂_ne_f₀₀).symm, (f₁₃_ne_f₀₀).symm, (f₂₂_ne_f₀₀).symm, (f₂₃_ne_f₀₀).symm, (f₃₃_ne_f₀₀).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₀₂_ne_f₀₁).symm, (f₀₃_ne_f₀₁).symm, (f₁₁_ne_f₀₁).symm, (f₁₂_ne_f₀₁).symm, (f₁₃_ne_f₀₁).symm, (f₂₂_ne_f₀₁).symm, (f₂₃_ne_f₀₁).symm, (f₃₃_ne_f₀₁).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₀₃_ne_f₀₂).symm, (f₁₁_ne_f₀₂).symm, (f₁₂_ne_f₀₂).symm, (f₁₃_ne_f₀₂).symm, (f₂₂_ne_f₀₂).symm, (f₂₃_ne_f₀₂).symm, (f₃₃_ne_f₀₂).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₁₁_ne_f₀₃).symm, (f₁₂_ne_f₀₃).symm, (f₁₃_ne_f₀₃).symm, (f₂₂_ne_f₀₃).symm, (f₂₃_ne_f₀₃).symm, (f₃₃_ne_f₀₃).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₁₂_ne_f₁₁).symm, (f₁₃_ne_f₁₁).symm, (f₂₂_ne_f₁₁).symm, (f₂₃_ne_f₁₁).symm, (f₃₃_ne_f₁₁).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₁₃_ne_f₁₂).symm, (f₂₂_ne_f₁₂).symm, (f₂₃_ne_f₁₂).symm, (f₃₃_ne_f₁₂).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₂₂_ne_f₁₃).symm, (f₂₃_ne_f₁₃).symm, (f₃₃_ne_f₁₃).symm]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, (f₂₃_ne_f₂₂).symm, (f₃₃_ne_f₂₂).symm]),
    Finset.sum_insert (by simp [Finset.mem_singleton, (f₃₃_ne_f₂₃).symm]),
    Finset.sum_singleton]
  try ring

/-- ★★★ **`n = 5` 的恒等**（干净上下文：只带具体的对称/对角等式）。 -/
theorem v5_realizes (d : Fin 5 → Fin 5 → ℝ) (h01 : d 0 1 = d 1 0) (h02 : d 0 2 = d 2 0) (h03 : d 0 3 = d 3 0) (h04 : d 0 4 = d 4 0) (h12 : d 1 2 = d 2 1) (h13 : d 1 3 = d 3 1) (h14 : d 1 4 = d 4 1) (h23 : d 2 3 = d 3 2) (h24 : d 2 4 = d 4 2) (h34 : d 3 4 = d 4 3)
    (hd1 : d 1 1 = 0) (hd2 : d 2 2 = 0) (hd3 : d 3 3 = 0) (hd4 : d 4 4 = 0) :
    ∀ x y : Fin 5, x ≠ y → phyleticDist G5 (v5 d) x y = d x y := by
  intro x y hxy
  rw [phyleticDist_ten (v5 d) x y]
  simp only [v5_f₀₀, v5_f₀₁, v5_f₀₂, v5_f₀₃, v5_f₁₁, v5_f₁₂, v5_f₁₃, v5_f₂₂, v5_f₂₃, v5_f₃₃]
  fin_cases x <;> fin_cases y <;>
    simp_all [sepInd, f₀₀, f₀₁, f₀₂, f₀₃, f₁₁, f₁₂, f₁₃, f₂₂, f₂₃, f₃₃] <;>
    linarith [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, hd1, hd2, hd3, hd4]

/-- ★★★ **`n = 5` 实例（修复形态）**：环形（Kalmanson）+ 对称 + 零对角 `d` 由**非负**加权
环形族实现；权重是 §7 逆矩阵的行（`v5`），非负性用一般 `n` 的 `kalmanson_*` 引理。 -/
theorem circularRealization_fin5 (d : Fin 5 → Fin 5 → ℝ) (hdiag : ∀ x, d x x = 0)
    (hsym : ∀ x y, d x y = d y x) (hd : IsCircularDist (Equiv.refl (Fin 5)) d) :
    ∃ (F : Finset (Split (Fin 5))) (w : Split (Fin 5) → ℝ),
      Circular (↑F : Set (Split (Fin 5))) ∧ (∀ s ∈ F, 0 ≤ w s) ∧
        ∀ x y : Fin 5, x ≠ y → phyleticDist F w x y = d x y := by
  refine ⟨G5, v5 d, ?_, ?_, ?_⟩
  · refine ⟨5, Equiv.refl (Fin 5), fun s hs => ?_⟩
    have hs' : s ∈ G5 := hs
    simp only [G5, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl isCyclicArc_f₀₀
    · exact Or.inl isCyclicArc_f₀₁
    · exact Or.inl isCyclicArc_f₀₂
    · exact Or.inl isCyclicArc_f₀₃
    · exact Or.inl isCyclicArc_f₁₁
    · exact Or.inl isCyclicArc_f₁₂
    · exact Or.inl isCyclicArc_f₁₃
    · exact Or.inl isCyclicArc_f₂₂
    · exact Or.inl isCyclicArc_f₂₃
    · exact Or.inl isCyclicArc_f₃₃
  · intro s hs
    have hs' : s ∈ G5 := hs
    simp only [G5, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [v5_f₀₀]
      have h := kalmanson_triangle (Equiv.refl (Fin 5)) d hdiag hd 0 1 4 (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₀₁]
      have h := kalmanson_H (Equiv.refl (Fin 5)) d hsym hd 0 1 2 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₀₂]
      have h := kalmanson_H (Equiv.refl (Fin 5)) d hsym hd 0 2 3 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₀₃]
      have h := kalmanson_H (Equiv.refl (Fin 5)) d hsym hd 0 3 4 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₁₁]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 0 1 1 2 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₁₂]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 0 1 2 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₁₃]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 0 1 3 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₂₂]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 1 2 2 3 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₂₃]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 1 2 3 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
    · rw [v5_f₃₃]
      have h := kalmanson_D (Equiv.refl (Fin 5)) d hd 2 3 3 4 (by decide) (by decide) (by decide)
      simp only [Equiv.refl_symm, Equiv.refl_apply] at h
      linarith
  · exact v5_realizes d (hsym 0 1) (hsym 0 2) (hsym 0 3) (hsym 0 4) (hsym 1 2) (hsym 1 3) (hsym 1 4) (hsym 2 3) (hsym 2 4) (hsym 3 4) (hdiag 1) (hdiag 2) (hdiag 3) (hdiag 4)

/-! ### 9.5 ★B：`n = 3` 的**具体** `d` 与解出的 `w` -/

/-- ★B 具体距离：非对角 `1`、对角 `0`（`Fin 3`）。 -/
def d3one : Fin 3 → Fin 3 → ℝ := fun x y => if x = y then 0 else 1

theorem d3one_symm (x y : Fin 3) : d3one x y = d3one y x := by
  unfold d3one
  fin_cases x <;> fin_cases y <;> norm_num

theorem d3one_diag (x : Fin 3) : d3one x x = 0 := by
  unfold d3one; simp

/-- ★B **具体实例**：`d3one` 解出的三条权重都是 `1/2`，且族 `G₃` 的系统发生距离**恰**等于 `d3one`。 -/
example : v₃ d3one c₀ = 1 / 2 ∧ v₃ d3one c₁ = 1 / 2 ∧ v₃ d3one c₂ = 1 / 2 ∧
    ∀ x y : Fin 3, x ≠ y → phyleticDist G₃ (v₃ d3one) x y = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v₃_c₀]; norm_num [d3one]
  · rw [v₃_c₁]; norm_num [d3one]
  · rw [v₃_c₂]; norm_num [d3one]
  · intro x y hxy
    rw [v₃_realizes d3one (d3one_symm 0 1) (d3one_symm 0 2) (d3one_symm 1 2)
      (d3one_diag 1) (d3one_diag 2) x y hxy]
    unfold d3one
    simp [hxy]


/-- ✅ **部分收口（W12g-4）**：`circularWeights_realization_gap` 在 `n = 3, 4, 5` 上**已证**
（三个实例定理的类型与 `circularWeights_realization_gap n` **逐字相同**）。一般 `n` 仍是该 `def` 的内容。 -/
theorem circularWeights_realization_gap_fin_le_five :
    circularWeights_realization_gap 3 ∧ circularWeights_realization_gap 4 ∧
      circularWeights_realization_gap 5 :=
  ⟨circularRealization_fin3, circularRealization_fin4, circularRealization_fin5⟩

end CircularRealization

/-! ## 10. 一般 `n` 的恒等（W12g-5）：线性代数路线 (b) 的**维数那一半**

路线 (b)（派单给定的骨架）：`Arc n` = 代表弧族 `{ (i,j) | i ≤ j ≤ n−2 }`（`binom n 2` 个，
每个环形 split 恰一个代表）；`Pair n` = 无序点对 `{ x < y }`（也 `binom n 2` 个）。
`Alm w p := ∑ a, w a * [弧 a 分离 p]`（`phyleticDist` 的线性版）、`Mlm` = §7 逆矩阵的三行泛函
⇒ `Mlm ∘ Alm = id`（§7 隔离引理 + 求和塌缩）⇒ `Alm` 单射；再用**维数相等** +
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` 得满射 ⇒ 恒等。

本节先落**维数那一半**（`arcPairEquiv` + 两个 `Fintype.card`/`finrank` 推论）；
`Alm`/`Mlm` 的定义与 `Mlm ∘ Alm = id` 见 `circularWeights_realization_gap` 的说明。 -/

section Dimension

/-- 代表弧 `[i,j]`：`i ≤ j` 且**补侧非空**（`j+1 < n` ⟺ `j ≤ n−2`，`n ≥ 2` 时）。
⚠️ 用 `j+1 < n` 而不是 `j ≤ n−2`：后者在 `n = 1` 时会漏进退化的「整圆弧」。 -/
abbrev Arc (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2 ∧ p.2.val + 1 < n}

/-- 无序点对（`x < y`）。 -/
abbrev Pair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-- ★ **代表弧 ↔ 无序点对**：`[i,j] ↦ (i, j+1)`（逆：`(a,b) ↦ (a, b−1)`）。 -/
noncomputable def arcPairEquiv (n : ℕ) : Arc n ≃ Pair n where
  toFun a :=
    ⟨(a.1.1, ⟨a.1.2.val + 1, a.2.2⟩),
      by
        have h1 : a.1.1.val ≤ a.1.2.val := Fin.le_iff_val_le_val.mp a.2.1
        exact Fin.lt_def.mpr (Nat.lt_succ_of_le h1)⟩
  invFun p :=
    ⟨(p.1.1, ⟨p.1.2.val - 1, by
        have h : p.1.1.val < p.1.2.val := p.2
        have h2 : p.1.2.val < n := p.1.2.isLt
        omega⟩),
      by
        have h : p.1.1.val < p.1.2.val := p.2
        refine ⟨Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt h), ?_⟩
        show p.1.2.val - 1 + 1 < n
        omega⟩
  left_inv a := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Fin.ext (show a.1.2.val + 1 - 1 = a.1.2.val from by omega)
  right_inv p := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Fin.ext (show p.1.2.val - 1 + 1 = p.1.2.val from by
      have h : p.1.1.val < p.1.2.val := p.2
      omega)

/-- ★ **维数相等**：`|Arc n| = |Pair n| = binom n 2`（两者基数相等，这是 (b) 的关键一步）。 -/
theorem card_arc_eq_card_pair (n : ℕ) : Fintype.card (Arc n) = Fintype.card (Pair n) :=
  Fintype.card_congr (arcPairEquiv n)

/-- ★ **`ℝ`-维数相等**：`dim (Arc n → ℝ) = dim (Pair n → ℝ)`（用 Mathlib 的
`Module.finrank_fintype_fun_eq_card`）。 -/
theorem finrank_arc_eq_finrank_pair (n : ℕ) :
    Module.finrank ℝ (Arc n → ℝ) = Module.finrank ℝ (Pair n → ℝ) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    card_arc_eq_card_pair]

end Dimension

/-! ## 11. 一般 `n` 的恒等（W12g-6）：`Alm` / `Mlm` 的 `LinearMap` 层

按 §10 的路线 (b)：

* `Alm`（`phyleticDist` 的线性版）：`w ↦ (p ↦ ∑ a, w a * [弧 a 分离 p])`；
* `Mlm`（§7 逆矩阵的三行泛函 L / H / D，带 `1/2`）：`δ ↦` 逐弧解出权重。

⚠️ 两个实现要点：(i) `Mlm` 的分支用 **`dite`**（分支内需要 `i−1 < j`、`0 < j`、`j+1 < n` 等算术前提）；
(ii) 每支的四（三）个位置先在函数体里 **`let` 绑定**，使三处实例化共享同一批项 ——
否则 `by omega` 的证明项会各自生成，`ring` 无法把它们认作同一个原子。 -/

section WeightAlgebra

/-- ★ 弧 → split：取弧本身作 `sideA`（补侧非空由 `Arc` 的护栏 `j+1 < n` 保证）。 -/
noncomputable def arcSplit {n : ℕ} (a : Arc n) : Split (Fin n) :=
  ofSideA (cycArc (Equiv.refl (Fin n)) a.1.1 a.1.2)
    (by
      have h : a.1.1 ≤ a.1.2 := a.2.1
      exact ⟨a.1.1, by simp [mem_cycArc, Finset.mem_Icc, h]⟩)
    (by
      refine ⟨⟨a.1.2.val + 1, a.2.2⟩, ?_⟩
      have hne : ¬ (⟨a.1.2.val + 1, a.2.2⟩ : Fin n) ≤ a.1.2 := fun hle =>
        Nat.not_succ_le_self a.1.2.val (Fin.le_iff_val_le_val.mp hle)
      rw [Finset.mem_compl]
      intro hcon
      simp only [mem_cycArc, Finset.mem_Icc, Equiv.refl_apply] at hcon
      exact hne hcon.2)

@[simp] theorem arcSplit_sideA {n : ℕ} (a : Arc n) :
    (arcSplit a).sideA = cycArc (Equiv.refl (Fin n)) a.1.1 a.1.2 := by
  unfold arcSplit
  exact Split.ofSideA_sideA _ _ _

/-- ★ 位置 `x, y` 的点对值（按大小取；`x = y` 取 `0`）。 -/
noncomputable def pairVal {n : ℕ} (δ : Pair n → ℝ) (x y : Fin n) : ℝ :=
  if h : x < y then δ ⟨(x, y), h⟩ else if h' : y < x then δ ⟨(y, x), h'⟩ else 0

theorem pairVal_add {n : ℕ} (δ δ' : Pair n → ℝ) (x y : Fin n) :
    pairVal (δ + δ') x y = pairVal δ x y + pairVal δ' x y := by
  unfold pairVal
  by_cases h : x < y
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h]
    simp only [Pi.add_apply]
  · by_cases h' : y < x
    · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h,
        dite_eq_left h', dite_eq_left h', dite_eq_left h']
      simp only [Pi.add_apply]
    · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h,
        dite_eq_right h', dite_eq_right h', dite_eq_right h']
      norm_num

theorem pairVal_smul {n : ℕ} (c : ℝ) (δ : Pair n → ℝ) (x y : Fin n) :
    pairVal (c • δ) x y = c * pairVal δ x y := by
  unfold pairVal
  by_cases h : x < y
  · rw [dite_eq_left h, dite_eq_left h]
    simp only [Pi.smul_apply, smul_eq_mul]
  · by_cases h' : y < x
    · rw [dite_eq_right h, dite_eq_left h', dite_eq_right h, dite_eq_left h']
      simp only [Pi.smul_apply, smul_eq_mul]
    · rw [dite_eq_right h, dite_eq_right h', dite_eq_right h, dite_eq_right h']
      ring

/-- ★ `Alm` 的函数部分：弧权重 → 点对距离（`phyleticDist` 的线性版）。 -/
noncomputable def AlmFun (n : ℕ) (w : Arc n → ℝ) : Pair n → ℝ :=
  fun p => ∑ a : Arc n, w a * sepInd (arcSplit a) p.1.1 p.1.2

theorem AlmFun_add (n : ℕ) (w w' : Arc n → ℝ) :
    AlmFun n (w + w') = AlmFun n w + AlmFun n w' := by
  funext p
  simp only [AlmFun, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem AlmFun_smul (n : ℕ) (c : ℝ) (w : Arc n → ℝ) :
    AlmFun n (c • w) = c • AlmFun n w := by
  funext p
  simp only [AlmFun, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- ★ **`Alm`**：弧权重 → 点对距离（线性映射）。 -/
noncomputable def Alm (n : ℕ) : (Arc n → ℝ) →ₗ[ℝ] (Pair n → ℝ) where
  toFun := AlmFun n
  map_add' := AlmFun_add n
  map_smul' := AlmFun_smul n

/-- ★ `Mlm` 的函数部分：§7 逆矩阵的三行泛函（L / H / D），带 `1/2`。

⚠️ 分支用 `dite`；三支的位置先 `let` 绑定（见本节开头说明）。 -/
noncomputable def MlmFun (n : ℕ) (δ : Pair n → ℝ) : Arc n → ℝ := fun a =>
  let i := a.1.1
  let j := a.1.2
  let z : Fin n := ⟨0, by have h := a.2.2; omega⟩
  let o : Fin n := ⟨1, by have h := a.2.2; omega⟩
  let L : Fin n := ⟨n - 1, by have h := a.2.2; omega⟩
  let j1 : Fin n := ⟨j.val + 1, a.2.2⟩
  let i0 : Fin n := ⟨i.val - 1, by have h := i.isLt; omega⟩
  (1 / 2) * (if h0 : i.val = 0 ∧ j.val = 0 then
      pairVal δ z o + pairVal δ z L - pairVal δ o L
    else if h1 : i.val = 0 then
      pairVal δ L j + pairVal δ z j1 - pairVal δ z j - pairVal δ L j1
    else
      pairVal δ i0 j + pairVal δ i j1 - pairVal δ i j - pairVal δ i0 j1)

theorem MlmFun_add (n : ℕ) (δ δ' : Pair n → ℝ) :
    MlmFun n (δ + δ') = MlmFun n δ + MlmFun n δ' := by
  funext a
  simp only [MlmFun, Pi.add_apply]
  by_cases h0 : a.1.1.val = 0 ∧ a.1.2.val = 0
  · rw [dite_eq_left h0, dite_eq_left h0, dite_eq_left h0]
    simp only [pairVal_add]
    ring
  · rw [dite_eq_right h0, dite_eq_right h0, dite_eq_right h0]
    by_cases h1 : a.1.1.val = 0
    · rw [dite_eq_left h1, dite_eq_left h1, dite_eq_left h1]
      simp only [pairVal_add]
      ring
    · rw [dite_eq_right h1, dite_eq_right h1, dite_eq_right h1]
      simp only [pairVal_add]
      ring

theorem MlmFun_smul (n : ℕ) (c : ℝ) (δ : Pair n → ℝ) :
    MlmFun n (c • δ) = c • MlmFun n δ := by
  funext a
  simp only [MlmFun, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : a.1.1.val = 0 ∧ a.1.2.val = 0
  · rw [dite_eq_left h0, dite_eq_left h0]
    simp only [pairVal_smul]
    ring
  · rw [dite_eq_right h0, dite_eq_right h0]
    by_cases h1 : a.1.1.val = 0
    · rw [dite_eq_left h1, dite_eq_left h1]
      simp only [pairVal_smul]
      ring
    · rw [dite_eq_right h1, dite_eq_right h1]
      simp only [pairVal_smul]
      ring

/-- ★ **`Mlm`**：点对函数 → 弧权重（§7 逆矩阵的三行泛函，线性映射）。 -/
noncomputable def Mlm (n : ℕ) : (Pair n → ℝ) →ₗ[ℝ] (Arc n → ℝ) where
  toFun := MlmFun n
  map_add' := MlmFun_add n
  map_smul' := MlmFun_smul n

end WeightAlgebra

end NeighborNet
