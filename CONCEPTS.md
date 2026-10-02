# phylogeny 概念清单 · 定义方案与先例

> **用途**：为「phylogeny 经典算法证明库」确定**需要定义哪些概念**、每个概念的**候选定义方案与优缺点**。
> **方法**：先翻经典教材/论文取先例定义，再给形式化候选。
> **状态**：2026-10-02 重起。本文是新的起点；上一轮 `DESIGN.md` 里的暂定决策（树底层、split 形态）在本文中作为**候选之一**重新列出，可推翻。

---

## 0. 文献调研结论（先说最重要的一条）

**形式化先例：初步检索未发现任何公开的 phylogenetics 形式化库。**

| 检查对象 | 结果 |
|---|---|
| Lean / Mathlib | 无 phylogenetics / tree metric / split / quartet（只有通用 `SimpleGraph`） |
| Lean 生态（Std, CSLib, SciLean, PhysLib…） | 无 |
| Isabelle / AFP（680+ 条目） | 未检索到 phylogenetics 条目 |
| Rocq/Coq（Mathematical Components 等） | 未检索到 |

**最接近的先行工作**：Kelk, van Iersel, Meuwese, Forte —— *Computational support for case-heavy proofs in mathematical phylogenetics*（arXiv:2512.16691）。他们不是做形式化证明，而是**用计算机枚举+验证**来扛住 phylogenetics 里爆炸式的 case analysis（以 Maximum Agreement Forest 为例），并明确说这类证明「已接近手工可写的极限」。**动机与我们完全一致** —— 这是立项动机的最好背书。

---

## 1. 概念清单（按依赖分层）

标 **★** = 核心必备；**○** = 后续需要；**·** = 可选/远期。

### L0 基础实体
| # | 概念 | 级别 |
|---|---|---|
| 1 | 分类单元集 `X`（有限、非空） | ★ |
| 2 | 相异度 / 距离矩阵 `δ : X → X → ℝ` | ★ |
| 3 | 实数权重 `ℝ≥0` | ★ |

### L1 树与拓扑
| # | 概念 | 级别 |
|---|---|---|
| 4 | 图论树（连通 + 无环） | ★ |
| 5 | **X-树 / 无根系统发生树**（叶集 = X，无度 2 顶点） | ★ |
| 6 | **有根系统发生树**（根 + 有向、叶 out-degree 0） | ○ |
| 7 | binary / fully-resolved | ★ |
| 8 | 边权 `w : E → ℝ≥0`；proper 边权 | ★ |
| 9 | 加权树 `(T, w)`；**三层结构：Cladogram（纯拓扑）/ Phylogram（+ 可加边权）/ AnnotatedTree（+ 标注，待定）** | ★ |
| 9b | **chronogram / time tree / ultrametric**（= Phylogram + 所有叶到根等距） | ○ |
| 10 | 路径 / 加权路径长 | ★ |
| 11 | 诱导距离 `d_(T,w)` | ★ |
| 12 | **restriction `T\|Y`**（诱导子树 + 抑制度 2 顶点） | ★ |
| 13 | 树同构 / 等价（保标号同构） | ★ |
| 14 | **cherry（樱桃）** | ★ |
| 15 | caterpillar | · |
| 16 | 叶 / 内部顶点 / 度 | ★ |

### L2 分裂与 quartet
| # | 概念 | 级别 |
|---|---|---|
| 17 | **split `A\|B`**；trivial split | ★ |
| 18 | split system；weighted split system | ★ |
| 19 | **compatible / pairwise compatible** | ★ |
| 19a | **tripartition**（内部节点诱导）/ **quadripartition**（内部边诱导） | ○ |
| 19b | 一般 **`k`-partition**；convex / biconvex character | · |
| 20 | Buneman graph | ○ |
| 21 | **quartet**（四元子树）；quartet split；quartet weight | ★ |
| 21b | **triplet / rooted triple**（`ab\|c`，3 叶 rooted）；**Topology（= 支撑集 + Split）** | ★ |
| 22 | quartet system；quartet 闭包/一致性 | ○ |
| 23 | rooted triple；`T displays ab\|c` | · |
| 24 | cluster / laminar family / hierarchy | ○ |

### L3 度量与判据
| # | 概念 | 级别 |
|---|---|---|
| 25 | **四点条件（4-point condition）** | ★ |
| 26 | 超度量 / 三点条件 | ★ |
| 27 | **tree metric / additive metric**；可加性 | ★ |
| 28 | **Buneman 定理**（四点条件 ⟺ 树度量 ⟺ 相容分裂系统） | ★ |
| 29 | Q-判据 / `ℓ` / `z`（NJ 用） | ★ |
| 30 | Atteson 半径（稳健性） | · |

### L4 树比较与重排
| # | 概念 | 级别 |
|---|---|---|
| 31 | **Robinson–Foulds 距离** | ○ |
| 31b | **加权距离族**：wRF（L1）/ KF·branch score（L2）/ BHV；**加权树 = split 权重向量** | ○ |
| 31c | **branch length 单位**：SU（替换数）/ time / CU（溯祖）/ θ；**可加 vs 标注**的区分 | ★ |
| 32 | **NNI / SPR / TBR / LPR / LLI** 操作与距离 | ○ |
| 33 | 共识树 / majority-rule | · |
| 34 | 树空间（BHV / treespace） | · |

### L5 算法与模型
| # | 概念 | 级别 |
|---|---|---|
| 35 | **Neighbor-Joining** | ★ |
| 36 | **UPGMA / 层次聚类 / dendrogram** | ★ |
| 37 | parsimony / character / Fitch 算法 | ○ |
| 38 | 最大似然 / 替换模型 / Felsenstein 剪枝 | · |
| 39 | gene tree / species tree / ILS / 溯祖 | ○ |
| 40 | ASTRAL 等 quartet-based 方法 | · |

---

## 2. 先例定义（谁怎么定义的，原文要点）

### 2.1 树

**Semple & Steel 体系**（转引自 Huber & Steel, *Tree reconstruction from triplet cover distances*, 2013）：
> "An **X−tree** `T=(V,E)` is a graph theoretical tree whose **leaf set is X** and which **does not have any vertices of degree 2**. We call an X−tree **fully-resolved** if every interior vertex of T has degree three."

**有根 / 无根分别定义**（Huber & Steel；亦见 *Phylogenetic Flexibility*, Bull. Math. Biol. 2018）：
> "a **rooted phylogenetic tree** T is a rooted tree having a set L(T) of labelled leaves (vertices of out-degree 0) and for which every non-leaf vertex is unlabelled and has **out-degree at least 2** … an **unrooted phylogenetic tree** T is an unrooted tree having a set L(T) of labelled leaves (**vertices of degree 1**) and for which every non-leaf vertex is unlabelled and has **degree at least 3**. In case each non-leaf vertex has degree exactly 3, we say that T is **binary**."

**Steel & Székely**（*An improved bound on MAST*）：
> "A **phylogenetic X-tree** is a **binary** tree in which the leaves are labelled bijectively with labels from a set X and internal vertices are unlabelled. Two phylogenetic X-trees are considered the same if there is a **label-preserving graph isomorphism** between them."

**Kelk et al 2025**（边角情形明确）：
> "An unrooted binary phylogenetic tree T on X is an undirected tree whose leaves are bijectively labeled with X and whose other vertices all have degree 3. **Note that the single vertex (|X|=1) and the single edge (|X|=2) are also unrooted binary phylogenetic trees.**"

**Restriction**：
> "For any subset `Y ⊆ X`, we denote by `T|Y` the Y-tree obtained by restricting T to Y (**suppressing resulting degree two vertices**)."

### 2.2 cherry / caterpillar
> "we call two distinct leaves x and y of T a **cherry** of T, denoted by x,y, if the **parent of x is simultaneously the parent of y**."（Huber & Steel 2013）
> "A **cherry** in a (rooted or unrooted) phylogenetic tree is a **pair of leaves that is adjacent to the same vertex**."（Phylogenetic Flexibility 2018）
> "A **caterpillar** tree on X is a binary phylogenetic X-tree for which the number of cherries is at most 1 (rooted) / 2 (unrooted)."

### 2.3 split 与兼容性

**Bandelt & Dress 体系**（转引自 Bastkowski PhD *From Trees to Networks and Back*）：
> "**Definition 2.3.1 (Split)**: A split `S = A|B (= B|A)` is a **bipartition of X into two non-empty subsets** A and B, which can also be called the two sides of the split. The split induced by edge e is denoted S_e. If `|A| = 1` or `|B| = 1`, then the split `A|B` is called **trivial**. In trees, trivial splits correspond to **pendant edges**. A set of splits is called a **split system**."
> "**Definition 2.3.2 (Compatible)**: Two splits S₁ = A₁|B₁ and S₂ = A₂|B₂ are **compatible** if one of the intersections `A₁∩A₂, A₁∩B₂, B₁∩A₂, B₁∩B₂` is **empty**."

**Splits-Equivalence Theorem**：
> "a split system in which every pair of splits is compatible can always be represented by a **necessarily unique X-tree**. Thus **X-trees and compatible split systems on X are in one-to-one correspondence**."

**Neighbor-Net**（Bryant & Moulton，arXiv:math/0702515）：
> "**Definition 1.** A split `S={A,B}` is a **partition of X into two non-empty blocks**. A set of splits is called a **split system**. The **split metric** determined by S is the pseudo-metric δ_S = 0 if {x,y} ⊆ A or ⊆ B, else 1."
> "**Definition 2.** A split system 𝒮 is **pairwise compatible** if for every pair of distinct splits S₁={A,B}, S₂={A′,B′}, at least one of `A∩A′, A∩B′, B∩A′, B∩B′` is empty."
> "There is a canonical median graph associated with a split system called the **Buneman graph**. The Buneman graph of a pairwise compatible split system is a **tree**."

**边权的术语**：
> "we call a map `w:E→ℝ` that assigns a weight `≥0` to every edge an **edge-weighting** … an edge-weighting that assigns non-zero weight to every edge of T that is not incident with a leaf of T is **proper**."

### 2.4 quartet

**Bastkowski（Bandelt–Dress 体系）**：
> "**Definition 2.3.3 (Quartet tree)**: Given a phylogenetic tree T on X and any set X′ ⊆ X of four taxa, the **smallest subtree T(X′)** of T that connects the four given taxa is called the quartet tree for the given taxa."
> "In the case where T(X′) has precisely two distinct vertices u and v of degree three, the path P connecting u and v in T(X′) separates two of the four given taxa, say a and a′, from the remaining two, say b and b′. We denote this by `aa′|bb′` and refer to it as the **quartet** induced by T … The **weight κ(q)** of a quartet q is the total length of the edges on the path P."

**Steel & Székely**（把 quartet 直接定义为划分）：
> "If |Y| = 4, the induced binary subtree is often identified with an **unordered partition of Y into two two-element sets**, obtained by removing the (unique) internal edge of T|Y. This partition is known as **quartet split**."

**Gambette 课程讲义的 quartet 闭包性质**：
> "Quartets: for any leaf e, `ab|cd ∈ Q ⇒ ab|ce ∈ Q` or `ae|cd ∈ Q`"（即 quartet 系统必须满足的闭包/一致性规则）

### 2.5 度量与判据

**dissimilarity map**（Neighbor-Net）：
> "A **dissimilarity map** on X is a function `δ : X×X → ℝ` that satisfies `δ(i,j) = δ(j,i) ≥ 0` and `δ(i,i) = 0`."

**四点条件**（Bastkowski，两版等价写法都给了）：
> "**Definition 2.3.4 (4-point condition)**: D is a distance function on X. The 4-point condition is fulfilled for D if `D(w,x) + D(y,z) ≤ max{ D(w,y)+D(x,z), D(w,z)+D(x,y) }` for all w,x,y,z ∈ X."
> （Bryant & Moulton 的等价写法）"two of the three terms are equal and greater than the third: `δ(i,j)+δ(k,l), δ(i,k)+δ(j,l), δ(i,l)+δ(j,k)`."

**tree metric**：
> "metrics satisfying the four point condition are called **tree metrics**. They are precisely the metrics δ for which there is an **edge weighted tree** whose leaves are labeled by X, and for which δ(i,j) is the 'additive distance' between i and j in the tree."

**Buneman–Bandelt–Dress 定理**（Neighbor-Net, Theorem 4）：
> (1) 存在 pairwise compatible split system 𝒮 与 `λ_S ≥ 0` 使 `δ = Σ_{S∈𝒮} λ_S δ_S`
> ⟺ (2) `δ` 是 **metric** 且满足**四点条件**。

**超度量 / 三点条件**（Stanford CS262 notes）：
> "A distance function is **ultrametric** if for any three distances `d_ij ≤ d_ik ≤ d_jk`, it is true that `d_ij ≤ d_ik = d_jk`. This is known as the **three point condition**."

### 2.6 树比较与重排

**Robinson–Foulds 距离**（Owen thesis）：
> "The Robinson-Foulds distance between two trees is the sum of the edges that are in the first tree but not the second, and the edges that are in the second but not the first. In other words, the distance is the **cardinality of the symmetric difference between the edge-sets**."（也叫 bipartition 集的对称差；binary 树直径 = 2(T−3)）

**NNI / SPR / TBR / LPR / LLI**（Atlantis Press 论文，定义最规范）：
> "**Nearest Neighbour Interchange (NNI)** means swapping two subtrees that are incident to the same internal edge."
> "**SPR**: Delete an edge `e=(v,w)` of T, get a new vertex `v′` by subdividing an edge in the component of T that does not contain v, add a new edge between v and v′, and finally **suppress all resulting degree-two vertices**."
> "**LPR**: a special case of SPR in which e is a pendant edge."
> "**TBR**: Delete an edge from T, subdivide an edge in **each** component of T, connect the two new vertices with an edge, and finally suppress all resulting degree-two vertices."
> "**LLI**: exchanges the labels of two leaves; does not change the topology."
> 距离定义：SPR 距离 = 把一棵变成另一棵所需的最少 SPR 次数；NNI 同理。

### 2.7 算法与模型

**NJ**（Weller 2023；Saitou–Nei 1987 / Studier–Keppler 1988）：
> `q(u,v) := (n−2)·d(u,v) − Σ_x d(u,x) − Σ_x d(v,x)`，选 q 最小的一对合并。

**UPGMA**：
> "At each step, the nearest two clusters are combined… The distance between any two clusters A and B is the **average of all distances** d(x,y) between pairs x ∈ A, y ∈ B." 产生 **rooted dendrogram**，需**分子钟**假设（等价于超度量）。

**gene tree vs species tree**：
> "A **gene tree** represents the evolutionary history of a particular gene or genomic region, while a **species tree** represents the evolutionary history of the species that contain those genes. Due to **incomplete lineage sorting (ILS)**, horizontal gene transfer, gene duplication and loss, a gene tree may differ from the species tree."

**cluster / laminar**（Gambette 讲义）：
> "one **cluster** of T = the set of leaves below one vertex of T"; clusters form a "**laminar family**, i.e., it contains no overlapping sets".

---

## 3. 关键形式化岔路（方案 + 优缺点）

> 这一节是本文的重点：数学定义各家一致，**分歧全在怎么编码**。

### 3.1 树的载体

先例都是「图论树 + 叶标号 + 边权」。形式化有三条路：

| 方案 | 内容 | 优点 | 缺点 |
|---|---|---|---|
| **A. 纯 `SimpleGraph`** | `G : SimpleGraph V` + `G.IsTree`；叶由度数定义 | 白蹭 `Walk`/`IsTree`/`Subgraph`/`Matching`/`Matroid` 全套 | `dist` 是 ℕ 无权；**taxon 标签无处安放**（要么 `V = X`，要么手动建立双射） |
| **B. 自定义 weight tree** | 自己的 `V/E/leaf/w/pathSum` 结构 | 完全贴合 phylogeny；taxon 标签天然 | 图论引理全部自证，Mathlib 一点用不上 |
| **C. 接口包一层** ✅ **已定** | 对外 phylogeny API，内部字段 `SimpleGraph V` + `w : Sym2 V → ℝ` + `leaf : X ↪ V` | 两头好处：拓扑白蹭、接口贴合、**可换底层** | 要写一层包装与转换引理；`SimpleGraph` 不许自环/重边（对树无影响） |

**待确认**：加权距离怎么定义？⚠️ 关键坑：`SimpleGraph.dist : V → V → ℕ` 是**无权 BFS**，加权路径长必须另起（沿 `Walk` 求和，或直接定义为「路径上边权之和」）。

#### ✅ 已定（2026-10-02，老师拍板）：方案 C —— 接口包一层

> 老师原话：**「包一层，蹭好处，也保留改底层的空间」**

**蹭到了什么**：`SimpleGraph` 的 `Walk`（含分解 / 子游走 / 映射 / 遍历）、`IsTree`、`IsAcyclic`、`Subgraph`、`Connected` / `ConnectedComponent`、`Matching`、`Matroid`（graphic matroid）、`DegreeSum`、`DeleteEdges` 等全部可用。

**「保留改底层空间」= 四条接口纪律**（这是方案 C 的**约束条款**，不是愿望）：

1. **对外类型签名里不出现 `SimpleGraph`**。上层引理只谈 `PhyloTree` / 叶 / split / quartet 这些抽象名词，不谈 `SimpleGraph V`、`Walk`、甚至不直接谈 `V`。
2. **底层只经「一个投影」进入**。内部字段 `toSimpleGraph : SimpleGraph V`（连同 `w`、`leaf`）；所有图论调用都走这个投影。将来换底层（如整体换成自定义结构）只需改它一处。
3. **接口以「字段 / 引理名」固化，不靠定义展开**。例如「叶 ⟺ 度 1」「两点间路径唯一」「删边把叶集二分」——都作为 `PhyloTree` 的字段或独立引理**命名**陈述；上层只引用名字，不引用其证明内部用了什么。
4. **加权距离不暴露 `Walk`**。对外只给 `dist : V → V → ℝ`；内部靠 `Walk` 求和还是别的方式，属实现细节。

→ 结果：若将来发现「沿 `Walk` 求和」不好使（`SimpleGraph.dist : V→V→ℕ` 无权这个坑是已知隐患），可以整体替换底层而**不动上层**。

**已知代价**：需写一层包装与转换引理；`SimpleGraph` 不允许自环 / 重边（对树无影响）；加权距离必须自建。

### 3.2 「叶」怎么定义（✅ 已定方案 C）

| 方案 | 优点 | 缺点 |
|---|---|---|
| **A. 嵌入 `leaf : X ↪ V` 为主**，`isLeaf := ∃ x, leaf x = v`；「叶=度1」作引理/公理 | taxon 标签随身带，phylogeny 语义直接；每个叶天然知道自己是谁 | 「叶集恰好是度 1 顶点」要额外陈述（作为公理或引理） |
| **B. 「度 1 顶点」为主**，再与 X 建立双射 | 与 `SimpleGraph` 既有引理最贴合 | 每个叶要额外携带「是哪个 taxon」；处处要处理双射 |
| **C. 两者并存 + 等价引理** ✅ **已定** | 接口最丰富；两视角零成本互切 | 多写一层（一条双向等价） |

> 先例里两种写法都有：Semple–Steel 用「leaf set is X」（= A），Steel–Székely 用「leaves labelled bijectively with X」（= B 的措辞）。

#### ✅ 已定（2026-10-02，老师拍板）：方案 C —— 两者并存 + 等价引理

> 老师原话：**「都要 + 等价」比较合适**

**形态**：两个视角都进 `PhyloTree`，用一组等价引理当桥梁。

```lean
structure PhyloTree (X : Type*) where
  V : Type
  [Fintype V] [DecidableEq V]
  leaf  : X ↪ V                       -- 视角 A：taxon → 顶点（标签随身）
  graph : SimpleGraph V               -- 视角 B：图论（度数可算）
  isTree : graph.IsTree
  -- 桥梁（等价引理，作为公理字段）
  leaf_iff_degree_one : ∀ v, (∃ x : X, leaf x = v) ↔ graph.degree v = 1
  -- 配套正规化（Semple–Steel 的 X-tree 定义含此条）
  no_degree_two : ∀ v, graph.degree v ≠ 2
```

**拆成两条「使用向」引理**，方便两边随时切换：

```lean
theorem leaf_deg_one  : (∃ x, leaf x = v) → graph.degree v = 1      -- A → B
theorem deg_one_leaf  : graph.degree v = 1 → ∃ x, leaf x = v        -- B → A
theorem card_leaves   : (univ.filter (fun v => graph.degree v = 1)).card = Fintype.card X
```

**为什么这样最合适**：
- 要用 **taxon 标签**时（cherry、quartet、split 全是叶标号的说法）走 `leaf` / `IsLeaf`；
- 要用 **图论引理**时（`DegreeSum`、`Subgraph`、`Matching`、邻域/度数 API）走 `degree = 1`；
- 两条等价引理让两边**随时互切、成本为零**——不复制结构、不建双射。

**两个必须注意的点**：
1. 「像 = 度 1 顶点集」**不是白来的**：`leaf` 是自由给的嵌入，所以这条等价必须作为 `PhyloTree` 的**公理字段**，不是可证引理。与 §3.1 接口纪律 3 一致。
2. 先例的 X-tree 定义还含一条 **「无度 2 顶点」**（Semple & Steel 原文），它与「叶 = 度 1」是配套的正规化条件，**应一并进 `PhyloTree`**；否则 §3.7 的「抑制度 2 顶点」失去依据。

**已知代价**：多一条字段 + 一条双向等价要维护；`SimpleGraph.degree` 需要 `[Fintype (graph.neighborSet v)]`（有限 `V` 下可自动得到，但写法上要留意）。

### 3.3 有根 vs 无根

| 方案 | 优点 | 缺点 |
|---|---|---|
| **A. 只做无根，有根另建一层** ✅ **已定** | 无根是主体（Buneman/split/quartet 都基于无根）；有根 = 无根 + 标记叶/根边 | 两套定义，有根侧引理要重复 |
| **B. 只做有根，无根 = 去掉根** | 有根更贴「进化」直觉；UPGMA/溯祖天然有根 | split/NJ/Buneman 全是无根说法，转写麻烦 |
| **C. 一个结构带 `root : Option V`** | 一套定义 | 处处 `Option` 分支，引理被污染 |

#### ✅ 已定（2026-10-02，老师拍板）：方案 A —— 先做无根，有根另建一层

> 老师原话：**「先做无根，有根另建一层，底层暂时可以定义为有名为 root 的叶子节点的无根树。你觉得怎么样？」**

**判断：方向对、表示法也对，而且是标准技巧 —— 但有三条纪律要加。**

**先例支持**（这不是权宜之计）：

- **Dress (1997)**（转引自 *Clustering systems of phylogenetic networks*, Theory in Biosciences 2023）：cluster 与 split 的对应，原文正是「**X is augmented by an additional outgroup `*`**」，即 `C | (X∖C) ∪ {*}`。
- **Semple & Steel (2003)**：**rooted phylogenetic tree ↔ hierarchy（laminar cluster family）是一一对应**。
- **通用教材/Wikipedia**：rooted tree 的**根是 degree 2 的节点**；"rooted trees can be generated from unrooted ones by **inserting a root**"。
- **计数验证**（arXiv:1203.5835）：`|R(n)| = (2n−3)·|B(n)|`（每条边对应一棵有根树）；而 unrooted binary trees on `X ∪ {*}` 的个数恰为 `(2n−3)!!`，**与 rooted binary trees on `X` 完全相同** → 「无根 + 一个标记叶」与「有根」是**双射**。

**三条纪律**（否则类型污染会扩散）：

1. **标记叶不能塞进 `X`**。类型上用 `X ⊕ Unit`（或 `Option X` 把 `none` 当标记）；真 taxon 是 `Sum.inl x` / `some x`。
2. **「根」是标记叶的唯一邻居（一个顶点）**，不是标记叶本身 —— 所以还要一条投影 `root : V`。
3. **必须区分「真 taxon 叶」与「root 标记叶」**。这正是污染点：按 §3.1 纪律，`X ⊕ Unit` 只能出现在 **rooted ↔ unrooted 的转换引理**里，**不进 rooted 侧引理的签名**。

**一个更长远的选择（供参考，不急定）**：
rooted 层的**抽象接口**建议用 **hierarchy（laminar cluster family）**——Semple & Steel 已证它与 rooted tree 是 1-1。这样 rooted 侧引理只谈 `cluster` / `MRCA` / `rootedTriple`，完全不碰 `X ⊕ Unit`；而「带标记叶的无根树」只是它的**一个实现**，靠转换引理接上。好处：将来换实现（如换成独立的 rooted 结构）不动上层 —— 与 §3.1「保留改底层空间」一致。

**结论**：老师方案**可直接用**，只要把 `X ⊕ Unit` 关在转换层。

### 3.4 split 的表示 —— ✅ 已定：自定义「划分族」（2026-10-02）

| 方案 | 优点 | 缺点 |
|---|---|---|
| **1a. `structure Split {A B : Finset X; Disjoint A B; A∪B=univ; 两 Nonempty}`**（上一轮暂定） | 4 条约束进类型；方向完整 | `{A,B}` 与 `{B,A}` 冗余，需 `swap` 或规范化 |
| **1b. 只存 `A`（+ Nonempty + `A ≠ univ`）** | 约束最少；`Disjoint`/`union` 变成定理 | 方向靠约定 |
| **2. `Sym2 (Finset X) + 子类型谓词`** | 白蹭 `Sym2`；「无序」自动化 | 约束反复展开；方向靠 `lift` |
| **3. 改造 `Setoid`/`Partition`** | 复用划分设施 | 语义是「任意多块」，非二分 → 绕远 |

#### 💬 待讨论（2026-10-02，老师提议）：bipartition / tripartition / quadripartition 一起定义？

> 老师原话：**「我感觉 bipartition 和 tripartition、quadripartition 一起定义更好，你觉得呢？」**

**我的判断：同意，而且理由比「省重复」强得多 —— 文献里这三者本就是一套，并且 ASTRAL 的核心对象正是它们。**

**文献先例（这三级对应是标准结果）**：

| 树的部件 | 诱导的划分 | 出处 |
|---|---|---|
| **边** `e` | **bipartition** `A\|B`（删 e） | Buneman / Bandelt–Dress（§2.3） |
| **内部节点** `v`（度 d） | **d-partition**；binary 时即 **tripartition** `A\|B\|C`（删 v） | ASTRAL 补充材料：「Each node u … **divides the set of taxa into three distinct subsets** … use **tripartitions and internal nodes interchangeably**」 |
| **内部边**（两端度 3） | **quadripartition** `A₁\|A₂\|B₁\|B₂` | Sayyari & Mirarab 2016：「Each **internal branch** divides L into four clusters, creating a **quadripartition**」 |
| 删 **k−1** 条边 | **k-partition**（一般框架） | Székely 2025, *New distances between phylogenetic trees* |

**三条强化理由**：

1. **ASTRAL 的核心对象就是 tripartition / quadripartition** —— 不是「将来可能用得上」。ASTRAL 的 DP 以 `Tri(u) = (A|B|C)` 为状态、以 `w(T)` 为权重；四分支支持度以 quadripartition 为单位。**要形式化 ASTRAL，这两个是必需品。**
2. **兼容性可推广**：Berry 等（*Optimal algorithms for local vertex quartet cleaning*）明说「**Two tripartitions (bipartitions) are compatible** if there exists a phylogeny that induces both … **Buneman (1971) 的算法可以轻松扩展到 tripartition**」。
3. **距离族统一**：Székely 2025 定义 `d_k` 距离族（基于公共 k-partition 数），其中 **`d₂` = Robinson–Foulds 距离**、**`d_{n−2}` = quartet 距离** —— RF 与 quartet distance 是同一族的两端。（术语：induced partition = **convex character**，公共的 = **biconvex character**。）

**但有个必须先想清楚的坑：四种「k-分裂」语义不同，不能合并成一个 `kPartition`。**

| 造法 | 得到的划分 | 用途 |
|---|---|---|
| 删 **1 条边** | bipartition | split / Buneman / NJ |
| 删 **1 个顶点**（度 d） | d-partition（binary：tripartition） | ASTRAL 节点分、四分支支持 |
| 删 **内部边 + 其两端点** | quadripartition | 内部边刻画 |
| 删 **k−1 条边** | k-partition | `d_k` 距离族 |

「删顶点」≠「删 k−1 条边」——它们是**不同的东西**，强行统一会掩盖语义。

**我的建议**：建一个**「划分族」层**，各自定义清楚 + 共享「划分」基础 + 备好与树的三种对应引理：

```lean
structure Partition (α : Type*) (n : ℕ) where   -- 一般 n-块划分（共享基础）；⚠️ 底是任意类型 α，不是 X
  parts : Fin n → Finset α
  disjoint : Pairwise (Disjoint on parts)
  union : Finset.univ.biUnion parts = Finset.univ   -- Finset 无 ⋃ 记法
  nonempty : ∀ i, (parts i).Nonempty

abbrev Split (X) := Partition X 2            -- 二分：专用 API（兼容性 / Buneman）
-- 另给 Tripartition / Quadripartition 各语义的专用结构 + 转换引理
```

**优先级**：`Split`（二分）仍**优先**（Buneman / NJ / 兼容性全建在它上面）；`Tripartition` / `Quadripartition` 紧随其后（ASTRAL 层前提）；一般 `kPartition` 放最后。

#### ✅ 决定（2026-10-02，老师采纳）：建「划分族」，`Partition` 为共享基础

老师原话：**「structure Partition 很好，采纳。」**

| 决定 | 内容 |
|---|---|
| **D3-a** | 采用 `structure Partition (α : Type*) (n : ℕ)`（`parts : Fin n → Finset α` + `disjoint` + `union` + `nonempty`）作**共享基础**。⚠️ **底必须参数化在任意类型 `α`**（非绑死 `X`）——否则 §3.5 的 `Split ↥S`（quartet/triplet 拓扑）写不出来 |
| **D3-b** | `Split`（二分）**单独立专用 API**（兼容性 / Buneman 压在它上面），底层可 `abbrev Split X := Partition X 2` |
| **D3-c** | **Tripartition / Quadripartition 各自语义化定义** + 与树的对应引理，**不硬塞进 `kPartition`**（「删顶点」≠「删 k−1 边」） |
| **D3-d** | 上一轮的「1a 两侧都存」**作废**——`Partition` 方案取代它（Fin n 索引天然给出方向，无需再存 A/B 两字段） |

**⚠️ 一个必须现在处理的命名冲突（否则开工即撞名）**：

Mathlib **已有** `Partition α`（`Mathlib.Order.Partition`，底是 `Set (Set α)`，语义「任意多块」）和 `SimpleGraph.Partition`。我们的 `Partition (X) (n : ℕ)` **同名不同物**，一旦 `open` 就撞。建议二选一：

| 命名方案 | 说明 |
|---|---|
| **`KPartition`**（推荐） | 直白（k-块划分），与 Mathlib 的 `Partition` 零冲突，`Split := KPartition X 2` 读起来也自然 |
| `Phylo.Partition`（进命名空间） | 保留 `Partition` 名字，靠 `NJ.Partition` 前缀隔离；代价是文档/引理名都要带前缀 |

**两个实现要点（写代码时别踩）**：
1. `Finset` 上没有 `⋃ i, parts i` 这个记法——全集并要写成 `Finset.univ.biUnion parts = Finset.univ`；`disjoint` 用 `Pairwise (Disjoint on parts)`（注意是 `Disjoint` 的 `Finset` 版）。
2. `abbrev Split X := Partition X 2` 有个语义微妙点：`Fin 2 → Finset X` 把两侧**有序化**了，而 split 本是**无序**的（`A|B` 与 `B|A` 同一）。这既可解释为「0 侧作参考侧」的规范化（好处：`swap` 变成 `Fin 2` 的换位，方向判定最简），也意味着**判等要商掉置换**。做 `Split` 专用 API 时把这一点显式化（给 `Split.swap` + `Split.eq_swap_iff`）。

#### 附：上一轮 4 个候选的最终处置

| 候选 | 处置 |
|---|---|
| 1a. 两侧都存 `Split` | ❌ 作废（被 `Partition` 方案取代） |
| 1b. 只存 `A`（+ Nonempty + `A ≠ univ`） | ➖ 备选（若最终嫌 `Fin n` 重，二分可退回此形态） |
| 2. `Sym2 (Finset X)` + 子类型 | ❌ 不采（约束反复展开、方向丢失） |
| 3. 改造 Mathlib `Setoid`/`Partition` | ❌ 不采（语义是「任意多块」，非二分）——**注意**：D3 采用的是**自定义** `Partition`，与这一条**不是一回事** |

### 3.5 quartet / triplet 的表示 —— ✅ 已定：集合 + split（拓扑分离，2026-10-02）

> 老师原话：**「quartet topology = quartet + split，quartet 就是 set，triplet topology 也可以类似定义」**

**核心思想：把「支撑集（set）」与「拓扑（topology）」彻底分开。**

- **quartet**（= 4 元叶集）**就是 set**——不带任何配对信息。
- **quartet topology** = **quartet + 一个 split**——配对方式由 split 承载。
- **triplet topology** 完全同构：= 3 元集 + 一个 split。

**文献先例（这套写法是标准，不是发明）**：

| 对象 | 先例写法 | 出处 |
|---|---|---|
| **rooted triple** | `ab\|c`：3 叶 rooted binary tree，`a,b` 成 cherry、`c` 邻 root；**`ab\|c` 与 `ba\|c` 等价**（无序） | Semple & Steel (2003)；Huber et al.；「有时也称 rooted triplets」 |
| **quartet** | `ab\|cd`：`{a,b}` 与 `{c,d}` 配对 | 标准 |
| 双向 | `ab\|c` 中「`{a,b}` 是 cherry」 ⟺ **`{a,b} \| {c}` 这个二分** | 同上 |

**统一形式（这就是老师说的那个 pattern）**：

| 对象 | 支撑集 | 拓扑 = **split of S** | 分裂形状 | 该支撑集上的拓扑数 |
|---|---|---|---|---|
| **quartet topology** | `S`，`\|S\|=4` | `Split ↥S` | **2 \| 2** | 3（= (4−1)!!） |
| **triplet topology** | `S`，`\|S\|=3` | `Split ↥S` | **2 \| 1** | 3（3 个 rooted triplet） |

两者**是同一个构造**，只是 `|S|` 与分裂形状不同。定一个 `Topology S := Split ↥S` 就统一了。

**Lean 形态（建议）**：

```lean
/-- 4 元叶集：quartet「就是 set」 -/
abbrev Quartet (X) := { S : Finset X // S.card = 4 }

/-- 3 元叶集 -/
abbrev TripletSet (X) := { S : Finset X // S.card = 3 }

/-- 拓扑 = 支撑集 + 其上的 2-划分。底换成子类型 ↥S —— 这就是「quartet + split」 -/
structure Topology (S : Finset X) where
  part : Split ↥S                                  -- 复用 §3.4 的 Split

abbrev QuartetTopology (X) := { Q : Quartet X // Topology Q.1 }   -- 2|2
abbrev TripletTopology (X) := { t : TripletSet X // Topology t.1 } -- 2|1
```

**四个必须现在想清楚的点**：

**① `Split` 的底必须**参数化**（这是 §3.1「保留改底层空间」的第一次实战检验）。**
quartet 的配对是**4 元集内部**的二分，不是整个 `X` 的二分。所以 §3.4 的 `Partition`/`Split` 定义时底要写成**任意类型** `α`（`structure Partition (α : Type*) (n : ℕ)`），`Split X := Partition X 2` 只是 `α := X` 的特例。**若把底硬编成 `X`，quartet 就废了。**

**② quartet topology 是「无根」的，triplet topology 天然「有根」。**
- `ab|cd` 只表达配对，不看方向 → 无根（§3.3 的无根层）。
- `ab|c` 里 **`c` 是外群**（"path from a to b does not intersect path from c to root"）——**「谁是外群」需要 root 才能说**。且**无根树上 3 叶只有 1 种拓扑**（三叉），无信息。
- ⇒ **triplet 概念属于 §3.3 的 rooted 层**，而 quartet 属于无根层。这个不对称是本质的，不是实现细节。

**③ 无序性要商：`ab|cd = cd|ab`，`ab|c = ba|c`。**
`Split ↥S` 用 `Fin 2` 索引会把两侧有序化（见 §3.4 的同一问题），所以 `Topology` 的判等要**商掉 `Split.swap`**；`ab|c` 与 `ba|c` 的等价还额外商掉**支撑集内 2 元侧的置换**。建议给 `QuartetTopology`/`TripletTopology` 一套 `swap` + `eq_iff`。

**④ 支撑集的 Lean 表示有三个候选，各有一个坑**：

| 候选 | 说明 | 坑 |
|---|---|---|
| **`{ S : Finset X // S.card = 4 }`**（推荐） | `Finset` 天然无重，`card` 直接可用 | 无 |
| `Finset.powersetCard 4 (univ : Finset X)` | 直接枚举所有 4 元子集（做 quartet 枚举方便） | 是「一族子集的 Finset」，非单个 quartet 类型 |
| `Sym X 4` | Mathlib 白蹭 `Sym` 全套（**`Sym2 α ≃ Sym α 2`** 已证） | ⚠️ **`Sym α n` 是 `Multiset` 商置换，允许重复元素**（`{a,a,b,c}` 也是 `Sym X 4` 的元素）→ 得再挂 `Nodup` 才等价于 4 元子集，反而绕 |

**命名**：`Quartet` / `QuartetTopology` / `Triplet`（= `TripletSet` + 拓扑）/ `Topology`。§2 概念清单已同步。

#### 附：旧 3 候选的最终处置

| 旧候选 | 处置 |
|---|---|
| A. `Finset X`(card=4) + 选一对作「一侧」 | ✅ **采纳其精神**，但升级为「set + `Split ↥S`」——「选一对」的规范化交给 `Split` 承载，不再手工选 |
| B. `Sym2 (Sym2 X)` | ❌ 不采（见坑 ④：`Sym` 是多重集商，需额外 `Nodup`） |
| C. 自定义 `structure Quartet {S; card_S; side; ...}` | ⚠️ 被 `Topology S` 取代（更通用：triplet 一并覆盖） |

### 3.6 加权函数的表示 —— 讨论中（2026-10-02 老师问：除了枝长还有哪些用例？）

#### 3.6.1 「权重」在 phylogenetics 里是三种不同的东西

| 类别 | 载体 | 可加？ | 典型用例 |
|---|---|---|---|
| **A. 边权（branch length）** | 边 `Sym2 V` | ✅ 沿路径求和有意义 | 枝长（见 §3.6.2） |
| **B. 结构权** | split / quartet / 节点 | ❌ 各自独立 | wRF、KF、BHV、split decomposition、quartet weight、支持度 |
| **C. 标注权（annotation）** | 任何对象 | ❌ | bootstrap、后验概率、演化速率 |

**混为一谈的后果**：`dist u v = Σ 边权` 这个定义只对 A 类有意义；对支持度树（B/C 类）会算出一个无意义的数。

---

#### 3.6.2 A 类·枝长的**单位**不止一种（同一拓扑 + 不同单位 = 不同对象）

| 单位 | 含义 | 出处 |
|---|---|---|
| **SU**（substitution units） | 每站点**期望替换数**（= 速率 × 时间）；序列推断树的默认 | 标准；CASTLES 论文 |
| **Time**（时间，Myr/年） | 绝对年代（需分子钟 / 化石标定） | chronogram；dating |
| **CU**（coalescent units） | **世代数 / Ne**（溯祖单位） | MSC；ASTRAL / MP-EST 输出 |
| **θ**（种群大小参数） | `θ = 2Ne·μ`（二倍体；`4Ne·μ` 视约定） | MSC；Degnan & Rosenberg 2009 |

**换算**：CU → mutation units 乘 `θ/2`（Degnan & Rosenberg 2009）。

**⚠️ 您实验室 CASTLES 论文原话（Tabatabaee, Zhang, Warnow, Mirarab 2023）**：
> "the branch lengths produced by summary methods are in **coalescent units (CUs)**, and these do not directly lead to branch lengths in substitution units. Moreover, **branch lengths in coalescent units are inferable only for the internal branches**"

⇒ CU 枝长**只有内部枝可推**（叶枝在 CU 下无意义），且 CU 与 SU 常差**两个数量级**。**「枝长」在库里不能有默认单位**——单位是必须显式携带的信息。

**枝长的下游用途**（CASTLES 列举，全部**要求权重可加** ⇒ 属 A 类）：

| 用途 | 出处 |
|---|---|
| 定年 dating | — |
| 比较基因组 comparative genomics | Hahn et al. 2005 |
| 比较性状分析（布朗运动等） | Felsenstein 1985；O'Meara 2012 |
| phylodynamics（疾病传播动力学） | Volz et al. 2013 |
| 物种界定 species delimitation | Rannala 2015 |
| 系统发育多样性 PD | Faith 2002；Lozupone & Knight 2005 |
| 检测选择（dN/dS 沿树） | Kosakovsky Pond & Frost 2005；Lanfear et al. 2010 |

---

#### 3.6.3 B 类：**不在边上**的权重（最容易漏）

| 权重对象 | 含义 | 用途 / 出处 |
|---|---|---|
| **split weight** | 给每个 split 一个实数权 | **BHV 空间把加权树完全等同于 split 权重向量**（Billera–Holmes–Vogtmann 2001）；split decomposition（Bandelt & Dress 1986） |
| **quartet weight** κ(q) | quartet 内部路径长度 | Semple & Steel Def 2.3.3 |
| **node weight** | 内部节点标注 | MSC 的 Ne；ASTRAL 内部枝 ≈ IL 期种群大小 |
| **支持度** | bootstrap % / localPP / 后验概率 | Felsenstein 1985；Sayyari & Mirarab 2016 |

**由此诱导的距离族**（都工作在「**权重向量**」上，而非「图 + 边权」）：

| 距离 | 公式 | 出处 |
|---|---|---|
| **RF**（无权） | split 对称差计数 | Robinson & Foulds 1981 |
| **wRF** | `Σ_s \|l₁(s) − l₂(s)\|`（split 权重上的 **L1**） | Robinson & Foulds 1979 |
| **KF / branch score** | `√Σ_s (l₁(s) − l₂(s))²`（**L2**） | Kuhner & Felsenstein 1994 |
| **BHV** | 加权树空间上的测地距离（`2n−3` 维） | Billera, Holmes & Vogtmann 2001 |
| **rooted triples / quartet distance** | triple / quartet 向量上的 L1 | Critchlow et al. 1996 |

---

#### 3.6.4 ✅ 关键设计结论：「可加」才是分界线

```
可加（additive） → 诱导距离 → 树度量 → NJ / Buneman / 四点条件      ← A 类（枝长）
不可加（label）  → 只是标注 → 参与比较必须另定规则（wRF/KF 等）      ← B / C 类
```

⇒ 库里应**显式区分两种树**：
- **`WeightedTree`（权可加；沿路径求和 = 距离）** —— NJ / Buneman / 一切距离法需要
- **`AnnotatedTree`（权只是标注；路径和无意义）** —— 支持度、速率、Ne

这正好也是 §3.1 接口纪律的又一次应用：**不预设权重是距离**，把「可加性」变成一个显式的结构字段/类型区分。

---

#### 3.6.5 表示方案

| 方案 | 优点 | 缺点 |
|---|---|---|
| `w : V → V → ℝ`（对称、非相邻为 0） | 简单直接 | 冗余；要维护「非边为 0」的一致性 |
| `w : Sym2 V → ℝ` | 天然对称、无向 | 需要 `Sym2` 求和/遍历设施 |
| `E : Type` 独立边类型 + `w : E → ℝ` ✅ **已选** | 最贴图论；便于「删边 / 加边」重排操作；`w` 定义域不冗余 | 要维护 `E` 与顶点对的对应 |
| **`Split → ℝ`（有限支撑）** ← 新 | **与 BHV / wRF / KF 同一表示**（加权树 = split 权重向量）；天然容纳「非边权重」 | 要从图算 split；叶枝 → 平凡 split 要记账 |

**✅ 决定（2026-10-02，老师）**：边权底层用 **`E → ℝ`**（独立边类型），原话「**E → ℝ 感觉自然**」。

**但「E 是不是新字段」必须现在定——两条子路线**：

| 子路线 | 定义 | 说明 |
|---|---|---|
| **A. `E` 派生（推荐）** | `E := {e : Sym2 V // e ∈ graph.edgeSet}` | **零维护**：`E` 由 `graph` 唯一确定，无需一致性字段。恰好就是 Mathlib 的 `SimpleGraph.edgeSet : Set (Sym2 V)` |
| **B. `E` 独立字段 + 等价** | `E : Type` + `edgeEquiv : E ≃ {e // e ∈ graph.edgeSet}` | 允许 `E` 携带独立结构（重排、加权网络、多图）；代价是每次用边都要过 `edgeEquiv` |

**✅ 已选子路线 A（2026-10-02，老师）**：`E` **派生**（不新字段）——`E := {e : Sym2 V // e ∈ graph.edgeSet}`，由 `graph` 唯一确定，无需一致性字段；恰好是 Mathlib 的 `SimpleGraph.edgeSet : Set (Sym2 V)`。**B 留作将来升级**——真需要「边带额外结构」时，A 加一条 `edgeEquiv` 即变成 B，上层引理不受影响（§3.1 接口纪律 3）。

```lean
structure Phylogram (X : Type*) extends Cladogram X where
  w : {e : Sym2 V // e ∈ graph.edgeSet} → ℝ      -- 子路线 A：E 派生
  w_nonneg : ∀ e, 0 ≤ w e.1
```

**顺带得到 `toSplitWeight : Split → ℝ` 的免费投影**（BHV 的洞见仍然适用）——叶枝 → 平凡 split、内边 → 非平凡 split，逐边搬运即可。**非边权重（split/quartet/node）将来照旧在此层之上另建**（§3.6.3）。

**值域**：`ℝ`。注意 **0 权边合法**（零长边 = polytomy，正因如此 §3.5 `IsCherry` 用 `≤`）；**负权一般排除**（树度量要求 ≥ 0，BHV 也取非负）。

---

#### 3.6.6 ✅ 决定（2026-10-02，老师定）：**三层结构**

> 老师原话：**「cladogram phylogram 这两层是必备的，annotated 是第三层，但这个先待定。」**

| 层 | 名称 | 内容 | 状态 |
|---|---|---|---|
| **第 1 层** | **Cladogram** | **纯拓扑**（无枝长字段；枝长不携带信息） | ✅ **必备** |
| **第 2 层** | **Phylogram** | 拓扑 + **可加边权** `w`（`dist = Σ 路径上的 w`） | ✅ **必备** |
| **第 3 层** | **AnnotatedTree** | + 任意标注（**不要求可加**） | ⬜ **待定** |

**文献依据（三层是标准术语）**：

| 术语 | 定义 | 出处 |
|---|---|---|
| **cladogram** | "gives **no meaning to branch lengths**; only the sequence and topology of the branching matters" | LibreTexts 26.2；Kling et al. 2018 |
| **phylogram** | "branch lengths are **directly related to the amount of genetic change**"（替换数 / 形态变化） | 同上 |
| **chronogram**（= time tree / ultrametric tree） | "branch lengths are **directly related to time**"；**超度量**（所有现存叶到根等距） | 同上 |

**⚠️ 一个必须澄清的术语陷阱**：
文献里 cladogram / phylogram / chronogram 是**同一拓扑的三种「facet」（枝长解释）**——"**the branch connections are the same in each, but the branch lengths have been adjusted to reflect different measures**"（Kling et al. 2018）——它们是**并列**的，不是包含链。
而老师这个分层是**结构性包含**（拓扑 → 加可加权 → 加任意标注），两者是**不同维度**，不冲突。另外「cladogram」一词在文献里有歧义（"sometimes applied to **any** type of phylogenetic tree"），这里取「**纯拓扑**」这个义项。

**✅ 与 §3.6.4「可加性分界」严丝合缝**：

```
第 1 层 Cladogram    ——  无权重（可加性不适用）
第 2 层 Phylogram    ——  可加侧  ←→ 诱导距离 → 树度量 → NJ/Buneman/四点条件
第 3 层 Annotated    ——  标注侧  ←→ wRF/KF/支持度，另定规则
```

**chronogram 的定位** = **Phylogram 的特例**（额外约束 `ultrametric`：所有叶到根路径长相等）。所以不必单开一层，用一条谓词/子类型即可：`IsUltrametric (T : Phylogram X) : Prop`。

**Lean 形态（建议，用 `extends` 做递进）**：

```lean
/-- 第 1 层（必备）：cladogram = 纯拓扑树 —— 即 §3.2 的 PhyloTree -/
structure Cladogram (X : Type*) where
  V : Type
  [Fintype V] [DecidableEq V]
  graph : SimpleGraph V
  isTree : graph.IsTree
  leaf : X ↪ V
  leaf_iff_degree_one : ∀ v, (∃ x, leaf x = v) ↔ graph.degree v = 1
  no_degree_two : ∀ v, graph.degree v ≠ 2

/-- 第 2 层（必备）：phylogram = cladogram + 可加边权 -/
structure Phylogram (X : Type*) extends Cladogram X where
  w : Sym2 V → ℝ
  w_nonneg : ∀ e, 0 ≤ w e
  -- 「可加」由 dist 定义承载：dist u v := 路径上 w 之和（路径唯一，`isTree` 保证）

/-- 第 3 层（待定）：annotated —— 先不设计，留接口 -/
-- structure AnnotatedTree (X : Type*) extends Cladogram X where annot : ...
```

**三个设计要点**：
1. **`Cladogram` 就是现有 `PhyloTree`**（§3.2 已定的那个），所以**第一层已定，无新增结构**。
2. **`extends` 让 `Phylogram` 免费继承全部拓扑引理**（Walk/IsTree/叶），第二层只加 `w` 两个字段——这正是 §3.1「接口包一层」的收益。
3. **第三层待定不影响前两层开工**——`AnnotatedTree` 若是 `Cladogram` 的扩展（而非 `Phylogram` 的），那三层是**树形**而非链；若将来要让 `Phylogram` 当 `AnnotatedTree` 的特例（权恰好可加），再加转换引理即可。**先留口子，不预付成本。**

**对既有代码的影响**：`NJ/CherryTree.lean` 的 `TreeRealization`（带 `d : V → V → ℝ`）**就是 Phylogram 的「距离投影」**——`d` 由 `w` 沿路径求和得来。将来重构时，`TreeRealization` 应改由 `Phylogram` 派生，`d` 变成定理而非字段（`d_leaf`、`d_tri` 等由 `w` 推出）。

### 3.7 restriction（`T\|Y`）—— ✅ 已定：定义为一个**映射**（`suppress`，方案 C），Cladogram / Phylogram 各一份（2026-10-02）

先例定义 `T|Y` 时都要 "**suppress** resulting degree-two vertices"（Semple & Steel；Steel & Székely）。

| 方案 | 说明 |
|---|---|
| **A. 不真做抑制** | `T\|Y` 定义为「诱导子树中所有度 2 顶点被**合同**后的商」→ 需要商类型 |
| **B. 只定义「诱导子树」** | 抑制留到需要时再说（多数引理其实不需要规范化形态） |
| **C. 定义 `suppress`** | `SimpleGraph V → SimpleGraph V'`（重写顶点集）→ 最忠实，但要处理类型重写 |

**⚠️ 关键：这一条与 §3.2 的决定「强耦合」——不能单独定。**

§3.2 把 **`no_degree_two` 写进了 `Cladogram`**（Semple & Steel 的正规化条件）。于是：

```
T 是 Cladogram  ⟹  T 无度 2 顶点
但 T|Y 的「诱导子树」天然会产生度 2 顶点
⟹  T|Y 若不抑制，就不是 Cladogram → 破坏类型一致（restriction 的结果不在同一类型里）
```

**两条出路（必须选一条，否则 `T|Y` 的类型说不通）**：

| 出路 | 做法 | 代价 |
|---|---|---|
| **① 真做抑制（→ 方案 C）** | 定义 `suppress`，让 `T\|Y : Cladogram Y` | 要处理顶点集重写（`↥` 子类型 + 合同），但类型不变式保住 |
| **② 放松 `Cladogram`** | 把 `no_degree_two` 从 `Cladogram` 降级为**谓词** `Nodedeg2`，`T\|Y` 只保证「是树 + 叶标号 Y」 | ⚠️ 动摇 §3.2 的决定；且 **Splits-Equivalence 的「唯一性」需要它**（否则同 split 系统对应多棵带度 2 顶点的树） |

**✅ 已定（2026-10-02，老师）：选择方案 C，且「cladogram 和 phylogram 都能把 restriction 定义为映射」。** 理由：`no_degree_two` 是唯一性的地基（§3.8 的 C 直接用），不该降级；而「抑制」本身在 `SimpleGraph` 上是一段独立小工程（删除度 2 顶点、连接其两邻），一次写好处处可用。**A（商类型）不必**——C 已经是「构造出规范形」，且**是函数**（可 `simp`、可复合、可 `#eval`），比关系型/商型好用得多。

**实施要点**：树是连通的且叶集固定，所以 `T|Y` 可以**先取诱导子图**（顶点 = 连接 Y 的最小连通子树的顶点），再 `suppress` 掉所有度 2 顶点；剩下顶点里度 1 的正是 Y（`leaf` 嵌入保持）。

#### 两层各有一份 restriction —— 而 Phylogram 那份**必须补一条合并规则**

> 老师补充：**「cladogram 和 phylogram 都能定义 restriction 为映射」**

```lean
namespace Cladogram
/-- 拓扑侧：诱导子树 + 抑制所有度 2 顶点（纯拓扑，无权重） -/
def restrict (T : Cladogram X) (Y : Finset X) : Cladogram ↥Y := ...
end Cladogram

namespace Phylogram
/-- 权侧：抑制度 2 顶点时，**两条边合并为一条，边权相加** -/
def restrict (T : Phylogram X) (Y : Finset X) : Phylogram ↥Y := ...
/-- 核心性质：restriction 保 Y 内叶对的距离 -/
theorem restrict_dist (T : Phylogram X) (Y : Finset X) (a b : ↥Y) :
    (T.restrict Y).dist a b = T.dist a b := ...
end Phylogram
```

**三个要点**：

1. **Cladogram 的 restriction 是纯拓扑映射**，无需任何数值规则。
2. **Phylogram 的 restriction 必须规定「合并边权 = 两边权之和」**——否则 `dist` 会变。**这条规则正是「可加性」的直接体现**（§3.6.4）：`d(a,b) = Σ 路径上的 w`，删掉中间那个度 2 顶点后，两段之和 = 原来那一段。
3. **`restrict_dist`（保距离）是 restriction 的灵魂**——它同时也是「为什么边权必须相加」的**证明义务**：若不做加法，这条定理证不出来。

**兼容性（自然性）引理**（应当有一条）：`Phylogram.restrict` 是 `Cladogram.restrict` 的 lift ——
```lean
theorem toCladogram_restrict (T : Phylogram X) (Y : Finset X) :
    (T.restrict Y).toCladogram = T.toCladogram.restrict Y := ...
```

**第三层待定**：`AnnotatedTree` 的 restriction **规则未定**——因为标注**不可加**（§3.6.4），「合并边时标注怎么办」（求和？取大？丢弃？）没有唯一答案。这正好说明第三层该慢定：**restriction 的可定义性本身就是「可加 vs 标注」分界的又一次体现。**

### 3.8 树相等 —— ✅ 已定：**A 作定义（`Iso`）+ C 作定理（Splits-Equivalence）**（2026-10-02）

| 方案 | 优点 | 缺点 |
|---|---|---|
| **A. 定义 `Iso`（保标号同构）关系，说「T ≅ T'」** | 忠实先例（"considered the same if label-preserving isomorphism"）；**Mathlib 有现成 `SimpleGraph.Iso` 可白蹭** | 每条引理都要 up to iso，繁琐 |
| **B. 直接把「相等」定义为拓扑相等**（用 `Quot`） | 引理干净 | 商类型难用（`Quot` 上的函数要 well-defined） |
| **C. 规范化表示**（树用唯一标准形，如 canonical split set） | 相等 = 结构相等，最干净 | 需要先有「split 系统唯一确定树」这条定理 |

**文献先例（一致口径：保标号同构）**：

| 出处 | 原话 |
|---|---|
| MathWorld（引 Semple & Steel 2003） | "Two such trees are considered the same when there is a **graph isomorphism between them that fixes every leaf label**." |
| Steel & Székely, *An improved bound on MAST* | "Two phylogenetic X-trees are considered the same, if there is a **label-preserving graph isomorphism** between them." |
| Steel, *Tracing Evolutionary Links* (2014) | 两棵 rooted X-树等价 ⟺ "isomorphic as rooted trees by an isomorphism that is the **identity on X**"（= 只允许内部顶点重命名） |

**🆕 Mathlib 现成设施（关键利好）**：`Mathlib/Combinatorics/SimpleGraph/Maps.lean:307`
```lean
abbrev Iso := RelIso G.Adj G'.Adj        -- 记法  G ≃g G'
```
⇒ **图同构部分完全白蹭**（含 `refl` / `symm` / `trans` / 复合引理），我们只需补「保持 `leaf`」与「保持 `w`」。

**✅ 已定（2026-10-02，老师）：主用 A，C 降格为定理**
- **主定义 `Iso`**（方案 A）——忠实先例；`SimpleGraph.Iso` 白蹭。
- **C 不作定义、而作定理**：`Nonempty (Iso T T') ↔ splits T = splits T'` ——**这正是 Splits-Equivalence 定理**（Semple & Steel Thm 3.1.4；Olds & Sullivant Thm 2.5）：
  > "Σ is pairwise compatible and contains the trivial splits **iff** there exists T with Σ = Σ(T). Furthermore, **the tree is uniquely determined by Σ(T)**; if Σ(T) = Σ(T′) then T and T′ are equivalent."
- **理由**：C 的「最干净」只有在**把定理当定义用**时才有，而 §3.2 那条纪律（等价关系是假设不是结论）同样适用——**不要把待证的定理写进定义**。选 A 不损失 C 的便利，只是把它变成一条可引用的定理。B（`Quot`）不采。

```lean
/-- 保标号（在 X 上恒等）的 cladogram 同构 —— 白蹭 `SimpleGraph.Iso` -/
structure Iso (T T' : Cladogram X) where
  gIso : T.graph ≃g T'.graph                                  -- Mathlib: RelIso T.graph.Adj T'.graph.Adj
  leaf_compat : ∀ x, gIso (T.leaf x) = T'.leaf x              -- identity on X
-- Phylogram 再加： w_compat : ∀ e, T'.w (gIso.mapEdge e) = T.w e
```

**一个实操建议**：把**大多数引理陈述在「同一个 `V` 同一棵 `graph`」上**（此时用 `=` 即可），只在**跨树比较**（RF / MAST / 共识树 / 树空间）时才用 `Iso`。这样 iso 的摩擦只落在真正需要它的地方。

**与 §5 第 10 条的联动**：C 要的 Splits-Equivalence **本来就是建议的首批大目标之一**——所以「A 作定义 + C 作定理」不但省事，还**把一个大目标直接接进来**，一举两得。

### 3.9 多元树 vs binary —— ✅ 已定：**一般树 + `IsBinary` 谓词**，需要 binary 时取别名/特殊处理（2026-10-02）

**先例**：`binary` = 内部顶点度**恰好 3**（无根）/ out-degree **恰好 2**（有根）；一般树只要求内部度 ≥ 3（无根）/ ≥ 2（有根）。**binary 是一般树的特例**（Semple & Steel）。

| 方案 | 优点 | 缺点 |
|---|---|---|
| **A. 只做 binary** | 简单；NJ / cherry 等多数定理都在 binary 语境 | **UPGMA 的 dendrogram 允许多元**；consensus tree 天然多元；`T\|Y` 也可能多元 |
| **B. 一般树 + `IsBinary` 谓词** | 灵活；与 Mathlib `SimpleGraph`（无 binary 假设）一致；只需在**需要的定理**上带假设 | 引理要带 `IsBinary` 假设（可批量处理） |
| **C. 两套定义** | —— | 重复劳动 |

**✅ 已定（2026-10-02，老师）：方案 B，并补充「需要 binary 的时候取别名或特殊处理」。** 理由：① 先例里「一般树」是**主定义**、binary 是特例，反过来会削掉 UPGMA / consensus / `T|Y`；② Mathlib 的 `SimpleGraph` 本身不假设 binary，`IsTree` 已白蹭，binary 只是一条额外谓词；③ 「引理要带假设」的代价可用「**在 `IsBinary` 假设下**开一段 section」批量消化。

#### `IsBinary` 的形态，与「别名 / 特殊处理」两种写法

```lean
/-- binary（无根）= 每个内部顶点度恰为 3（Semple & Steel） -/
def IsBinary (T : Cladogram X) : Prop :=
  ∀ v : T.V, ¬ IsLeaf T v → T.graph.degree v = 3

/-- 写法一【取别名】：把「binary 树」当成一种对象，丢给别的函数/结构 -/
abbrev BinaryCladogram (X : Type*) := { T : Cladogram X // T.IsBinary }
abbrev BinaryPhylogram (X : Type*) := { T : Phylogram X // T.IsBinary }

/-- 写法二【特殊处理】：在一批引理里开 section 带入假设，签名不重复 -/
section Binary
variable {T : Cladogram X} (hT : T.IsBinary)
theorem binary_internal_deg (v : T.V) (hv : ¬ IsLeaf T v) : T.graph.degree v = 3 := hT v hv
-- … 该 section 内的引理都自动带 hT
end Binary
```

**何时用哪个**：
- **需要把 binary 当作「一种对象」传递**（如 `NJ : Dissimilarity → BinaryPhylogram`，或某个只对 binary 有定义的重排操作）→ **别名（子类型）**。
- **只是定理需要假设**（如「binary 树上 cherry 数 ≥ 1」）→ **`section` 特殊处理**，避免每条签名都写 `(hT : T.IsBinary)`。

**两条注意**：
1. `IsBinary` 是**纯拓扑**概念，与边权无关——`w = 0` 的内边是 polytomy（§3.5）但拓扑上仍算 binary（度仍为 3）。
2. **有根版**另有一条：`IsBinary` 的 rooted 形式是「内部顶点 out-degree 恰 2」（§3.3 的 rooted 层建立后再补）。

### 3.10 距离/度量用不用 Mathlib 的 `Metric`

- ⚠️ 先例里 dissimilarity **明确不要求三角不等式**（"δ(i,j)=δ(j,i) ≥ 0, δ(i,i)=0"），而 `Metric` 要求三角不等式。
- 所以**不能用** `Metric`/`PseudoMetricSpace` 表示 dissimilarity（前期已踩过这个点）。
- 候选：自定义 `Dissimilarity` 结构（我们已有），或直接用函数 `X → X → ℝ` + 假设。**这一点已由 §3.6 的三层结构覆盖**（`Phylogram` 的 `w : E → ℝ` 是源头，`dist` 是派生）。

### 3.11 Splits-Equivalence 定理（第 10 条核心，2026-10-02 简述）

**一句话**：一个 split 系统「**两两相容**」⟺ 它是某棵树**全部边**诱导的 split 集；且这棵树**同构意义下唯一**。⇒ **树 ⟺ 相容 split 系统**，是**双射**。

**三个精确陈述（文献口径一致）**：

| 出处 | 陈述 |
|---|---|
| **Semple & Steel**, *Phylogenetics*, **Theorem 3.1.4**（原为 **Buneman 1971**） | 设 Σ 是 X-splits 的集合。则 Σ **唯一确定一棵树** ⟺ Σ **相容**。 |
| Hathcock (USC thesis), **Thm 2.12** | 存在 X-树 T 使 `Σ = Σ(T)` ⟺ Σ 的 split **两两相容**；若存在，则 **T 同构唯一**。 |
| Springer, *Characterizing compatibility…*, **Thm 1** | 设 Σ 含**所有平凡 split**。则 `Σ = Σ(T) ∪ Σ_triv(T)` ⟺ Σ **两两相容**；**T 同构唯一**。 |

**前置定义**（我们已有或将有）：
- **split of T**：删边 `e` → 叶集分成 `A|B`（§3.4）；**叶边**给**平凡 split** `{x} | X∖{x}`。
- **相容（compatible）**：`A₁|A₂` 与 `B₁|B₂` 相容 ⟺ **四个交 `A₁∩B₁, A₁∩B₂, A₂∩B₁, A₂∩B₂` 至少一个为空**。平凡 split 与**任何** split 相容。
- **`Σ(T)`**：T 的**所有边**（含叶边）诱导的 split 集。

**直觉**：两条 split 相容 = 「**可被同一棵树同时实现**」（不矛盾）。所以「两两相容」= 「全体可被同一棵树实现」。

**证明策略（形式化路线图）**：

1. **(⟹) 容易**：若 Σ 来自树 T 的边，则任两 split `σ₁, σ₂` 可证存在划分 `X₁|X₂|X₃` 使 `σ₁ = X₁|(X₂∪X₃)`、`σ₂ = (X₁∪X₂)|X₃` ⇒ `X₁∩X₃ = ∅` ⇒ 相容。**只用树的组合性质**。
2. **(⟸) 对 `|Σ|` 归纳**（全部难度在此）：
   - 取 `A|B ∈ Σ` 使 `Σ∖{A|B}` 仍相容 ⇒（归纳假设）存在唯一 `T'`；
   - **关键引理**：存在顶点 `v ∈ T'`，使 `T'∖v` 的**每个连通块的叶集要么 ⊂ A、要么 ⊂ B**；
   - 把 `v` **劈成两顶点** `v_A, v_B`（中间加一条边），A 侧接 `v_A`、B 侧接 `v_B` ⇒ 得 `T`，且 `Σ = Σ(T)`；唯一性由归纳假设传递。
   - **关键引理本身的证明 = 染色 + 极值点**：按 `A/B` 给 `X` 染色；「每条边恰有一侧连通块单色」⇒ 存在**唯一**顶点使所有连通块单色（本质是树上的**中值/极值顶点**论证）。
3. **这条「劈顶点」构造正是 BUILD 算法的种子**（Aho et al. 1981）⇒ 形式化它 ≈ 形式化 BUILD 的正确性。

**加权版（对 Buneman 直接有用）**：
> `d` 是 tree-like（伪）度量 ⟺ `d` 可由**正权相容 split 系统**分解：`d(x,y) = Σ_{分离 x,y 的 split} w(split)`；且该系统**唯一**，**split 与树的边一一对应**。（Semple & Steel Thm 3.1.4 + 7.1.8 + 7.3.2）

**为什么是地基（三条）**：
1. **树 ⟺ split 系统** ⇒ 给 §3.8 的「C 作定理」提供内容：`Nonempty (Iso T T') ↔ Σ(T) = Σ(T')`。
2. **BHV / wRF / KF 全建在「split 权重向量」上**（§3.6.3）⇒ 这条定理把「树」与「向量」正式对接。
3. **NJ / Buneman 的出口**：`NJ/CherryTree.lean` 里那条「Buneman 存在性」假设，其证明必经此处。

**形式化工作量评估（诚实）**：核心是「归纳 + 劈顶点 + 染色极值引理」，**不是**研究级难度，但工程量不小——需先备齐：路径唯一性、连通块叶集、劈顶点的图操作。**比 `max_z_cherry_core` 好啃**，属「大而常规」。

#### Quartet 版的等价描述 —— 与 split 的**关键差别**（2026-10-02 老师补充）

> 老师原话：**「应该还有一个等价描述，所有 quartet cladogram 兼容。」**

**有；但它的「判据形态」与 split 完全不同 —— 这点必须说清，否则会误用。**

**① 结构上的对应（确有双射）**：
- **`(n choose 4)` 个 quartet split 唯一决定一棵 binary X-树** —— **Colonius & Schultze (1981)**（stemmatology 语境），**Bandelt & Dress (1986)** 发展；且有**多项式**重建算法。
- 即 `q(T)` 是 binary 树 T 的**完整不变量** —— 与 `Σ(T)` 对 split 的角色**完全平行**。

**② 但相容性判据不同（关键）**：

| 情形 | 判据 | 复杂度 |
|---|---|---|
| **full**（每个 4 元子集**恰好一个** quartet） | ✅ 有：**推理规则** `ab\|cx ∧ ab\|xd ⟹ ab\|cd`（+ 对称变体）—— Colonius-Schultze 的完整刻画 | **多项式**（Bandelt-Dress） |
| **thin**（每个 `k≥4` 元子集至多 `k−3` 个 quartet） | 充分条件：`thin ⟹ 相容` | 判定多项式 |
| **一般 Q** | ❌ **无两两判据** | **NP-complete**（**Steel 1992**） |

**③ 与 split 的对照（务必记住）**：

| | **split** | **quartet** |
|---|---|---|
| 「树 ⟺ 数据」双射 | ✅ `Σ(T)` | ✅ `q(T)`（**binary** 时） |
| 判据形式 | **两两相容**（局部 ⟹ 整体） | **无两两判据**；full 时用**推理规则 / 闭包** |
| 判定复杂度 | **多项式**（甚至线性） | **NP-complete**（一般情形） |
| 「两两 ⟹ 整体」 | ✅ 成立 | ❌ **不成立** |

⇒ **split 相容性是「两两」的，quartet 相容性不是。** 这正是 Splits-Equivalence 比 quartet 版**干净得多**的原因。

**④ 对库的意义（建议）**：
- **Splits-Equivalence 先证**：判据局部、多项式，且是 Buneman 的出口。
- **Quartet 版另立**：精确说法是「**存在 cladogram 显示 Q 中所有 quartet**」= **Quartet Compatibility**，本身 **NP-complete**。所以它**只能作「存在性命题」或「算法目标」**（Quartet MaxCut、Q\*、thin 判据、full 情形的推理规则），**不能当判据 / 定义用** —— 否则等于把 NP-hard 写进定义。
- 一个呼应：上面的「退化 quartet」写法（`ab|cd` 表示 `ab‖cd` **或星形/polytomy**）与 §3.5 里 `IsCherry` 用 `≤` 是同一件事（含退化情形）。

---

## 4. 落地路线：里程碑 + 目录结构 + 第一步

### 4.0 Mathlib 支撑点清单（已实测，可直接白蹭）

| 需求 | Mathlib 位置 | 备注 |
|---|---|---|
| 图 / 游走 / `Walk` / `IsPath` | `Combinatorics/SimpleGraph/{Basic,Walk,Maps}` | —— |
| **`G.IsTree`** | `Acyclic.lean:57`（`structure IsTree : Prop extends …`） | 白蹭 |
| **树 ⟺ 路径唯一** ★ | `Acyclic.lean:240` **`isTree_iff_existsUnique_path`**：`G.IsTree ↔ Nonempty V ∧ ∀ v w, ∃! p : G.Walk v w, p.IsPath` | **M0 地基** |
| 叶存在性（度 1 顶点）★ | `Acyclic.lean:512` `IsTree.exists_ne_and_degree_eq_one` | 白蹭 |
| 图同构 `G ≃g G'` ★ | `Maps.lean:307` `abbrev Iso := RelIso G.Adj G'.Adj` | 树相等 |
| 边集 `Set (Sym2 V)` ★ | `G.edgeSet` | `E` 派生 |
| 度数 `G.degree` | `DegreeSum.lean` | 叶 = 度 1 |
| 无向对 | `Data/Sym/Sym2` | 边、quartet |
| **加权距离** | ❌ **无**（`SimpleGraph.dist : V → V → ℕ` 是**无权** BFS） | **必须自建** |

### 4.1 里程碑

| 里程碑 | 内容 | 交付 |
|---|---|---|
| **M0 树载体** | `structure Cladogram`（`V` / `graph` / `isTree` / `leaf : X ↪ V` / `leaf_iff_degree_one` / `no_degree_two`）+ 基础引理（`IsLeaf`、`leaf_degree_one`、`degree_one_leaf`、`path_unique`、`exists_leaf`） | `Phylo/Core.lean` 编译通过 |
| **M1 加权层 + 同构** | `Phylogram extends Cladogram`（`w : {e // e ∈ edgeSet} → ℝ` + `w_nonneg`）、`dist`（路径求和）、`restrict`（抑制 + **边权相加**）、`restrict_dist`、`Iso`（`≃g` + leaf/w 保持）、`splits : T → Finset (Split X)` | `Phylo/Core.lean` 续写 |
| **M2 split 系统 + Splits-Equivalence** ★ | `KPartition` / `Split`、相容性、**劈顶点引理**（染色 + 极值点）、**Splits-Equivalence 定理** | `Phylo/Split.lean` |
| **M3 Buneman** | tree metric / 四点条件 / 可加性；**Buneman 定理**（加权版，用 M2） | `Phylo/Metric.lean`；接回 `NJ/CherryTree.lean` |
| **M4 quartet / triplet 层** | `Topology`（集合 + `Split ↥S`）、`display`、Colonius-Schultze（full 推理规则）、quartet 距离 | `Phylo/Quartet.lean` |
| **M5 算法层** | NJ（接现有 `Cherry.lean`）、UPGMA（超度量）、RF / KF / BHV、NNI/SPR、parsimony / ML | `Phylo/Algorithm/…` |

**前四个里程碑对应第一批大目标**（Splits-Equivalence → Buneman），M0/M1 是它们的必要前置。

### 4.2 目录结构（建议）

**命名（2026-10-02 老师提议）**：**仓库 / 包名 = `lean4phylo`**（双关：Lean **4** phylo / **lean for** phylo）；**Lean 库名 = `Phylo`**（PascalCase，`import Phylo.Core` 才顺）。⚠️ **库目录名不得与 `NJ` 仅差大小写**（Windows 文件系统大小写不敏感，`Nj/` 会撞 `NJ/`）。
> 注：Lean 惯例里包名（小写）与库名（PascalCase）本就常不同 —— Mathlib（包 `mathlib`）/ PhysLib（库 `PhysLean`）。

```
lean4phylo/                     ← 仓库根（包名 lean4phylo）
  Phylo/                        ← Lean 库（lean_lib Phylo）
    Core.lean                -- M0+M1：Cladogram / Phylogram / IsLeaf / dist / restrict / Iso
    Split.lean               -- M2：KPartition·Split / 相容性 / Splits-Equivalence
    Metric.lean              -- M3：tree metric / 四点条件 / Buneman
    Quartet.lean             -- M4：Topology / display / Colonius-Schultze
    Mathlib/                 -- 存放「Mathlib 缺、自建」的声明（取自 LeanProject 模板）
    Algorithm/
      NJ.lean                -- M5
      UPGMA.lean
      Compare.lean           -- wRF / KF / BHV
  Phylo.lean                    -- 根模块：import 全部（字母序）
  NJ/ + NJ.lean                 -- 现有 NJ 算法应用（保留）
```

**库与算法分离**：新库叫 `Phylo/`（通用库），现有 `NJ/Cherry.lean`、`NJ/CherryTree.lean`（NJ 算法应用）**保留为独立文件**，将来作为 `Phylo/Algorithm/NJ` 的验证样例 —— 避免「库」和「某个算法的实现」混在一个模块里。

### 4.3 第一步（M0 具体动作）

1. 新建 `Phylo/Core.lean`，最小导入集起步（开发期 ~12s/次）：
   ```lean
   import Mathlib.Combinatorics.SimpleGraph.Acyclic
   import Mathlib.Combinatorics.SimpleGraph.Maps
   import Mathlib.Combinatorics.SimpleGraph.DegreeSum
   import Mathlib.Data.Fintype.Basic
   import Mathlib.Data.Finset.Card
   ```
2. 写 `structure Cladogram (X : Type*)`（§3.2 / §3.6.6 的形态）。
3. 写 `IsLeaf` 与四条基础引理：`leaf_degree_one` / `degree_one_leaf` / `path_unique`（调 `isTree_iff_existsUniquePath`）/ `exists_leaf`。
4. `lake env lean Phylo/Core.lean` 迭代到零警告。
5. **交付后停下汇报接口**（老师定的「M0 跑通再确认」节奏），确认后再开 M1。

**M0 开工时需确认的两个技术点**：
- `SimpleGraph.IsTree` 的 `extends` 具体列出什么（决定 `T.isTree.connected` 能否直接用）；
- `IsPath` 的确切位置与命名空间（`Walk.lean` vs `Walk/Basic.lean`）。

### 4.4 概念推进顺序（与概念清单 L0–L5 对齐）

1. **L0 + L1 树载体**（概念 1–13）：树、叶、边权、加权距离、restriction
2. **L1 后半 + L2 分裂**（14, 17–19）：cherry、split、兼容性 + **Splits-Equivalence 定理**
3. **L2 quartet + L3 度量**（21, 25–28）：quartet、四点条件、tree metric、**Buneman 定理**
4. **L3 判据 + L5 NJ**（29, 35）：Q-判据 → NJ（接上已有 `Cherry.lean`）
5. **L5 UPGMA**（26, 36）：超度量 → UPGMA
6. **L4 比较与重排**（31, 32）：RF、NNI/SPR
7. **L5 模型**（37–40）：parsimony、ML、gene/species tree

---

## 5. 待老师拍板的问题

1. ~~**树载体**：3.1 的 A / B / C 选哪个？~~ ✅ **已定：3.1 方案 C（接口包一层）**，附四条接口纪律 —— 见 §3.1。
2. ~~**「叶」的定义**：3.2 的 A / B / C？~~ ✅ **已定：3.2 方案 C（两者并存 + 等价引理）** —— 见 §3.2。
3. ~~**有根/无根**：3.3 的哪条路线？~~ ✅ **已定：3.3 方案 A**（先做无根；有根 = 「无根 + 标记叶」另建一层）—— 见 §3.3。
4. ~~**split 形态 + k-分裂族**~~ ✅ **已定：建「划分族」**——自定义 `structure Partition (X) (n : ℕ)` 作共享基础；`Split` 单独立专用 API；Tri/Quadripartition 各自语义化；上一轮「1a 两侧都存」作废（→ D3-a…d，见 §3.4 末）。**遗留命名问题：自定义 `Partition` 与 Mathlib `Partition` 撞名，需改名（建议 `KPartition`）。**
5. ~~**quartet 形态**~~ ✅ **已定：集合 + split（拓扑分离）**——quartet = 4 元集；quartet topology = quartet + `Split ↥S`（2|2）；triplet topology 同构（3 元集 + 2|1）。**连带约束：`Split`/`Partition` 的底必须参数化在任意类型 `α` 上（否则 `Split ↥S` 写不出来）**；triplet 属 rooted 层。见 §3.5。
6. ~~**加权函数**~~ ✅ **已定（2026-10-02）**：① 三层结构——**第 1 层 `Cladogram`（纯拓扑，= 现有 `PhyloTree`）与第 2 层 `Phylogram`（+ 可加边权）必备**，第 3 层 `AnnotatedTree` 待定（留口子）；② **边权底层 = `E → ℝ`（独立边类型）**，`E` **派生**自 `graph.edgeSet`（**子路线 A 已选**，零维护）。见 §3.6.5–3.6.6。
7. ~~**树相等**~~ ✅ **已定：A 作定义（`Iso`，白蹭 Mathlib `SimpleGraph.Iso` `G ≃g G'`）+ C 作定理（= **Splits-Equivalence**）**，B（`Quot`）不采。见 §3.8。
8. ~~**binary 优先还是通用树优先**~~ ✅ **已定：方案 B（一般树 + `IsBinary` 谓词）**，需要 binary 时**取别名**（`BinaryCladogram := {T // IsBinary T}`，当对象传递）或**特殊处理**（`section` 带假设，只影响签名）。见 §3.9。
9. ~~**restriction 的抑制操作**~~ ✅ **已定：方案 C（真做 `suppress`），且 Cladogram / Phylogram 各定义为一份映射**；Phylogram 侧须补「合并边权相加」规则 + `restrict_dist`（保距离）。第三层 `AnnotatedTree` 的 restriction 规则未定（不可加）。见 §3.7。
10. ~~**要不要把「Splits-Equivalence 定理」和「Buneman 定理」作为库的第一批大目标**~~ ✅ **已定（2026-10-02）：要，且 Splits-Equivalence 必须证**（老师原话「这个必须证」），Buneman 建在其上。**另确认 quartet 版等价描述**（Colonius-Schultze：`(n choose 4)` 个 quartet 决定 binary 树）——但**判据形态不同**（无两两判据；full 情形用推理规则；一般情形 NP-complete），故**只作算法目标、不作定义**。见 §3.11。

---

## 6. 文献来源

**教材**：Semple & Steel, *Phylogenetics* (2003)；Steel, *Phylogeny: Discrete and Random Processes in Evolution* (2016)；Felsenstein, *Inferring Phylogenies* (2004)；Huson, Rupp & Scornavacca, *Phylogenetic Networks* (2010)；Dress, Huber, Koolen, Moulton & Spillner, *Basic Phylogenetic Combinatorics* (2011)。

**关键论文**：Buneman (1971/1974, splits & tree metric)；Bandelt & Dress (1986, split decomposition)；Saitou & Nei (1987)；Studier & Keppler (1988)；Bryant & Moulton (Neighbor-Net, arXiv:math/0702515)；Mihaescu, Levy & Pachter (2006, arXiv:cs/0602041)；Weller (2023, arXiv:2305.18866)；Robinson & Foulds (1981)；Kelk et al (2025, arXiv:2512.16691)。

**讲义/学位论文**：Huber & Steel, *Tree reconstruction from triplet cover distances* (2013)；Bastkowski, *From Trees to Networks and Back* (PhD)；Gambette, *Algorithmics & Phylogenetics*（课程讲义）；Atlantis Press（NNI/SPR/TBR 定义）；Stanford CS262 Lecture 15（UPGMA/超度量）。
