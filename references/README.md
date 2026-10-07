# `references/` —— 形式化缺口对应的原始文献与证明原文

> **生成**：2026-10-07 ｜ **最后更新**：2026-10-07 14:30（老师补充下载 12 篇付费墙文献；扫描件改用 PDFium 渲染）
> **用途**：为 `HANDOVER.md` 的 T0 批（`QuartetDecidesTree` / Buneman / NJ / NJst / SVDQuartets）
> 与 `NEXT.md` 的后续目标（不变量 / 溯祖基座 / supertree / 低垂果实）提供**可直接查阅的证明原文**。
> **来源**：全部为**公开可获取**版本（arXiv / 出版社 OA / 作者主页 / PMC / 机构仓储）。
> **付费墙文献见 §5**，附完整链接供老师自行下载。

---

## 0. 目录结构与规模

```
references/
├── README.md          ← 本文件（索引 + 证明出处映射 + 失败链接）
├── pdf/               ← 原始 PDF（18 篇）
├── md/                ← 转好的 Markdown（18 篇，可直接读）
├── img/               ← Buneman 扫描件的页面图像（12 张，OCR + 读图用）
├── ocr/               ← tesseract OCR 的逐页纯文本（12 个）
├── convert.py         ← PDF → Markdown（pdfminer + 符号修复 + 扫描件防护）
├── render_pages.py    ← ★ 扫描件：PDFium 渲染页面为 PNG（**优于 extract_img.py**）
├── merge_ocr.py       ← 把 ocr/ 逐页文本合并成可读 Markdown
├── extract_img.py     ← 扫描件 → 页面图像（pypdf，**已弃用**，见下方说明）
└── cleanup.py         ← 单独修复 (cid:) 字形残留
```

**当前规模**：**30 篇** PDF + **30 篇** Markdown。
**其中 3 篇为扫描件**（Buneman 1971/1974、Evans–Speed 1993），正文由 PDFium 渲染 + tesseract OCR 生成。

**转换方法**：
- 有文本层的 PDF → `pdfminer.six` 直接抽取 + 内置 `(cid:)` 符号修复。
- **扫描件** → **`render_pages.py`（PDFium 渲染页面为 PNG，scale=4.0）** → `tesseract 5.3.4` OCR
  （`--psm 6`）→ `merge_ocr.py` 按页拼装。
- ⚠️ `convert.py` 有**扫描件防护**：抽不出正文时**跳过**，不覆盖已有的 OCR 文本。

> ⚠️ **重要教训（2026-10-07 实测）**：**提取 PDF 内嵌图像 ≠ 渲染页面**。
> `extract_img.py`（pypdf 提取内嵌图）在某些 1-bit CCITT 扫描件上会得到**完全不可读**的位图
> —— OCR 输出全页乱码（如 `Vi uBpre of tebtoqacpou`）。
> 换用 `render_pages.py`（PDFium 渲染）后同一页 OCR **完全正常**。
> ⇒ **扫描件一律用 `render_pages.py`**；`extract_img.py` 仅作备用。

**⚠️ 已知的转换局限**：
1. 扫描件 OCR 有识别错误（`Nand M` = `N and M`，下标/上标常丢失）。
2. 无 `ToUnicode` 表的字体会残留 `(cid:NNN)`（常见 `∑` 已修复；希腊字母仍有残留）。
3. arXiv 论文开头会混入页边竖排的 arXiv 编号栏（形如单字符行），是版面副产物，可忽略。

### ⭐ 更好的办法：直接读图（2026-10-07 老师确认）

**dsh + DeepSeek-V4.1-Flash 具备读图能力** ⇒ **不必依赖 OCR**：

- **扫描件**（Buneman 1971/1974）：直接读 `img/` 里的页面 JPG，公式与下标原样可读。
- **任意 PDF 的公式**：先 `python extract_img.py pdf/<某篇>.pdf img` 导出页面图，再直接读图。
- **`(cid:NNN)` 残留**：遇到时以读图为准，不要猜符号。

---
## 1. 速查表 A：T0 批（见 `HANDOVER.md` §4）

| 本库缺口 | 原始证明文献 | 状态 | 在 `md/` 中的位置 |
|---|---|---|---|
| **T0.1 `QuartetDecidesTree`** | **Colonius & Schulze 1981**（原始）<br>**Steel 1992** | ⚠️ 均付费墙 | 见 §5.1；**完整转述**见下两行 |
| ↑ 同一结果 | **Huber, Moulton, Semple, Wu 2018** | ✅ | `Huber2018_*.md` **§2 Theorem 1**（412 行） |
| ↑ 同一结果（thin/transitive/saturated） | **Huber et al. 2017 (arXiv:1702.00190)** | ✅ | `HuberEtAl2017_*.md` **§3 Theorem 6**（315 行） |
| **T0.2 Buneman 存在性** | **Buneman 1971**（原始） | ✅ **扫描件 + OCR** | `Buneman1971_*.md`（9 页） |
| ↑ 四点条件的图论证明 | **Buneman 1974** | ✅ **扫描件 + OCR** | `Buneman1974_*.md`（3 页） |
| ↑ split 分解 / Buneman 树 | **Bandelt & Dress 1986** | ✅ **新增** | `BandeltDress1986_*.md`（35 页） |
| **T0.3 `MaxZCherryCore`** | **Studier & Keppler 1988** | ⚠️ 付费墙 | 见 §5.1 |
| ↑ 同一结果（leaf-status 重证） | **Weller 2023 (arXiv:2305.18866)** | ✅ | `Weller2023_*.md` **Thm 1**（124）、**Thm 2**（378） |
| ↑ 同一结果（分析学重证） | **Mihaescu, Levy, Pachter 2006** | ✅ | `MihaescuLevyPachter2006_*.md` |
| ↑ NJ 的**抗噪**半径（后续目标 D1） | **Atteson 1999**；**Kuhner & Felsenstein 1994** | ✅ **KF 已下载** | `KuhnerFelsenstein1994_*.md` |
| **T0.4 NJst 一致性** | **Allman, Degnan, Rhodes 2016 (arXiv:1604.05364)** | ✅ | `AllmanDegnanRhodes2016_*.md` **Thm 4.1**（610） |
| **T0.5 SVDQuartets 可识别性** | **Chifman & Kubatko 2015 (arXiv:1406.4811)** | ✅ | `ChifmanKubatko2015_*.md` |
| （T2 前置）相容 ⟹ 存在树 | **Aho, Sagiv, Szymanski, Ullman 1981** | ✅ **新增** | `AhoSagivSzymanskiUllman1981_*.md`（17 页；算法在 393 行） |

---

## 2. 速查表 B：`NEXT.md` 的后续目标

> ✅ = 文献已在 `md/`；⚠️ = 仍在 §5.1 失败清单。

### 2.1 系统发生不变量（I 组）⭐ 老师最感兴趣

| 目标 | 文献 | 状态 | 关键内容 / 位置 |
|---|---|---|---|
| **I1 四点不变量**（Cavender–Felsenstein） | Cavender & Felsenstein (1987) | ⚠️ | 公式在 `Sturmfels2004_*.md`、`AllmanRhodes2006_*.md` 有完整转述 |
| **I2 Lake 线性不变量** | Lake (1987) | ⚠️ | **`CasanellasFernandezSanchez2011_*.md` §5.5 有完整转述** |
| **I3 Hadamard / Fourier 变换** | **Evans & Speed (1993)** | ✅ **老师下载** | `EvansSpeed1993_*.md`（23 页，扫描件 OCR）；正文 355–377 |
| ↑ 同一结果（toric 理想） | **Sturmfels & Sullivant (2005)** | ✅ | `SturmfelsSullivant2005_*.md`（JC/Kimura 的 Gröbner 基，次数 ≤ 4） |
| **I4 `rank ≤ 4` / 子式为零** | **Allman & Rhodes (2006)** | ✅ | `AllmanRhodes2006_*.md`：一般 Markov 模型的不变量理想；κ=2 时**全理想 = 3×3 子式生成** |
| **I5 不变量决定拓扑 / 构造不变量** | **Allman & Rhodes (2003)** | ✅ **老师下载** | `AllmanRhodes2003_*.md`（32 页）；**「某些矩阵必须交换 ⟹ 度数 κ+1 的不变量」** |
| **I6 edge invariants 足够** | **Casanellas & Fernández-Sánchez (2011)** | ✅ | `CasanellasFernandezSanchez2011_*.md`：**Buneman Splits-Equivalence 的代数类比**；§5 给了 JC/K2P/K3P/GM 的**四元集显式不变量** |
| **I7 toric 理想（见 I3）** | 同 Sturmfels–Sullivant | ✅ 同上 | — |
| （辅助）代数几何综述 | **Sturmfels (2004)** | ✅ | `Sturmfels2004_*.md`：问题清单 + 条件独立 ⟹ `5×5` 子式为零的构造 |
| （辅助）两状态 tripod | **Allman & Rhodes (2011)** | ✅ | `AllmanRhodes2011_TwoStateMarkovTripodTrees_*.md` |

### 2.2 溯祖理论基座（M 组）⭐ 老师要求「基座得建立起来」

| 目标 | 文献 | 状态 | 关键内容 / 位置 |
|---|---|---|---|
| **M1 4 元集 ILS 公式** | Tajima (1983)；Hudson (1983)；Pamilo–Nei (1988) | ⚠️ | **公式 `1−⅔e^{−t}` 在 `ChifmanKubatko2015_*.md` 有完整推导** |
| **M2 溯祖等待时间** | **Kingman (1982)** | ✅ **老师下载** | `Kingman1982_*.md`（14 页）：**n-coalescent 定义**（22 行）、**转移率**（59 行）、纯死亡过程分解 |
| **M4 site pattern 概率** | **Chifman & Kubatko (2015)** | ✅ | `ChifmanKubatko2015_*.md` |
| **M5 ASTRAL 局部支持** | **Sayyari & Mirarab (2016)** | ✅ | `SayyariMirarab2016_*.md`：**quartet 频率 ⟹ 局部后验概率 + 溯祖单位枝长** |
| **M6 STAR 推广** | **Allman, Degnan, Rhodes (2013)** | ✅ | `AllmanDegnanRhodes2013_STARGeneralizations_*.md` |
| **M6' NJst 一致性** | **ADR (2016)** | ✅ | `AllmanDegnanRhodes2016_*.md` |
| **M6'' split 概率** | **ADR (2017)** | ✅ | `AllmanDegnanRhodes2017_SplitProbabilitiesMSC_*.md`：**只用 split 分布** |
| **M7 基因树分布可算（COAL）** | **Degnan & Salter (2005)** | ✅ **老师下载** | `DegnanSalter2005_*.md`（14 页）：任意物种树的基因树拓扑分布递推 |
| **M8 unrooted ⟹ rooted** | **ADR (2011)** | ✅ | `AllmanDegnanRhodes2011_*.md`：≥5 物种时**无根**基因树分布识别**有根**物种树 |
| （辅助）ranked 基因树概率 | **Stadler & Degnan (2012)** | ✅ | `StadlerDegnan2012_*.md` |

### 2.3 supertree 与共识（C 组）⭐ 老师「也是」

| 目标 | 文献 | 状态 | 关键内容 / 位置 |
|---|---|---|---|
| **C1 严格/半严格共识** | **Day (1985)** | ✅ **老师下载** | `Day1985_*.md`（22 页）：**严格共识定义**（20 行）、`O(kn)` 算法（1421 行） |
| **C2 Adams 共识** | **Adams (1972)** | ✅ **老师下载** | `Adams1972_*.md`（9 页）：consensus method、nesting（39 行起） |
| **C3/C4 R\* 与贪心共识** | Bryant (2003) | ⚠️ | 综述，章节清晰 |
| **C5 共识公理化** | McMorris & Neumann 等 | ⚠️ | — |
| **C6 MinCut Supertree** | **Semple & Steel (2000)** | ✅ **老师下载** | `SempleSteel2000_*.md`（12 页）：**算法在 182/224 行**；修改 Aho 算法，图不连通时删最小割边集 |
| **C7 supertree 不存在性** | Steel, Dress & Böcker (2000) | ⚠️ | — |

### 2.4 低垂果实（F 组）

| 目标 | 文献 | 状态 | 关键内容 / 位置 |
|---|---|---|---|
| **F1 字符相容性定理** | **Estabrook, Johnson & McMorris (1976)** | ✅ **老师下载** | `EstabrookJohnsonMcMorris1976_*.md`（7 页）：**两两相容 ⟹ 全局相容**；二进制因子化 |
| ↑ 无向字符状态树版 | **Estabrook & Meacham (1979)** | ✅ **老师下载** | `EstabrookMeacham1979_*.md`（6 页） |
| **F2 严格共识** | = C1 | ✅ | — |
| **F3 KF 距离** | **Kuhner & Felsenstein (1994)** | ✅ **老师下载** | `KuhnerFelsenstein1994_*.md`（10 页） |
| **F4 JC 距离校正** | Jukes & Cantor (1969) | ⚠️ 书章 | **公式在 `Sturmfels2004_*.md`** |
| **F5 Lake 不变量** | = I2 | ⚠️ | — |
| **F6 Buneman 树 / split 分解** | **Buneman 1971**；**Bandelt & Dress 1986** | ✅ | 两篇均已在手 |
| **F7 rooted triplet（Aho 有根版）** | **Aho et al. (1981)**；Bryant & Steel (1995) | ✅ **Aho 已在手** | `AhoSagivSzymanskiUllman1981_*.md`；**Bryant–Steel 1995 见 §5.1（下错了篇）** |
| **F8 Fitch 一般树 / Sankoff** | Fitch (1971)；Sankoff (1975) | ⚠️ | — |
| **F9 严格共识的树空间性质** | = C1 | ✅ | — |

---

## 3. 已下载文献清单（30 篇）

### 3.1 本轮老师补充下载（12 篇，2026-10-07 14:19）

| # | `md/` 文件 | 主题 | 对应目标 |
|---|---|---|---|
| 1 | `AhoSagivSzymanskiUllman1981_InferringTreeLCA.md` | 相容约束 ⟹ 树（**本库 `Aho.lean` 的原出处**） | F7 / T2 前置 |
| 2 | `EstabrookJohnsonMcMorris1976_FoundationCladisticCharacterCompatibility.md` | **两两相容 ⟹ 全局相容** | **F1** |
| 3 | `BandeltDress1986_ReconstructingShapeOfTree.md` | **split 分解 / Buneman 树** | T0.2 / F6 |
| 4 | `Kingman1982_TheCoalescent.md` | **n-coalescent / 溯祖等待时间** | **M2** |
| 5 | `SempleSteel2000_MinCutSupertree.md` | **MINCUTSUPERTREE 算法** | **C6** |
| 6 | `KuhnerFelsenstein1994_SimulationComparison.md` | **KF branch score 距离** | **F3** |
| 7 | `Day1985_OptimalAlgorithmsComparingTrees.md` | **严格共识定义 + `O(kn)`** | **C1/F2** |
| 8 | `Adams1972_ConsensusTechniquesComparison.md` | **Adams 共识（nesting）** | **C2** |
| 9 | `DegnanSalter2005_GeneTreeDistributions.md` | **基因树拓扑分布递推（COAL）** | **M7** |
| 10 | `EvansSpeed1993_InvariantsProbabilityModels.md` | **Hadamard / Fourier 变换（扫描件）** | **I3** |
| 11 | `EstabrookMeacham1979_UndirectedCharacterStateTrees.md` | 无向字符状态树相容性 | F1 |
| 12 | `AllmanRhodes2003_PhyloInvariantsGeneralMarkov.md` | **构造不变量（矩阵交换）** | **I5** |

> ✅ **本批下载 13 个文件，12 篇有效**（编号 1–12）。
> ⚠️ 第 13 个（`1-s2.0-S0196885885710214-main.pdf`）**不是 Bryant & Steel 1995** ——
> 经 PDFium 渲染 + OCR 验证，它其实是 **Chamayou (1995), *Examples of Random Recurrences in Closed Form*,
> Adv. Appl. Math. 16:454–463**（同一卷、页码 454 vs 415，属同卷不同篇），与本项目无关，**已删除**。
> ⇒ **Bryant & Steel 1995 仍在 §5.1 待补**。

### 3.2 之前已下载（18 篇）

| # | `md/` 文件 | 主题 | 对应目标 |
|---|---|---|---|
| 1 | `Buneman1971_RecoveryOfTreesFromDissimilarity.md` | 相容性判据、Splits-Equivalence | T0.2 / F6 |
| 2 | `Buneman1974_MetricPropertiesOfTrees.md` | **四点条件 ⟹ 树度量** | **T0.2** |
| 3 | `Weller2023_NeighborJoining_LeafStatus.md` | NJ leaf-status | **T0.3** |
| 4 | `MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md` | NJ 正确性 | T0.3 |
| 5 | `HuberEtAl2017_SymbolicTernaryMetrics.md` | **quartet 系统 thin/transitive/saturated** | **T0.1** |
| 6 | `Huber2018_QuarnetRules_Level1Networks.md` | Colonius–Schultze 推理规则 | T0.1 / N3 |
| 7 | `AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md` | NJst 一致性 | **T0.4** |
| 8 | `ChifmanKubatko2015_IdentifiabilityarXiv1406.4811.md` | SVDQuartets 可识别性 + **ILS 概率推导** | T0.5 / **M1** |
| 9 | `SturmfelsSullivant2005_ToricIdealsPhyloInvariants.md` | **toric 理想 / Gröbner 基** | **I3/I7** |
| 10 | `AllmanRhodes2006_PhyloIdealsVarietiesGeneralMarkov.md` | （见 3.1 #7） | I4 |
| 11 | `CasanellasFernandezSanchez2011_RelevantInvariants.md` | **edge invariants 足够（代数版 Buneman 定理）** | **I6** |
| 12 | `Sturmfels2004_PhylogeneticAlgebraicGeometry.md` | 代数几何综述 + 问题清单 | I1/辅助 |
| 13 | `AllmanRhodes2011_TwoStateMarkovTripodTrees.md` | 两状态 tripod 模型代数分析 | I/辅助 |
| 14 | `SayyariMirarab2016_ASTRALLocalSupport.md` | **quartet 频率 ⟹ 局部后验 + 枝长** | **M5** |
| 15 | `AllmanDegnanRhodes2013_STARGeneralizations.md` | STAR 推广一致性 | **M6** |
| 16 | `AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md` | MSC 下的 **split 概率** | **M6** |
| 17 | `AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md` | 无根基因树 ⟹ 有根物种树 | **M8** |
| 18 | `StadlerDegnan2012_RankedGeneTreeProbability.md` | ranked 基因树概率 | M2/M7 辅助 |

## 4. 复现方法

```bash
# 虚拟环境（已建好，含 pdfminer.six / pypdf / pypdfium2 / Pillow）
PY=/c/Users/ASTER/.workbuddy/binaries/python/envs/default/Scripts/python.exe

# ① 有文本层的 PDF → Markdown（内置符号修复 + 扫描件防护，扫描件会自动跳过）
"$PY" convert.py pdf md

# ② 扫描件：用 PDFium 渲染页面为 PNG（★ 优于 extract_img.py）
"$PY" render_pages.py pdf/EvansSpeed1993_InvariantsProbabilityModels.pdf img 4.0
#   （scale: 2.0≈144dpi，3.0≈216dpi，4.0≈288dpi；扫描件建议 4.0）

# ③ OCR（走 WSL 的 tesseract 5.3.4）
wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/references && \
  for f in img/EvansSpeed1993_*.png; do b="${f%.*}"; b="${b#img/}"; \
  tesseract "$f" "ocr/$b" -l eng --psm 6; done'

# ④ 把 ocr/ 的逐页文本合并成可读 Markdown
"$PY" merge_ocr.py EvansSpeed1993_InvariantsProbabilityModels \
  "Evans & Speed 1993 — Invariants of Some Probability Models Used in Phylogenetic Inference" \
  "Ann. Statist. 21(1):355–377."

# ⑤（可选）单独修复数学符号残留
"$PY" cleanup.py
```

**一步到位的渲染 + OCR（WSL 内）**：

```bash
wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/references && \
  PY=/mnt/c/Users/ASTER/.workbuddy/binaries/python/envs/default/Scripts/python.exe && \
  "$PY" render_pages.py pdf/<某篇>.pdf img 4.0 && \
  for f in img/<某篇>_*.png; do b="${f%.*}"; b="${b#img/}"; \
    tesseract "$f" "ocr/$b" -l eng --psm 6; done'
```

---

## 5. ⚠️ 未能下载的文献（付费墙）—— 附链接

### 5.1 仍需下载（付费墙）—— 老师可自行下载

> ✅ **2026-10-07 更新**：老师已补充下载 **12 篇**（见 §3.1），下列清单已相应缩短。
> 剩余项**多数不阻塞推进** —— 关键公式/证明已在`md/` 已有文献中（见「说明」列）。

| 文献 | 链接 | 说明 |
|---|---|---|
| **Bryant & Steel 1995**<br>*Extension operations on sets of leaf-labelled trees*<br>Adv. Appl. Math. 16(4):415–430 | <https://doi.org/10.1006/aama.1995.1021> | **F7 rooted triplet**。⚠️ **2026-10-07 曾下错**（同卷拿到 Chamayou 1995 的 454–463 页），**需重新下载**：请注意页码应为 **415–430** |
| **Colonius & Schulze 1981**<br>*Tree structures for proximity data*<br>Br. J. Math. Stat. Psychol. 34:167–180 | <https://doi.org/10.1111/j.2044-8317.1981.tb00626.x> | **T0.1 的原始出处**。结果已由 `Huber2018_*.md` / `HuberEtAl2017_*.md` 完整转述 |
| **Steel 1992**<br>*The complexity of reconstructing trees from qualitative characters and subtrees*<br>J. Classification 9:91–116 | <https://doi.org/10.1007/BF02618470> | 完整 quartet 系统决定树（正方向）。复杂度部分（NP-complete）已降级 |
| **Studier & Keppler 1988**<br>*A note on the neighbor-joining algorithm of Saitou and Nei*<br>Mol. Biol. Evol. 5(6):729–731 | <https://doi.org/10.1093/oxfordjournals.molbev.a040527><br>PubMed: <https://pubmed.ncbi.nlm.nih.gov/3221794/> | NJ 的**首个正确证明**。⚠️ 出版社 CDN 返回错误文件。内容已被 `Weller2023` / `MihaescuLevyPachter2006` 覆盖 |
| **Saitou & Nei 1987**<br>*The neighbor-joining method*<br>Mol. Biol. Evol. 4(4):406–425 | <https://doi.org/10.1093/oxfordjournals.molbev.a040454> | NJ 原算法（其正确性证明有误，见 Studier–Keppler） |
| **Margush & McMorris 1981**<br>*Consensus n-trees*<br>Bull. Math. Biol. 43(2):239–244 | <https://doi.org/10.1016/S0092-8240(81)90019-7> | 多数共识树（本库 `Phylo/Consensus.lean` 的原始出处） |
| **Cavender & Felsenstein 1987**<br>*Invariants of phylogenies in a simple case with discrete states*<br>J. Classification 4:57–71 | <https://doi.org/10.1007/BF01890075> | **I1 四点不变量的原始出处**。⚠️ **公式已在 `Sturmfels2004_*.md` / `AllmanRhodes2006_*.md` 有完整转述** |
| **Lake 1987**<br>*A rate-independent technique…: evolutionary parsimony*<br>Mol. Biol. Evol. 4(2):167–191 | <https://doi.org/10.1093/oxfordjournals.molbev.a040433> | **I2 Lake 线性不变量**。⚠️ **已在 `CasanellasFernandezSanchez2011_*.md` §5.5 有完整转述** |
| **Tajima 1983**<br>*Evolutionary relationship of DNA sequences in finite populations*<br>Genetics 105(2):437–460 | <https://doi.org/10.1093/genetics/105.2.437><br>PMC 综述：<https://pmc.ncbi.nlm.nih.gov/articles/PMC5068832/> | **M1 ILS 公式**（也是首次提出 ILS）。⚠️ 公式在 `ChifmanKubatko2015_*.md` 有推导 |
| **Hudson 1983**<br>*Testing the constant-rate neutral allele model with protein sequence data*<br>Evolution 37(1):203–217 | <https://doi.org/10.1111/j.1558-5646.1983.tb05528.x> | **M1 ILS 公式**（独立发现） |
| **Kingman 1982b**<br>*On the genealogy of large populations*<br>J. Appl. Prob. 19A:27–43 | <https://doi.org/10.1017/S0021900200039176> | M2 另一版本（**首次描述溯祖**）。⚠️ 1982a 已下载，**此项可缓** |
| **Bryant 2003**<br>*A classification of consensus methods for phylogenetics*<br>DIMACS Series 61:163–184 | <https://doi.org/10.1090/dimacs/061/12> | **C3/C4 R\* 与贪心共识**。作者主页可能免费：<https://www.math.otago.ac.nz/>（David Bryant） |
| **Steel, Dress & Böcker 2000**<br>*Basic properties of supertrees*<br>Syst. Biol. | <https://doi.org/10.1080/106351500750047161> | **C7 supertree 不存在性** |
| **Meacham 1981**<br>*Compatibility analysis of phylogenetic data* | 见已下载的 `EstabrookMeacham1979_*.md` | F1 补充（**1979 版已在手，此版可缓**） |
| **Fitch 1971**<br>*Toward defining the course of evolution…*<br>Syst. Zool. 20(4):406–416 | <https://doi.org/10.2307/2412116> | **F8 Fitch 一般树**。⚠️ 本库已有 4 元集版（`fitchCost_eq`） |
| **Sankoff 1975**<br>*Minimal mutation trees of sequences*<br>SIAM J. Appl. Math. 28(1):35–42 | <https://doi.org/10.1137/0128004> | **F8 Sankoff 算法** |
| **Jukes & Cantor 1969**<br>*Evolution of protein molecules*<br>In: Mammalian Protein Metabolism, pp. 21–132 | 书章（无 DOI）：<https://doi.org/10.1016/B978-1-4832-3211-9.50009-7> | **F4 JC 距离校正**。⚠️ 公式已明确：`d = −¾·ln(1 − 4p/3)`；**不阻塞** |
| **Atteson 1999**<br>*The performance of neighbor-joining methods of phylogenetic reconstruction*<br>Algorithmica 25:251–278 | <https://doi.org/10.1007/PL00008277> | **D1 Atteson 安全半径 1/2**。⚠️ 定理陈述在 `MihaescuLevyPachter2006_*.md` **Theorem 2** 有完整给出 |

**注**：`Kuhner & Felsenstein 1994` 的 KF 公式（F3）已由本次下载覆盖，公式为
`KF(T,T') = √( Σ_e (w_e − w'_e)² )`（`e` 遍历两树全部边，缺失边权取 0；
即树向量 = split 权重向量的 `L²` 距离）。


### 5.2 教科书（最佳单一来源）

**Semple & Steel, *Phylogenetics* (2003), Oxford University Press** —— 上述多条结果的统一叙述处：
- **§3.8** Splits-Equivalence
- **§6.4** quartet 系统与 C–S 推理规则（= **T0.1**）
- **§7.2** 四点条件 / Buneman 定理（= **T0.2**）

**Steel, *Phylogeny: Discrete and Random Processes in Evolution* (2016), SIAM** ——
不变量（**I 组**）与溯祖（**M 组**）的权威综述。

> 💡 **重要结论**：**多数「下载失败」条目的关键公式/证明已在已下载的文献中有完整转述**
> —— 例如 I1/I2 在 `Sturmfels2004` / `AllmanRhodes2006` / `Casanellas2011` 中，
> M1 在 `ChifmanKubatko2015` 中，T0.1 在 `Huber2018` / `HuberEtAl2017` 中。
> ⇒ **不阻塞形式化推进**；付费墙文献只在需要「原始出处」时才有必要。
