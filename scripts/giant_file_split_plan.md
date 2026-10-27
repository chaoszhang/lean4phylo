# 巨型文件拆分方案（W39-6）—— **只出方案，不落地**

> **状态**：📄 **方案**。本轮**一个文件都没拆**（派单：拆巨型文件落地要老师批）。
> **实测日期**：2026-10-27（W39）。行号是当次实测；拆之前必须重取（会漂）。
> **对象**：`Phylo/Stat/BunemanIndexBridge.lean`（**6072** 行）＞ `Phylo/Stat/ReciprocalMonophyly.lean`
> （**5220**）＞ `Phylo/Stat/HookLength.lean`（**5126**）。三者合计 16 418 行 ≈ 全库 `Phylo/` 的 22%。

## 0. 先说清「为什么拆」和「拆什么不算拆」

* 目的不是美观，是**单文件编译成本**与**改动冲突面**：一个 6000 行文件里改一行，`lake` 要重编整个
  模块（`BunemanIndexBridge` 单文件 ~20 s），且任何两个泳道并行动同一文件必冲突。
* **纯搬运**（pure move）= 只做「剪切 → 粘到新文件 → 补 import / namespace / variable / open」，
  **不新增、不删除、不改写任何 `def`/`theorem` 的陈述与证明**。
* ⚠ **★D 更正（派单措辞）**：派单的验收标准写「job 数 / 模块数 / 台账 72 / 三脚本全不变」。
  `job 数` 与 `模块数` **必然**会变 —— 拆一个文件就是 +1 个模块、+1 个 build job。正确的不变式是：
  **增量恰好等于新增模块数**（拆 1 刀 ⇒ 3988 → 3989、模块 156 → 157），而**台账 72** 与
  **三脚本（`list_gaps` / `check_vacuous` / `check_refuted`）的输出**必须**逐字**不变。

## 1. 三个文件的结构（实测小节边界）

**`BunemanIndexBridge.lean`（6072）** —— 61 个小节，主题上分三大块：

| 块 | 行段 | 内容 | 行数 |
|---|---|---|---|
| A | 77–2063（§1–§8.9） | `bunemanIndex = α`、各瓶颈的**证伪**、`SplitPrime` 不可满足、隔离指数器材 | 1987 |
| B | 2064–3301（§9–§12.3） | `bSep` 计算核心、(B2) 加法核心、(B1) 收口、`fourPointCharacterization` 各半边 | 1238 |
| C | 3302–6072（§4.2 ＋ §8.10–§8.16） | **BdD Thm 2 收官**：权重层、`canonicalSplitDecomposition_gap_holds`、最终形态 | 2771 |

⚠ 小节编号本身已经乱了：`§4.2` 出现在 3302（离 §4 有 3000 行）、`§8.12`/`§8.13` 各出现两次。
拆的时候顺手重编号是**额外收益**，但**不算纯搬运**（要单独一刀）。

**`ReciprocalMonophyly.lean`（5220）**

| 块 | 行段 | 内容 | 行数 |
|---|---|---|---|
| A | 167–1157（§3–§7） | 闭形式、算术恒等式、树层、显式缺口 | 991 |
| B | 1158–2414（§8–§10） | `MSCTreeLaw n` 容器、去根桥、`rootedToCladogram` | 1257 |
| C | 2415–5220（§11–§13） | 一般 `n` 的权重层、split 族载体、`n ≤ 2` 基例、away 侧、三事件分解 | 2806 |

**`HookLength.lean`（5126）**

| 块 | 行段 | 内容 | 行数 |
|---|---|---|---|
| A | 121–983（§1–§12） | 钩长、`LE`、**hook-length 公式本体**`LE · ∏s = N!`、与纤维数对上 | 863 |
| B | 984–2582（§13–§14.7） | `cladesOf` 的 (O2)/(O1) 器材、层分解无重、创建序 | 1599 |
| C | 2583–5120（§15–§23） | `LinExt`、(O1) 的 ≤/≥ 两半、交错引理、洗牌双射、`LinExt = LE`、**收口** | 2538 |

## 2. **第一刀切哪个：`HookLength.lean` 在 `§15` 前（行 2583）切开**

```
Phylo/Stat/HookLength.lean            5126 → 2582 行   （§1–§14.7）
Phylo/Stat/LinExt.lean                 新增 2538 行    （§15–§23，第 2583 行起整块搬走）
```

**为什么是它（而不是最大的那个）**：三者里它**唯一满足全部四条「搬运零风险」**：

1. **`private` 声明：0 条**（三个文件都是 0，这条是共同前提）；
2. **`:NNN` 自引用行号：0 条** —— `BunemanIndexBridge` 有 **89** 条、`ReciprocalMonophyly` 有 **86** 条
   docstring 里写着本文件的 `:NNN`，搬完必须**逐条重解析重写**（这才是拆分真正的成本）；
   `HookLength` 一条都没有 ⇒ 搬完不会有一处引用失真；
3. **单 `namespace`、单 `variable` 作用域**：`namespace Phylo.Stat.HookLength`（115）到 `end`（5120），
   中间没有嵌套 namespace；`variable {α} [DecidableEq α]`（119）一条到底；
4. **切点两侧均衡**：2582 / 2538（最大的 `BunemanIndexBridge` 无论怎么切都有 2700+ 的一半）。

**新文件 `Phylo/Stat/LinExt.lean` 的骨架**（纯搬运必写的四件事）：

```lean
import Phylo.Stat.HookLength          -- ① 依赖方向：尾块 import 头块（反向会成环）
open Classical                         -- ② 头文件的 `open Classical`（117）
open Phylo.Stat.RankedGeneTree         -- ③ 头文件里**非 `in` 作用域**的那条 open（918）
namespace Phylo.Stat.HookLength        -- ④ 命名空间必须重开（否则名字全变，台账与脚本全红）
variable {α : Type*} [DecidableEq α]
...（§15–§23 原文，一字不改）
end Phylo.Stat.HookLength
```

`Phylo.lean` 只需插一行（按字母序）：`import Phylo.Stat.LinExt`（在 `Phylo.Stat.KmatNonneg` 之后、
`Phylo.Stat.MSCMeasure` 之前）。

## 3. 后续两刀（同一策略，等第一刀验收通过再做）

| 顺序 | 文件 | 切点 | 结果 | 新模块名 |
|---|---|---|---|---|
| ② | `BunemanIndexBridge.lean` | **行 3302（`§4.2` 前）** | 3301 ＋ 2771 | `Phylo/Stat/CanonicalSplitDecomposition.lean` |
| ③ | `ReciprocalMonophyly.lean` | **行 2415（`§11` 前）** | 2414 ＋ 2806 | `Phylo/Stat/YHKWeightLayer.lean` |

② 的额外工作：`universe u` 在 3745/4470/5090/… 出现多次，搬走的那块要从**块内那一条**开始
（在 3302 起的新文件里补 `universe u`），否则 `u` 未声明；`open Finset`（60）要重开。
③ 的额外工作：`noncomputable section`（161）、`open Classical`（163）要重开；
`instance {n} (L : MSCTreeLaw n) : Fintype L.Ω`（1228）留在头块，尾块 import 头块即可用。

**三刀全做完之后**：最大单文件从 **6072 → 3301**（`BunemanIndexBridge`）／2771／2806，
全库 job 数 3988 → **3991**、模块数 156 → **159**。

## 4. 纯搬运的**验收标准**（每刀都要逐项跑）

| # | 验收项 | 期望 | 怎么测 |
|---|---|---|---|
| 1 | build | `lake build Phylo` **EXIT 0** | `bash ~/w28/build.sh` |
| 2 | job 数 | **3988 ＋ 新增模块数**（每刀 +1，三刀 +3 = 3991） | 同上，末行 `Build completed successfully (N jobs)` |
| 3 | 模块数 | 156 ＋ 新增（每刀 +1） | `grep -c '^import' Phylo.lean` |
| 4 | 七桶台账 | 仍 **72**：真开放 1 / 已收口 38 / 条件收口 2 / 已证伪 17 / 追溯 6 / 判定收档 7 / 长期开放 1（W40 降级后口径） | `bash scripts/list_gaps.sh B` |
| 5 | `check_vacuous.sh` | **44/44**，VERDICT ✓（它用 `grep -F` 名字与字面量，**不依赖行号** ⇒ 搬家不该让它变） | `bash scripts/check_vacuous.sh` |
| 6 | `check_refuted.sh` | 21/21 ✓ | `bash scripts/check_refuted.sh` |
| 7 | `check_file_imports` | EXIT 0 | `bash scripts/check_file_imports.sh` |
| 8 | 声明集合 | 搬迁前后**同一声明集合**：`grep -hE '^(theorem|lemma|def|abbrev|instance|structure|inductive) '` 两边拼起来排序后**逐字相同** | 一条 `awk` 管道即可 |
| 9 | 无残留 | 头文件里不留任何只被尾块使用的辅助定义（反之亦然） | 靠 1/2 通过 + 人工过一遍 `#check` 名单 |

★ 第 8 项是「纯搬运」的**定义式验收**：只有它成立，才能说「没顺手改数学」。

## 5. 风险（按严重度）

1. **`private` 跨模块**：三个文件当前都是 **0 条 `private`** ⇒ **这条风险现在是零**，
   但**每刀之前必须重测**（`grep -c '^private' <file>`）；一旦有人加了 `private` 又被另一块用到，
   纯搬运就会失败，只能把它升为 public —— **那就不再是纯搬运**，必须单独报批。
2. **`:NNN` 自引用漂移**（最大成本）：`BunemanIndexBridge` **89** 条、`ReciprocalMonophyly` **86** 条、
   `HookLength` **0** 条。搬完必须**逐条重解析**（每条都要在搬后的文件里 `grep -n` 找真身），
   否则 docstring 全部失真 —— 这正是第 2 刀、第 3 刀比第 1 刀贵一个数量级的原因。
3. **`namespace` / `variable` / `open` 作用域**：切点若落在 `section` 或 `namespace` 内部，尾块会丢上下文，
   编译报「unknown identifier」。实测三个文件的 `section`/`namespace` 都是**顶格单层**，
   但 `BunemanIndexBridge` 在 4432/4569/5065/… 有 `end Split` / 再 `namespace Split` 的开关，
   切点 3302 落在第 1 个 `namespace Split`（62–4432）内部 ⇒ 新文件必须**重开 `namespace Split`** 并补齐 `open Finset`。
4. **`omit … in` 孤儿**：`omit [Fintype X] [DecidableEq X] in` 是**下一条声明**的修饰。
   切点若正好落在 `omit … in` 与它的声明之间，搬运会把它切成孤儿 ⇒ **切点必须落在小节标题行，
   不许落在 `omit` 与其目标声明之间**（§ 标题是安全边界）。
5. **`set_option … in` 同理**：同一原则（切点只落在 `/-! ## …` 行）。
6. **`docstring 跨节引用`**：大量 docstring 写「见 §8.3」「见 `:3358`」；搬家后 `§` 编号会变，
   要么重编号（非纯搬运），要么在文件头加一张「旧 § → 新模块」对照表（**推荐后者**，属纯搬运的安全附加）。
7. **`Phylo.lean` 的字母序**：import 列表是人工维护的字母序，插错位置不影响编译但不合规范；
   插完用 `LC_ALL=C sort -c` 验顺序。
8. **编译时间回归**：拆完之后**增量**编译更快，但**全量**编译会因为多一个模块**略慢**。
   这是预期代价，不算回归；第 2 项验收只钉「job 数增量 = 模块增量」。

## 6. 明确**不做**的事

* 不做任何**重命名**（改动台账名字 = 静默删债，W36 已定纪律）；
* 不顺手**重编号 §**（那是独立的一刀，需要单独批）；
* 不顺手**订正 docstring 表述**（同理，独立一刀）；
* 不在同一刀里搬**两个**块（一刀只切一次，才能让「纯搬运」可验收）。
