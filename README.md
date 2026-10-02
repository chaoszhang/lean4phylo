# lean4phylo

系统发生学（phylogenetics）经典算法的形式化库 —— 用 Lean 4 建立**可机检**的证明。

> 名字双关：**Lean 4** phylo ／ **lean for** phylo。

## 目标

把系统发生学的经典定义与算法（树 / split / quartet / 树度量 / NJ / UPGMA / 树比较……）
形式化进 Lean 4，最终形成**所有经典算法证明的库**。

## 结构

| 路径 | 内容 | 状态 |
|---|---|---|
| `Phylo/Core.lean` | **cladogram**（树载体）与基础引理 | M0 🚧 |
| `Phylo/Split.lean` | split 系统 · 相容性 · **Splits-Equivalence** | M2 计划 |
| `Phylo/Metric.lean` | 树度量 · 四点条件 · **Buneman** | M3 计划 |
| `Phylo/Quartet.lean` | quartet / triplet · `Topology` | M4 计划 |
| `Phylo/Algorithm/` | NJ / UPGMA / 树比较（RF·KF·BHV） | M5 计划 |
| `Phylo/Mathlib/` | Mathlib 尚未提供、本库自建的声明（便于将来回灌） | 备用 |

## 快速开始

```bash
lake exe cache get    # 下载 mathlib 预编译缓存（首次必需；否则要编译数小时）
lake build
```

在 VS Code 中打开**目录**（不是单个文件）以获得完整补全。

## 设计文档

- `CONCEPTS.md` —— 概念清单 · 文献先例定义 · 10 条形式化决策 · 里程碑
- `SCAFFOLD.md` —— 工程骨架（模板调研 + 落地清单）
- `MEMORY.md` —— 项目长期记忆

## 里程碑

```
M0 树载体 → M1 加权层+同构 → M2 Splits-Equivalence ★ → M3 Buneman ★ → M4 quartet/triplet → M5 算法
```
