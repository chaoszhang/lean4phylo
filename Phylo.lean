/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Aho
import Phylo.Algorithm.BinaryCount
import Phylo.Algorithm.Cherry
import Phylo.Algorithm.NJ
import Phylo.Algorithm.NNI
import Phylo.Algorithm.RF
import Phylo.Algorithm.UPGMA
import Phylo.Binary
import Phylo.Consensus
import Phylo.Core
import Phylo.Dendrogram
import Phylo.Distance
import Phylo.Laminar
import Phylo.Mathlib.Walk
import Phylo.Quartet
import Phylo.QuartetUnique
import Phylo.SideSubtree
import Phylo.Split
import Phylo.Stat.ASTRAL
import Phylo.Stat.CASTER
import Phylo.Stat.MSC
import Phylo.Stat.NJst
import Phylo.Stat.Parsimony
import Phylo.Stat.QuartetDecides
import Phylo.Stat.Stability
import Phylo.Stat.SVDQuartets

/-!
# `lean4phylo` —— 系统发生学经典算法的形式化库

根模块：按字母序 import 库内全部模块。
参见 `CONCEPTS.md`（概念设计）、`SCAFFOLD.md`（工程骨架）。
-/
