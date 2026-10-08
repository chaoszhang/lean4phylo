/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Aho
import Phylo.Algorithm.BinaryCount
import Phylo.Algorithm.Cherry
import Phylo.Algorithm.NJ
import Phylo.Algorithm.NJHardCore
import Phylo.Algorithm.NNI
import Phylo.Algorithm.RF
import Phylo.Algorithm.UPGMA
import Phylo.Binary
import Phylo.Buneman
import Phylo.BunemanGraft
import Phylo.BunemanShrinkPD
import Phylo.BunemanTree
import Phylo.CherryQuartet
import Phylo.Compatibility
import Phylo.Consensus
import Phylo.ContractCount
import Phylo.Core
import Phylo.Dendrogram
import Phylo.DissimilarityPerturb
import Phylo.Distance
import Phylo.DistanceCorrection
import Phylo.InductiveAssembly
import Phylo.InternalEdge
import Phylo.JukesCantor
import Phylo.LakeInvariants
import Phylo.Laminar
import Phylo.LaminarCount
import Phylo.LeafStatus
import Phylo.Mathlib.Walk
import Phylo.PhylogramContract
import Phylo.PositiveRealization
import Phylo.Quartet
import Phylo.QuartetInhabitation
import Phylo.QuartetUnique
import Phylo.RootedTriplet
import Phylo.SideSubtree
import Phylo.Split
import Phylo.SplitsDetermineTree
import Phylo.SplitsDetermineTreeBase
import Phylo.SplitsMaximal
import Phylo.Stat.ASTRAL
import Phylo.Stat.CASTER
import Phylo.Stat.MSC
import Phylo.Stat.NJst
import Phylo.Stat.NJstWitness
import Phylo.Stat.Parsimony
import Phylo.Stat.QuartetDecides
import Phylo.Stat.Stability
import Phylo.Stat.SVDQuartets
import Phylo.Supertree
import Phylo.TreeDistance

/-!
# `lean4phylo` —— 系统发生学经典算法的形式化库

根模块：按字母序 import 库内全部模块。
参见 `CONCEPTS.md`（概念设计）、`SCAFFOLD.md`（工程骨架）。
-/
