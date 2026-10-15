/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Numeric.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Variable.PeriodicCNFStripDirectSourceVariableDecidableEqInstance
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankGlobalCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiler for direct-source global carrier ranks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


attribute [local instance] directSourceVariableDecidableEqInstance

noncomputable abbrev directSourceCarrierGlobalRanksComputableInPolyTime :=
  TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierRankGlobal.ranksComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
