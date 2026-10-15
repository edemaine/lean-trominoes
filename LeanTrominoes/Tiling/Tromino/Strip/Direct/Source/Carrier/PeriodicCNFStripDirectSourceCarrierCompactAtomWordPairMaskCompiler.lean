/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Numeric.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankOrderedRetainedPairCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Direct compiler for the retained carrier-pair mask -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The global-rank mask selecting retained adjacent carrier links is
computable in polynomial time. -/
noncomputable def directSourceCarrierRetainedPairMaskComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierRetainedPairMask decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierRankOrderedPairs.retainedMaskBitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
