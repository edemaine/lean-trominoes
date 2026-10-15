/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceMaskCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryCompiler
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Copied.RetainedAngularFanFinalCopiedClauseQueryCompiler
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Compiling fallback-family occurrence-slot masks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile the complete five-family occurrence mask with independently
chosen carrier and bend values. -/
noncomputable def
    directSourceFinalFallbackOccurrenceMaskComputableInPolyTime
    (carrierActive bendActive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool
      id id
      (directSourceFinalFallbackOccurrenceMask
        decider carrierActive bendActive) := by
  unfold directSourceFinalFallbackOccurrenceMask
  exact TM2ListAppend.nativeComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime
        (directRetainedFinalCrossoverClauseQueriesComputableInPolyTime decider)
        retainedFinalCopiedClauseDescriptorsComputableInPolyTime)
      (descriptorOccurrenceMaskComputableInPolyTime false))
    (directSourceFinalCarrierOccurrenceMaskSuffixComputableInPolyTime
      decider carrierActive bendActive)

end LeanTrominoes.PeriodicCNFStripReduction

end
