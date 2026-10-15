/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Copied.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedLocalAtomCodeCompiler

/-! # Direct parent-indexed copied local atom codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Numeric parent-indexed identities for all local positions in the direct
copied occurrence prefix. -/
def directSourceFinalCopiedLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- The local-code column stays aligned with the exact copied occurrence
stream. -/
theorem directSourceFinalCopiedLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedLocalAtomCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedLocalAtomCodes
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes_length _

/-- Direct local atom identities are polynomial-time computable as unary
fields. -/
noncomputable def
    directSourceFinalCopiedLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedLocalAtomCodes decider) := by
  unfold directSourceFinalCopiedLocalAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
