/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Cycle.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Copied.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeSemantics
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldEncoderAppendClosure

/-! # Complete direct final inherited ring-atom codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Complete inherited base-nine code column in canonical copied-plus-cycle
occurrence order. -/
def directSourceFinalInheritedRingAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCopiedInheritedRingAtomCodes decider symbols ++
    directSourceFinalCycleInheritedRingAtomCodes decider symbols

@[simp] theorem directSourceFinalInheritedRingAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalInheritedRingAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalInheritedRingAtomCodes, List.length_append,
    directSourceFinalCopiedInheritedRingAtomCodes_length,
    directSourceFinalCycleInheritedRingAtomCodes_length,
    directSourceFinalCompiledOccurrenceData_eq_copied_cycle,
    List.length_append]

/-- The complete inherited ring-code column is polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalInheritedRingAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInheritedRingAtomCodes decider) := by
  unfold directSourceFinalInheritedRingAtomCodes
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCopiedInheritedRingAtomCodesComputableInPolyTime
      decider)
    (directSourceFinalCycleInheritedRingAtomCodesComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
