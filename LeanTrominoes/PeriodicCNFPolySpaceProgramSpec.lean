/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramResetRelation
import LeanTrominoes.PeriodicCNFPolySpaceNativeCompiler

/-!
# Normalized request-printer specification for a polynomial-space decider

The request generator now has an expression-free target.  For a direct list
of finite source symbols, this file instantiates the normalized bounded TM2
program, prefixes its exact instruction-derived clause count and affine fresh
boundary, and proves that the resulting natural fields are exactly the compact
request already consumed by the verified structural evaluator.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceProgramSpec

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Direct postorder instruction word for the source-symbol instance. -/
def program (symbols : List encoding.Γ) : TransitionProgram.Program :=
  BoundedMachineProgram.designatedMachineResetClock
    (tm := decider.tm)
    (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
    (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)
    (PolySpaceCompiler.initialConfigurationOfSymbols decider symbols)
    (PolySpaceReduction.acceptingConfiguration decider)

/-- Affine first fresh Tseitin atom for the source-symbol instance. -/
def fresh (symbols : List encoding.Γ) : Nat :=
  BoundedMachineAtom.atomCount (tm := decider.tm)
    (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
    (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)

/-- Exact natural fields to be emitted by the concrete request printer. -/
def fields (symbols : List encoding.Γ) : List Nat :=
  (TransitionProgram.clauseCount (program decider symbols) + 1) ::
    fresh decider symbols ::
      transitionProgramFields (program decider symbols)

@[simp]
theorem sourceCompilerRequest_program (symbols : List encoding.Γ) :
    (PolySpaceNativeCompiler.sourceCompilerRequest decider
      symbols).expression.program = program decider symbols := by
  rw [PolySpaceNativeCompiler.sourceCompilerRequest_expression]
  exact BoundedMachineProgram.program_designatedMachineResetClock _ _

@[simp]
theorem sourceCompilerRequest_fresh (symbols : List encoding.Γ) :
    (PolySpaceNativeCompiler.sourceCompilerRequest decider symbols).fresh =
      fresh decider symbols := by
  exact PolySpaceNativeCompiler.sourceCompilerRequest_fresh decider symbols

/-- The normalized field specification is the evaluator's semantic compact
request, field for field. -/
theorem fields_eq_transitionCompilerInputFields
    (symbols : List encoding.Γ) :
    fields decider symbols =
      transitionCompilerInputFields
        (PolySpaceNativeCompiler.sourceCompilerRequest decider
          symbols).expression
        (PolySpaceNativeCompiler.sourceCompilerRequest decider
          symbols).fresh := by
  unfold fields transitionCompilerInputFields
  rw [sourceCompilerRequest_program, sourceCompilerRequest_fresh]
  rw [← TransitionExpr.TransitionProgram.clauseCount_program
    (PolySpaceNativeCompiler.sourceCompilerRequest decider
      symbols).expression]
  rw [sourceCompilerRequest_program]

/-- The normalized fields are exactly the pre-existing native frontend
request on source fields. -/
@[simp]
theorem fields_eq_nativeCompilerProgramInput (symbols : List encoding.Γ) :
    fields decider symbols =
      PolySpaceNativeCompiler.nativeCompilerProgramInput decider
        (FiniteEncodingNativeFields.fields symbols) := by
  rw [fields_eq_transitionCompilerInputFields]
  rfl

/-- Encoding the normalized field specification gives the exact semantic
request encoding consumed by the evaluator. -/
@[simp]
theorem trList_fields (symbols : List encoding.Γ) :
    PartrecToTM2.trList (fields decider symbols) =
      (PolySpaceNativeCompiler.sourceCompilerRequest decider symbols).encode := by
  rw [fields_eq_nativeCompilerProgramInput,
    PolySpaceNativeCompiler.sourceCompilerRequest_encode]

end PolySpaceProgramSpec
end PeriodicCNF
end LeanTrominoes
