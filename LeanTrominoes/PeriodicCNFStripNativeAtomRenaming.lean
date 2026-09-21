/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OccurrenceIdentityRenaming
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceStableRankHorizontalSemantics
import LeanTrominoes.PeriodicExactOneInjectiveRenaming

/-! # Native numeric atom names for the compiled horizontal exact-one formula

These names are the existing polynomial-time identity compiler's output,
not the generic encodable representation of nested geometric variables.
-/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance nativeAtomStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeAtomVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

def nativeRoutedFormulaSource (symbols : List encoding.Γ) :=
  (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase

theorem nativeAtomCodes_coherent (symbols : List encoding.Γ) :
    OccurrenceIdentity.Coherent (nativeRoutedFormulaSource decider symbols).variableOccurrences
      (directSourceFinalAtomIdentityCodes decider symbols) := by
  refine ⟨directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols,?_⟩
  intro i hi j hj
  exact directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols i j
    (by rwa [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms])
    (by rwa [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms])

def nativeAtomRenaming (symbols : List encoding.Γ) : RoutedVariable → Nat :=
  OccurrenceIdentity.rename (nativeRoutedFormulaSource decider symbols).variableOccurrences
    (directSourceFinalAtomIdentityCodes decider symbols)

theorem nativeAtomRenaming_injective (symbols : List encoding.Γ) : Function.Injective (nativeAtomRenaming decider symbols) :=
  OccurrenceIdentity.rename_injective _ _ (nativeAtomCodes_coherent decider symbols)

def nativeRoutedFormula (symbols : List encoding.Γ) : PeriodicCNF Nat :=
  (nativeRoutedFormulaSource decider symbols).rename (nativeAtomRenaming decider symbols)

theorem nativeRoutedFormula_atoms (symbols : List encoding.Γ) :
    (nativeRoutedFormula decider symbols).variableOccurrences = directSourceFinalAtomIdentityCodes decider symbols := by
  rw [nativeRoutedFormula,PeriodicCNF.variableOccurrences_rename]
  exact OccurrenceIdentity.map_rename _ _ (nativeAtomCodes_coherent decider symbols)

theorem nativeRoutedFormula_exactOne (symbols : List encoding.Γ) :
    PeriodicOneInThree.Satisfiable (nativeRoutedFormula decider symbols) ↔
      PeriodicOneInThree.Satisfiable (nativeRoutedFormulaSource decider symbols) :=
  PeriodicOneInThree.satisfiable_rename_iff _ _ (nativeAtomRenaming_injective decider symbols)

noncomputable def nativeRoutedFormulaAtomsComputableInPolyTime :
    Turing.TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (nativeRoutedFormula decider symbols).variableOccurrences) := by
  simpa only [nativeRoutedFormula_atoms] using directSourceFinalAtomIdentityCodesComputableInPolyTime decider

end LeanTrominoes.PeriodicCNFStripReduction
end
