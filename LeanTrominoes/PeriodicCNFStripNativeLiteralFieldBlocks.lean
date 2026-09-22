/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeAtomRenaming
import LeanTrominoes.PeriodicCNFStripNativeLiteralOffsets
import LeanTrominoes.PeriodicCNFStripNativeLiteralValues
import LeanTrominoes.PositionedIncidenceFormulaFields

/-! # Four native fields per actual normalized literal -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedIncidenceRows PeriodicCNFFlatEncoding
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeLiteralFieldStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeLiteralFieldVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

noncomputable def nativeRowAtomColumn :
    Compiler (nativeIncidenceRows decider) (fun s row => nativeAtomRenaming decider s row.2.1.atom) := by
  apply TM2ComputableInPolyTime.of_eq (nativeRoutedFormulaAtomsComputableInPolyTime decider)
  intro s
  rw [nativeRoutedFormula, PeriodicCNF.variableOccurrences_rename]
  unfold nativeRoutedFormulaSource
  rw [← PositionedIncidenceRows.atoms, List.map_map]
  simp only [nativeIncidenceRows, Function.comp_def]

noncomputable def nativeRowValueColumn :
    Compiler (nativeIncidenceRows decider) (fun _ row => row.2.1.value.toNat) := by
  apply TM2ComputableInPolyTime.of_eq (nativeLiteralValuesCompiler decider)
  intro s
  exact (PositionedIncidenceRows.map_literals
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
    (fun literal => literal.value.toNat)).symm

noncomputable def nativeLiteralFieldBlocksCompiler [Inhabited encoding.Γ] :
    BlocksCompiler (nativeIncidenceRows decider)
      (fun s row => UnaryFieldEncoderMachine.unaryFields
        (literalFields (namedLiteral (nativeAtomRenaming decider s) row))) := by
  let physical : BlocksCompiler (nativeIncidenceRows decider) (fun s row =>
      UnaryFieldEncoderMachine.unaryField (nativeAtomRenaming decider s row.2.1.atom) ++
      (UnaryFieldEncoderMachine.unaryField (Encodable.encode
        (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)).1) ++
      (UnaryFieldEncoderMachine.unaryField (Encodable.encode
        (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)).2) ++
       UnaryFieldEncoderMachine.unaryField row.2.1.value.toNat))) :=
    appendBlocks (blocks (nativeRowAtomColumn decider))
    (appendBlocks (blocks (nativeAnchoredOffsetCompiler decider true))
      (appendBlocks (blocks (nativeAnchoredOffsetCompiler decider false))
        (blocks (nativeRowValueColumn decider))))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply congrArg FiniteAlphabetDelimitedBlockJoin.blocks
  apply List.map_congr_left
  intro row _
  have value : encodeBoolField row.2.1.value = row.2.1.value.toNat := by cases row.2.1.value <;> rfl
  simp only [namedLiteral, literalFields, PeriodicLiteral.rename, PeriodicLiteral.anchorNormalize,
    DelimitedDirectionDisplacement.component, Bool.true_eq_false, ↓reduceIte,
    UnaryFieldEncoderMachine.unaryFields_cons, UnaryFieldEncoderMachine.unaryFields_nil,
    List.append_nil, value]

end LeanTrominoes.PeriodicCNFStripReduction
end
