/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeClauseHeaders
import LeanTrominoes.PeriodicCNFStripNativeLiteralFieldBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.UnaryFieldClosure
import LeanTrominoes.PeriodicOneInThreeAnchorNormalization

/-! # Complete native formula-field compiler for the routed exact-one source -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedIncidenceRows PeriodicCNFFlatEncoding
open UnaryFieldEncoderMachine (unaryFields unaryField)
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeFormulaStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeFormulaVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

def nativeNormalizedFormula (s : List encoding.Γ) : PeriodicCNF Nat :=
  (nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)

private theorem encoded_row (name : RoutedVariable → Nat) (row : Row RoutedVariable) :
    header row ++ unaryFields (literalFields (namedLiteral name row)) = unaryFields (rowFields name row) := by
  unfold header rowFields
  split <;> simp [unaryFields, unaryField]

noncomputable def nativeFormulaBodyCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id unaryFields
      (fun s => (nativeIncidenceRows decider s).flatMap (rowFields (nativeAtomRenaming decider s))) := by
  let physical := finishBlocks (appendBlocks (nativeClauseHeaderBlocksCompiler decider)
    (nativeLiteralFieldBlocksCompiler decider))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  simp only [id_eq, encoded_row]
  induction nativeIncidenceRows decider s with
  | nil => rfl
  | cons row rest ih => simp [List.flatMap_cons, ih]

private theorem arity_nonempty {V : Type*} (source : PositionedPeriodicCNF V)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clause : PositionedPeriodicClause V) (member : clause ∈ source.clauses) : clause.literals ≠ [] := by
  have hm : clause.literals ∈ source.erase.clauses := List.mem_map.mpr ⟨clause, member, rfl⟩
  have lengths := arity clause.literals hm
  intro empty
  simp [empty] at lengths

private theorem routedClauses_nonempty (source : PeriodicCNF Nat)
    (clause : PositionedPeriodicClause RoutedVariable)
    (member : clause ∈ (horizontalRoutedFormulaComputed source).clauses) : clause.literals ≠ [] := by
  apply arity_nonempty (horizontalRoutedFormulaComputed source) _ clause member
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact horizontalSemanticRoutedFormula_arityTwoOrThreeComputed source

noncomputable def nativeFormulaFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id unaryFields (fun s => formulaFields (nativeNormalizedFormula decider s)) := by
  let counts := TM2CompositionMachine.computableInPolyTime (nativeClauseAritiesCompiler decider)
    UnaryFieldAggregate.countCompiler
  let physical := UnaryFieldClosure.appendCompiler id _ _ counts (nativeFormulaBodyCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  unfold nativeNormalizedFormula nativeRoutedFormulaSource
  rw [formulaFields_eq _ _ (routedClauses_nonempty _)]
  simp only [List.length_map, PositionedPeriodicCNF.erase, List.singleton_append, nativeIncidenceRows]

/-- Every field of the actual normalized, numerically renamed formula is
compiled in polynomial time, including for an empty input alphabet. -/
noncomputable def nativeFormulaFieldsCompiler :
    TM2ComputableInPolyTime id unaryFields (fun s => formulaFields (nativeNormalizedFormula decider s)) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeFormulaFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime unaryFields _

/-- Native binary output, with the complete formula encoded field by field. -/
noncomputable def nativeFormulaEncodingCompiler :
    TM2ComputableInPolyTime id PeriodicCNFFlatEncoding.finEncoding.encode (nativeNormalizedFormula decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeFormulaFieldsCompiler decider)
    UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  simp only [PeriodicCNFFlatEncoding.finEncoding, PeriodicCNFFlatEncoding.finEncodingOfFields, encodeNatFields_eq_trList, id_eq]

/-- Serialization uses an injective renaming and a clause-anchor change,
both preserving exact-one satisfiability. -/
theorem nativeNormalizedFormula_exactOne (s : List encoding.Γ) :
    PeriodicOneInThree.Satisfiable (nativeNormalizedFormula decider s) ↔
      PeriodicOneInThree.Satisfiable (nativeRoutedFormulaSource decider s) := by
  unfold nativeNormalizedFormula
  rw [PeriodicOneInThree.satisfiable_rename_iff _ _ (nativeAtomRenaming_injective decider s),
    PeriodicOneInThree.anchorNormalize_satisfiable_iff]

end LeanTrominoes.PeriodicCNFStripReduction
end
