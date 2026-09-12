/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAuxiliaryCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalComposedInheritedCoordinateCompiler

/-! # Compiled final gauged Figure 9 variable coordinates -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader PlanarOneInThreeNoUnitsFigureNine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance composedVariableStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Select actual inherited or auxiliary Figure 9 coordinates using the
same scope bits as the identity compiler. Fresh polarity variables will use
their own route-based positions in the subsequent polarity stage. -/
def directSourceFinalComposedVariableCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues (directSourceFinalAtomScopeBits decider symbols)
    (directSourceFinalComposedInheritedCoordinates decider horizontal keepPositive symbols)
    (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalComposedVariableCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalComposedVariableCoordinates
    exact AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime id
      (directSourceFinalAtomScopeBits decider)
      (directSourceFinalComposedInheritedCoordinates decider horizontal keepPositive)
      (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive)
      (fun symbols => by rw [directSourceFinalAtomScopeBits_length, directSourceFinalComposedInheritedCoordinates_length])
      (fun symbols => by rw [directSourceFinalComposedInheritedCoordinates_length, directSourceFinalAuxiliaryCoordinates_length])
      (directSourceFinalAtomScopeBitsComputableInPolyTime decider)
      (directSourceFinalComposedInheritedCoordinatesComputableInPolyTime decider horizontal keepPositive)
      (directSourceFinalAuxiliaryCoordinatesComputableInPolyTime decider horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalComposedVariableCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalComposedVariableCoordinates
  rw [AlignedUnaryBooleanChoice.selectedValues_length _ _ _
    (by rw [directSourceFinalAtomScopeBits_length, directSourceFinalComposedInheritedCoordinates_length]),
    directSourceFinalAtomScopeBits_length]

/-- Every original polarity occurrence selects its exact Figure 9 variable
position after final gauging. Both operands and the scope control retain the
same source-parent and generated-clause witness. -/
theorem directSourceFinalComposedVariableCoordinates_finalGauged_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (sourceLocal : (directSourceFormula decider symbols).IsLocal)
    (sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3)
    (sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols))
    (sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [])
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) :
    (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols)).position
          (instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
            witness.metadata.sourceClause (prefixAtom occurrence.header.figurePrefix)))) := by
  have indexLt := (List.getElem?_eq_some_iff.mp lookup).1
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalOccurrences_length_eq_compiled]
    exact indexLt
  have outputLt : index < (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive symbols).length := by
    rw [directSourceFinalComposedVariableCoordinates_length]
    exact compiledLt
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨outputLt, ?_⟩
  rw [← List.getD_eq_getElem _ 0 outputLt, directSourceFinalComposedVariableCoordinates,
    AlignedUnaryBooleanChoice.selectedValues_getD _ _ _
      (by rw [directSourceFinalAtomScopeBits_length, directSourceFinalComposedInheritedCoordinates_length])
      (by rw [directSourceFinalComposedInheritedCoordinates_length, directSourceFinalAuxiliaryCoordinates_length])
      index (by rw [directSourceFinalAtomScopeBits_length]; exact compiledLt)]
  have scopeLookup : (directSourceFinalAtomScopeBits decider symbols).getD index false =
      finalAtomScopeBit (outputAtomScopeControl occurrence.header) := by
    rw [directSourceFinalAtomScopeBits_eq_occurrences, List.getD_eq_getElem?_getD,
      List.getElem?_map, lookup, Option.map_some, Option.getD_some]
  rw [scopeLookup]
  cases selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) with
  | none =>
      rw [sourceOccurrenceScope_of_auxiliary occurrence ⟨original, selected⟩]
      simp only [finalAtomScopeBit, ↓reduceIte]
      have coordinates := directSourceFinalAuxiliaryCoordinates_finalGauged_lookup
        decider horizontal keepPositive symbols sourceLocal sourceWidth sourceOccurrences sourceNonempty
        index occurrence lookup witness (by simpa only [prefixAtom_eq_localQuery] using selected)
      simp only [List.getD_eq_getElem?_getD, coordinates, Option.getD_some, prefixAtom_eq_localQuery]
  | some slot =>
      rw [sourceOccurrenceScope_of_inherited occurrence original slot selected]
      simp only [finalAtomScopeBit, Bool.false_eq_true, ↓reduceIte]
      have coordinates := directSourceFinalComposedInheritedCoordinates_finalGauged_lookup
        decider horizontal keepPositive symbols index occurrence witness lookup original slot selected
      simpa only [List.getD_eq_getElem?_getD, Option.getD_some] using
        congrArg (fun value => value.getD 0) coordinates

/-- At an actual final gauged clause and literal index, the coordinate
column names that literal's variable, including the final clockwise reorder. -/
theorem directSourceFinalComposedVariableCoordinates_literal_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (sourceLocal : (directSourceFormula decider symbols).IsLocal)
    (sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3)
    (sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols))
    (sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [])
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence)
    (clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (clauseMember : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx)
    (literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (literalMember : (literal, occurrence.header.polarity.indexed.sourceLiteralIndex) ∈ clause.literals.zipIdx) :
    (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols)).position literal.atom)) := by
  rw [← witness.finalGaugedLiteralAtom sourceLocal sourceWidth sourceOccurrences sourceNonempty
    clauseMember literalMember]
  simpa only [prefixAtom_eq_localQuery] using
    directSourceFinalComposedVariableCoordinates_finalGauged_lookup decider horizontal keepPositive symbols
      sourceLocal sourceWidth sourceOccurrences sourceNonempty index occurrence lookup witness original

end LeanTrominoes.PeriodicCNFStripReduction
end
