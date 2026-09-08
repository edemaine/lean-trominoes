/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCanonicalCrossingCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossingCoordinateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingCoordinateLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingInternalCrossingCoordinateLookupSemantics

/-! # Exact canonical coordinates for final crossing-gadget occurrences -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

private theorem input_eq_mk {input : DelimitedBinaryWords.Input} {words : List (List Bool)}
    (equal : input.words = words) : input = ⟨words⟩ := DelimitedBinaryWords.eq_of_words_eq equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance canonicalCrossingStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

private theorem coordinate_query_valid (symbols : List encoding.Γ)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (member : query ∈ directSourceFinalCoordinateAtoms decider symbols) :
    RetainedDrawingPeriodicPlanarSATVariableValid (directSourceFormula decider symbols) query.original := by
  have valid := directSourceFinalCoordinateAtoms_valid decider symbols query member
  change @RetainedDrawingPeriodicPlanarSATVariableValid Variable originalAtomWordVariableDecidableEq
    (directSourceFormula decider symbols) query.original at valid
  rw [show originalAtomWordVariableDecidableEq = directSourceVariableDecidableEq from Subsingleton.elim _ _] at valid
  exact valid

def directSourceFinalCanonicalBoundaryCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceCrossingCoordinateKeys decider symbols)
    (directSourceCarrierCanonicalCrossingCoordinates decider CrossingSide.localPosition field symbols)

noncomputable def directSourceFinalCanonicalBoundaryCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalBoundaryCoordinates decider field) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCanonicalBoundaryCoordinates
    apply DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceCrossingCoordinateKeys decider)
      (directSourceCarrierCanonicalCrossingCoordinates decider CrossingSide.localPosition field)
    · intro symbols
      rw [directSourceCarrierCanonicalCrossingCoordinates_length, directSourceCrossingCoordinateKeys_eq_nodes,
        List.length_map]
    · exact directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider
    · exact directSourceCrossingCoordinateKeysComputableInPolyTime decider
    · exact directSourceCarrierCanonicalCrossingCoordinatesComputableInPolyTime decider CrossingSide.localPosition field
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

theorem directSourceFinalCanonicalBoundaryCoordinates_eq_queryData
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalBoundaryCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (CarrierCrossingCoordinateKeys.queryDatum
          (CarrierCanonicalCrossingCoordinates.nodeValue CrossingSide.localPosition field
            (routeDescriptorStreamGridSize (numericRouteDescriptors (directSourceFormula decider symbols))))) := by
  have keysEq := input_eq_mk (directSourceCrossingCoordinateKeys_eq_nodes decider symbols)
  unfold directSourceFinalCanonicalBoundaryCoordinates
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceCarrierCanonicalCrossingCoordinates_eq_nodes]
  exact CarrierCrossingCoordinateKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols)) _

/-- Boundary contributions already include canonical wrapping and the exact local side offset. -/
theorem directSourceFinalCanonicalBoundaryCoordinates_eq_positions
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalBoundaryCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .boundary boundary => CarrierCrossingPointField.pointValue field
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              (directSourceFormula decider symbols)).position ⟨.boundary boundary⟩)
        | _ => 0 := by
  rw [directSourceFinalCanonicalBoundaryCoordinates_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query with
  | boundary boundary =>
      change CarrierCanonicalCrossingCoordinates.nodeValue CrossingSide.localPosition field _ (.boundary boundary) = _
      unfold CarrierCanonicalCrossingCoordinates.nodeValue
      rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors _
        (directSource_incidencesWithMetadata_ne_nil decider symbols),
        CarrierCanonicalCrossingCoordinates.boundary_nodePoint_eq_position]
  | terminal _ _ => rfl
  | atom _ => rfl
  | crossoverInternal _ => rfl

def directSourceFinalCanonicalInternalCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceInternalCrossingCoordinateKeys decider symbols)
    (directSourceInternalCanonicalCoordinateData decider field symbols)

noncomputable def directSourceFinalCanonicalInternalCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalInternalCoordinates decider field) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCanonicalInternalCoordinates
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceInternalCrossingCoordinateKeys decider)
      (directSourceInternalCanonicalCoordinateData decider field)
      (directSourceInternalCanonicalCoordinateData_length decider field)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceInternalCrossingCoordinateKeysComputableInPolyTime decider)
      (directSourceInternalCanonicalCoordinateDataComputableInPolyTime decider field)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

theorem directSourceFinalCanonicalInternalCoordinates_eq_queryData
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalInternalCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (InternalCrossingCoordinateKeys.queryDatum
          (fun candidate => CarrierCanonicalCrossingCoordinates.nodeValue
            (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable candidate.1)) field
            (routeDescriptorStreamGridSize (numericRouteDescriptors (directSourceFormula decider symbols))) candidate.2)) := by
  have keysEq := input_eq_mk (directSourceInternalCrossingCoordinateKeys_eq_candidates decider symbols)
  unfold directSourceFinalCanonicalInternalCoordinates
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceInternalCanonicalCoordinateData_eq_candidates]
  exact InternalCrossingCoordinateKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols)) _

/-- Internal contributions already include canonical wrapping and the exact local role offset. -/
theorem directSourceFinalCanonicalInternalCoordinates_eq_positions
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalInternalCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .crossoverInternal internal => CarrierCrossingPointField.pointValue field
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              (directSourceFormula decider symbols)).position ⟨.crossoverInternal internal⟩)
        | _ => 0 := by
  rw [directSourceFinalCanonicalInternalCoordinates_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query with
  | crossoverInternal internal =>
      rcases internal with ⟨crossing, role⟩
      change CarrierCanonicalCrossingCoordinates.nodeValue
        (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role)) field _
        (.boundary ⟨crossing, .left⟩) = _
      unfold CarrierCanonicalCrossingCoordinates.nodeValue
      rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors _
        (directSource_incidencesWithMetadata_ne_nil decider symbols),
        CarrierCanonicalCrossingCoordinates.internal_nodePoint_eq_position]
  | terminal _ _ => rfl
  | atom _ => rfl
  | boundary _ => rfl

theorem directSourceFinalCanonicalBoundaryCoordinates_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalBoundaryCoordinates decider field symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalCanonicalBoundaryCoordinates_eq_queryData, List.length_map]

theorem directSourceFinalCanonicalInternalCoordinates_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalInternalCoordinates decider field symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalCanonicalInternalCoordinates_eq_queryData, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
