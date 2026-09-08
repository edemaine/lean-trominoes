/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossingCoordinateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingCoordinateLookupSemantics

/-! # Crossing origins in the exact final boundary-occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

private theorem input_eq_mk {input : DelimitedBinaryWords.Input} {words : List (List Bool)}
    (equal : input.words = words) : input = ⟨words⟩ :=
  DelimitedBinaryWords.eq_of_words_eq equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance finalBoundaryCrossingOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The physical crossing origin for each boundary occurrence, with zero in
positions belonging to other atom families. Local side offsets are not included. -/
def directSourceFinalBoundaryCrossingOrigins (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceCrossingCoordinateKeys decider symbols)
    (directSourceCarrierCrossingMacroOriginCoordinates decider field symbols)

noncomputable def directSourceFinalBoundaryCrossingOriginsComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalBoundaryCrossingOrigins decider field) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalBoundaryCrossingOrigins
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceCrossingCoordinateKeys decider)
      (directSourceCarrierCrossingMacroOriginCoordinates decider field)
      (fun symbols => (directSourceCrossingCoordinateKeys_length_origins decider field symbols).symm)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceCrossingCoordinateKeysComputableInPolyTime decider)
      (directSourceCarrierCrossingMacroOriginCoordinatesComputableInPolyTime decider field)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

private theorem coordinate_query_valid (symbols : List encoding.Γ)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (member : query ∈ directSourceFinalCoordinateAtoms decider symbols) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      (directSourceFormula decider symbols) query.original := by
  have valid := directSourceFinalCoordinateAtoms_valid decider symbols query member
  change @RetainedDrawingPeriodicPlanarSATVariableValid Variable originalAtomWordVariableDecidableEq
    (directSourceFormula decider symbols) query.original at valid
  rw [show originalAtomWordVariableDecidableEq = directSourceVariableDecidableEq from
    Subsingleton.elim _ _] at valid
  exact valid

/-- The lookup recovers the exact physical datum at every valid boundary occurrence. -/
theorem directSourceFinalBoundaryCrossingOrigins_eq_queryData
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalBoundaryCrossingOrigins decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (CarrierCrossingCoordinateKeys.queryDatum (CarrierCrossingMacroOrigin.nodeValue field)) := by
  have keysEq := input_eq_mk (directSourceCrossingCoordinateKeys_eq_nodes decider symbols)
  unfold directSourceFinalBoundaryCrossingOrigins
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceCarrierCrossingMacroOriginCoordinates_eq_nodes]
  exact CarrierCrossingCoordinateKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols))
    (CarrierCrossingMacroOrigin.nodeValue field)

/-- Each boundary entry contains its actual crossing macrocell origin before
canonical gauging, and every non-boundary entry is zero. -/
theorem directSourceFinalBoundaryCrossingOrigins_eq_origins
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalBoundaryCrossingOrigins decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .boundary boundary => CarrierCrossingPointField.pointValue field
            (crossingMacroOrigin boundary.crossing)
        | _ => 0 := by
  rw [directSourceFinalBoundaryCrossingOrigins_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;> rfl

/-- All four origin columns use the same complete occurrence presentation. -/
theorem directSourceFinalBoundaryCrossingOrigins_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceFinalBoundaryCrossingOrigins decider field symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalBoundaryCrossingOrigins_eq_queryData, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
