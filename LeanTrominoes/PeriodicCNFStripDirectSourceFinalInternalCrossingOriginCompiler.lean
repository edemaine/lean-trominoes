/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceInternalCrossingCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingInternalCrossingCoordinateLookupSemantics

/-! # Crossing origins in the exact final internal-occurrence order -/

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

noncomputable local instance finalInternalCrossingOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The physical crossing origin for each internal occurrence, with zero in
positions belonging to other atom families. Local internal offsets are not included. -/
def directSourceFinalInternalCrossingOrigins (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceInternalCrossingCoordinateKeys decider symbols)
    (directSourceInternalCrossingOriginCoordinates decider field symbols)

noncomputable def directSourceFinalInternalCrossingOriginsComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInternalCrossingOrigins decider field) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalInternalCrossingOrigins
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceInternalCrossingCoordinateKeys decider)
      (directSourceInternalCrossingOriginCoordinates decider field)
      (fun symbols => (directSourceInternalCrossingCoordinateKeys_length_origins decider field symbols).symm)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceInternalCrossingCoordinateKeysComputableInPolyTime decider)
      (directSourceInternalCrossingOriginCoordinatesComputableInPolyTime decider field)
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

/-- The lookup recovers the exact physical datum at every valid internal occurrence. -/
theorem directSourceFinalInternalCrossingOrigins_eq_queryData
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalInternalCrossingOrigins decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (InternalCrossingCoordinateKeys.queryDatum (fun candidate => CarrierCrossingMacroOrigin.nodeValue field candidate.2)) := by
  have keysEq := input_eq_mk (directSourceInternalCrossingCoordinateKeys_eq_candidates decider symbols)
  unfold directSourceFinalInternalCrossingOrigins
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceInternalCrossingOriginCoordinates_eq_candidates]
  exact InternalCrossingCoordinateKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols))
    (fun candidate => CarrierCrossingMacroOrigin.nodeValue field candidate.2)

/-- Each internal entry contains its actual crossing macrocell origin before
canonical gauging, and every non-internal entry is zero. -/
theorem directSourceFinalInternalCrossingOrigins_eq_origins
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalInternalCrossingOrigins decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .crossoverInternal (crossing, _) => CarrierCrossingPointField.pointValue field
            (crossingMacroOrigin crossing)
        | _ => 0 := by
  rw [directSourceFinalInternalCrossingOrigins_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;> rfl

/-- All four origin columns use the same complete occurrence presentation. -/
theorem directSourceFinalInternalCrossingOrigins_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceFinalInternalCrossingOrigins decider field symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalInternalCrossingOrigins_eq_queryData, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
