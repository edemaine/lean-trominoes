/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceInternalCrossingRoleDataCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATMacrocellCoordinates
import LeanTrominoes.PeriodicOrthocrossingInternalCrossingCoordinateLookupSemantics

/-! # Internal-role data and local coordinates in final occurrence order -/

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

/-- A fixed role datum at each internal occurrence, with zero for other atom families. -/
def directSourceFinalInternalRoleData (roleValue : PlanarThreeSAT.CrossoverInternal → Nat)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceInternalCrossingCoordinateKeys decider symbols)
    (directSourceInternalCrossingRoleData decider roleValue symbols)

noncomputable def directSourceFinalInternalRoleDataComputableInPolyTime
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInternalRoleData decider roleValue) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalInternalRoleData
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceInternalCrossingCoordinateKeys decider)
      (directSourceInternalCrossingRoleData decider roleValue)
      (fun symbols => (directSourceInternalCrossingCoordinateKeys_length_roleData decider roleValue symbols).symm)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceInternalCrossingCoordinateKeysComputableInPolyTime decider)
      (directSourceInternalCrossingRoleDataComputableInPolyTime decider roleValue)
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
theorem directSourceFinalInternalRoleData_eq_queryData
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) (symbols : List encoding.Γ) :
    directSourceFinalInternalRoleData decider roleValue symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (InternalCrossingCoordinateKeys.queryDatum (fun candidate => roleValue candidate.1)) := by
  have keysEq := input_eq_mk (directSourceInternalCrossingCoordinateKeys_eq_candidates decider symbols)
  unfold directSourceFinalInternalRoleData
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceInternalCrossingRoleData_eq_candidates]
  exact InternalCrossingCoordinateKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols))
    (fun candidate => roleValue candidate.1)

/-- The output uses the exact role of each internal occurrence. -/
theorem directSourceFinalInternalRoleData_eq_roles
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) (symbols : List encoding.Γ) :
    directSourceFinalInternalRoleData decider roleValue symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .crossoverInternal (_, role) => roleValue role
        | _ => 0 := by
  rw [directSourceFinalInternalRoleData_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;> rfl

/-- Role columns use the complete final occurrence presentation. -/
theorem directSourceFinalInternalRoleData_length
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) (symbols : List encoding.Γ) :
    (directSourceFinalInternalRoleData decider roleValue symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalInternalRoleData_eq_queryData, List.length_map]


/-- Signed local coordinates inside the crossing macrocell. -/
def internalRoleLocalCoordinate (field : CarrierCrossingMacroOrigin.Field)
    (role : PlanarThreeSAT.CrossoverInternal) : Nat :=
  CarrierCrossingPointField.pointValue field
    (PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role))

def directSourceFinalInternalLocalCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalInternalRoleData decider (internalRoleLocalCoordinate field) symbols

noncomputable def directSourceFinalInternalLocalCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInternalLocalCoordinates decider field) :=
  directSourceFinalInternalRoleDataComputableInPolyTime decider (internalRoleLocalCoordinate field)

/-- These are precisely the finite local offsets retained by canonical macrocell gauging. -/
theorem directSourceFinalInternalLocalCoordinates_eq_localPositions
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalInternalLocalCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .crossoverInternal internal => CarrierCrossingPointField.pointValue field
            (periodicPlanarSATVariableLocalPosition
              (PeriodicPlanarSATVariable.crossoverInternal (Variable := Variable) internal))
        | _ => 0 := by
  unfold directSourceFinalInternalLocalCoordinates
  rw [directSourceFinalInternalRoleData_eq_roles]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;> rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
