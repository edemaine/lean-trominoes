/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIdentityCoordinateCompiler
import LeanTrominoes.RetainedAngularFanCycleCoordinateFormula

/-! # Aligned source origins and ring offsets for final cycle occurrences -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance cycleCoordinateDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceFinalCycleCoordinateOwners (symbols : List encoding.Γ) :=
  (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup

private theorem cycleOwner_member (symbols : List encoding.Γ)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (member : atom ∈ directSourceFinalCycleCoordinateOwners decider symbols) :
    atom ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences := by
  simpa only [directSourceFinalCycleCoordinateOwners, List.mem_dedup] using member

/-- One fixed ring-slot table for each retained source atom, in marker order. -/
def directSourceFinalCycleCoordinateEntries (symbols : List encoding.Γ) :
    List (WrappedPeriodicPlanarSATVariable Variable × DirectFinalCycleRingVertexSlot) :=
  (directSourceFinalCycleCoordinateOwners decider symbols).flatMap fun atom =>
    directSourceFinalLocalCycleRingVertexSlots.map (atom, ·)

private theorem cycleBlockLength_eq_slots :
    directSourceFinalCycleOccurrenceBlockLength FormulaShapeDirectionOrdering.Token.variable =
      directSourceFinalLocalCycleRingVertexSlots.length := by
  simp [directSourceFinalCycleOccurrenceBlockLength, directSourceFinalCycleClauseDescriptorBlock,
    FormulaShapeFixedEightDirection.cycleClauseBlock]

def directSourceFinalCycleOwnerCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values (directSourceFinalCycleInheritedAtomIdentityIndices decider symbols)
    (directSourceFinalCanonicalCoordinates decider field symbols)

noncomputable def directSourceFinalCycleOwnerCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCycleOwnerCoordinates decider field) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCycleOwnerCoordinates
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id
      (directSourceFinalCycleInheritedAtomIdentityIndices decider)
      (directSourceFinalCanonicalCoordinates decider field)
      (directSourceFinalCycleInheritedAtomIdentityIndicesComputableInPolyTime decider)
      (directSourceFinalCanonicalCoordinatesComputableInPolyTime decider field)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

theorem directSourceFinalCycleOwnerCoordinates_length (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    (directSourceFinalCycleOwnerCoordinates decider field symbols).length =
      (directSourceFinalCycleOccurrenceData decider symbols).length := by
  rw [directSourceFinalCycleOwnerCoordinates, UnaryIndexedValueLookup.values_length,
    directSourceFinalCycleInheritedAtomIdentityIndices_length]

/-- Every cycle row receives the coordinates of its actual retained owner. -/
theorem directSourceFinalCycleOwnerCoordinates_eq_entries (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    directSourceFinalCycleOwnerCoordinates decider field symbols =
      (directSourceFinalCycleCoordinateEntries decider symbols).map fun entry =>
        CarrierCrossingPointField.pointValue field
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            (directSourceFormula decider symbols)).position entry.1) := by
  unfold directSourceFinalCycleOwnerCoordinates
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt]
  · rw [directSourceFinalCycleInheritedAtomIdentityIndices_eq_flatMap_replicate,
      directSourceFinalDistinctAtomIdentityIndices_eq_actual_atoms,
      List.flatMap_map, List.map_flatMap]
    unfold directSourceFinalCycleCoordinateEntries directSourceFinalCycleCoordinateOwners
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom member
    rw [List.map_replicate, directSourceFinalCanonicalCoordinates_getD_identity decider field symbols atom
      (cycleOwner_member decider symbols atom member), cycleBlockLength_eq_slots, List.map_map]
    simp only [Function.comp_def, List.map_const']
  · intro identity member
    rw [directSourceFinalCycleInheritedAtomIdentityIndices_eq_flatMap_replicate,
      directSourceFinalDistinctAtomIdentityIndices_eq_actual_atoms] at member
    obtain ⟨ownerIdentity, ownerMember, repeated⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp ownerMember
    have identityEq := List.eq_of_mem_replicate repeated
    rw [identityEq, directSourceFinalCanonicalCoordinates_length]
    exact directSourceFinalCompactAtomIdentityDatum_lt_coordinates decider symbols atom
      (cycleOwner_member decider symbols atom atomMember)

theorem directSourceFinalCycleRingVertexSlots_eq_owner_blocks (symbols : List encoding.Γ) :
    directSourceFinalCycleRingVertexSlots decider symbols =
      (directSourceFinalCycleCoordinateOwners decider symbols).flatMap
        fun _ => directSourceFinalLocalCycleRingVertexSlots := by
  apply (List.map_injective_iff (f := Fin.val)).mpr (fun _ _ equal => Fin.ext equal)
  change directSourceFinalCycleRingVertexSlotValues decider symbols = _
  rw [directSourceFinalCycleRingVertexSlotValues_eq_flatMap,
    directSourceFinalDistinctAtomIdentityIndices_eq_actual_atoms]
  simp only [directSourceFinalCycleCoordinateOwners, List.flatMap_map, List.map_flatMap]

def directSourceFinalCycleLocalCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun slot : DirectFinalCycleRingVertexSlot =>
    CarrierCrossingPointField.pointValue field
      (retainedSplitRingVertexOffset (directFinalCycleRingVertexOfSlot slot)))
    (directSourceFinalCycleRingVertexSlots decider symbols)

noncomputable def directSourceFinalCycleLocalCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCycleLocalCoordinates decider field) := by
  unfold directSourceFinalCycleLocalCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCycleRingVertexSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime (fun slot : DirectFinalCycleRingVertexSlot =>
      CarrierCrossingPointField.pointValue field
        (retainedSplitRingVertexOffset (directFinalCycleRingVertexOfSlot slot))))

theorem directSourceFinalCycleLocalCoordinates_length (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    (directSourceFinalCycleLocalCoordinates decider field symbols).length =
      (directSourceFinalCycleOccurrenceData decider symbols).length := by
  unfold directSourceFinalCycleLocalCoordinates FiniteUnaryFieldMap.values
  rw [List.length_map]
  simpa only [directSourceFinalCycleRingVertexSlotValues, List.length_map] using
    directSourceFinalCycleRingVertexSlotValues_length decider symbols

/-- The local column shares the owner column's exact row order. -/
theorem directSourceFinalCycleLocalCoordinates_eq_entries (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    directSourceFinalCycleLocalCoordinates decider field symbols =
      (directSourceFinalCycleCoordinateEntries decider symbols).map fun entry =>
        CarrierCrossingPointField.pointValue field
          (retainedSplitRingVertexOffset (directFinalCycleRingVertexOfSlot entry.2)) := by
  unfold directSourceFinalCycleLocalCoordinates FiniteUnaryFieldMap.values
  rw [directSourceFinalCycleRingVertexSlots_eq_owner_blocks]
  simp only [directSourceFinalCycleCoordinateEntries, List.map_flatMap, List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction
end
