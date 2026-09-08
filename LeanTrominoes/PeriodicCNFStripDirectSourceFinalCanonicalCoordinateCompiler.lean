/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalTerminalCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalCrossingCoordinateCompiler
import LeanTrominoes.UnaryAlignedAddNativeListCompiler

/-! # Complete canonical coordinates in final atom-occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance finalCanonicalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The four disjoint atom-family contributions produce one canonical
coordinate field for every final occurrence. -/
def directSourceFinalCanonicalCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryAlignedAddMachine.sums
    (UnaryAlignedAddMachine.sums
      (directSourceFinalOriginalAtomCoordinates decider
        (CarrierCrossingPointField.horizontal field)
        (CarrierCrossingPointField.keepPositive field) symbols)
      (directSourceFinalCanonicalTerminalCoordinates decider
        (CarrierCrossingPointField.horizontal field)
        (CarrierCrossingPointField.keepPositive field) symbols))
    (UnaryAlignedAddMachine.sums
      (directSourceFinalCanonicalBoundaryCoordinates decider field symbols)
      (directSourceFinalCanonicalInternalCoordinates decider field symbols))

noncomputable def directSourceFinalCanonicalCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalCoordinates decider field) := by
  let original := directSourceFinalOriginalAtomCoordinates decider
    (CarrierCrossingPointField.horizontal field) (CarrierCrossingPointField.keepPositive field)
  let terminal := directSourceFinalCanonicalTerminalCoordinates decider
    (CarrierCrossingPointField.horizontal field) (CarrierCrossingPointField.keepPositive field)
  let boundary := directSourceFinalCanonicalBoundaryCoordinates decider field
  let internal := directSourceFinalCanonicalInternalCoordinates decider field
  have originalTerminal : ∀ symbols, (original symbols).length = (terminal symbols).length := by
    intro symbols
    exact (directSourceFinalOriginalAtomCoordinates_length decider _ _ symbols).trans
      (directSourceFinalCanonicalTerminalCoordinates_length decider _ _ symbols).symm
  have boundaryInternal : ∀ symbols, (boundary symbols).length = (internal symbols).length := by
    intro symbols
    exact (directSourceFinalCanonicalBoundaryCoordinates_length decider field symbols).trans
      (directSourceFinalCanonicalInternalCoordinates_length decider field symbols).symm
  have originalBoundary : ∀ symbols, (original symbols).length = (boundary symbols).length := by
    intro symbols
    exact (directSourceFinalOriginalAtomCoordinates_length decider _ _ symbols).trans
      (directSourceFinalCanonicalBoundaryCoordinates_length decider field symbols).symm
  let firstCompiler := UnaryAlignedAddMachine.nativeListComputableInPolyTime
    original terminal originalTerminal
    (directSourceFinalOriginalAtomCoordinatesComputableInPolyTime decider _ _)
    (directSourceFinalCanonicalTerminalCoordinatesComputableInPolyTime decider _ _)
  let secondCompiler := UnaryAlignedAddMachine.nativeListComputableInPolyTime
    boundary internal boundaryInternal
    (directSourceFinalCanonicalBoundaryCoordinatesComputableInPolyTime decider field)
    (directSourceFinalCanonicalInternalCoordinatesComputableInPolyTime decider field)
  exact UnaryAlignedAddMachine.nativeListComputableInPolyTime
    (fun symbols => UnaryAlignedAddMachine.sums (original symbols) (terminal symbols))
    (fun symbols => UnaryAlignedAddMachine.sums (boundary symbols) (internal symbols))
    (fun symbols => by
      rw [UnaryAlignedAddMachine.sums_length
          (UnaryAlignedAddMachine.Valid.of_length_eq (originalTerminal symbols)),
        UnaryAlignedAddMachine.sums_length
          (UnaryAlignedAddMachine.Valid.of_length_eq (boundaryInternal symbols))]
      exact originalBoundary symbols)
    firstCompiler secondCompiler

private theorem originalAtomCoordinateField_eq_named (source : PeriodicCNF Variable)
    (field : CarrierCrossingMacroOrigin.Field) (query : WrappedPeriodicPlanarSATVariable Variable) :
    originalAtomCoordinateField source (CarrierCrossingPointField.horizontal field)
      (CarrierCrossingPointField.keepPositive field) query =
      CarrierCrossingPointField.pointValue field
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position query) := by
  change CarrierCrossingPointField.pointValue field
    ((@retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement Variable
      instDecidableEqProd source).position query) = _
  rw [show (instDecidableEqProd : DecidableEq Variable) = directSourceVariableDecidableEq from
    Subsingleton.elim _ _]

/-- All entries are the signed fields of the actual canonically gauged
placement; no constructor-specific contribution remains. -/
theorem directSourceFinalCanonicalCoordinates_eq_positions
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalCoordinates decider field symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        CarrierCrossingPointField.pointValue field
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            (directSourceFormula decider symbols)).position query) := by
  unfold directSourceFinalCanonicalCoordinates
  rw [directSourceFinalOriginalAtomCoordinates_eq_geometricCases,
    directSourceFinalCanonicalTerminalCoordinates_eq_positions,
    directSourceFinalCanonicalBoundaryCoordinates_eq_positions,
    directSourceFinalCanonicalInternalCoordinates_eq_positions,
    UnaryAlignedAddMachine.sums_map, UnaryAlignedAddMachine.sums_map,
    UnaryAlignedAddMachine.sums_map]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query with
  | atom atom =>
      simp only [Nat.add_zero]
      exact originalAtomCoordinateField_eq_named (directSourceFormula decider symbols)
        field ⟨.atom atom⟩
  | terminal indexed endpoint =>
      simp only [Nat.add_zero, Nat.zero_add, CarrierCrossingPointField.pointValue]
  | boundary boundary => simp only [Nat.add_zero, Nat.zero_add]
  | crossoverInternal internal => simp only [Nat.add_zero, Nat.zero_add]

theorem directSourceFinalCanonicalCoordinates_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalCoordinates decider field symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalCanonicalCoordinates_eq_positions, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
