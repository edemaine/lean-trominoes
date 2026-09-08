/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastIndexMappedDatumLookup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedRingAtomSemantics
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Canonical coordinates retrieved through exact source-atom identities -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance identityCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

private theorem equalityRow_eq (values : List (List Bool)) (target : List Bool) :
    LastRepresentativeEqualityRows.equalityRow values target =
      StableOccurrenceRanks.equalityRow values target := rfl

private theorem coordinateAtom_member (symbols : List encoding.Γ)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (member : atom ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences) :
    atom ∈ directSourceFinalCoordinateAtoms decider symbols := by
  rwa [directSourceFinalCoordinateAtoms_eq_variableOccurrences]

/-- Every represented source-atom identity is a valid coordinate-column index. -/
theorem directSourceFinalCompactAtomIdentityDatum_lt_coordinates (symbols : List encoding.Γ)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (member : atom ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences) :
    directSourceFinalCompactAtomIdentityDatum decider symbols
      (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) atom) <
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  unfold directSourceFinalCompactAtomIdentityDatum
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, equalityRow_eq]
  dsimp only
  exact LastTrueUnaryValueLookupMachine.lookup_mappedKey_range_lt
    (directSourceFinalCoordinateAtoms decider symbols)
    (directSourceFinalCompactAtomWord (directSourceFormula decider symbols)) atom
    (coordinateAtom_member decider symbols atom member)

/-- Looking up a canonical coordinate at its last-index identity gives the
actual represented atom's placement, independently of duplicate occurrences. -/
theorem directSourceFinalCanonicalCoordinates_getD_identity
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (member : atom ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences) :
    (directSourceFinalCanonicalCoordinates decider field symbols).getD
      (directSourceFinalCompactAtomIdentityDatum decider symbols
        (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) atom)) 0 =
      CarrierCrossingPointField.pointValue field
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          (directSourceFormula decider symbols)).position atom) := by
  rw [directSourceFinalCanonicalCoordinates_eq_positions]
  unfold directSourceFinalCompactAtomIdentityDatum
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, equalityRow_eq]
  dsimp only
  apply LastTrueUnaryValueLookupMachine.getD_lookup_mappedKey_range
    (directSourceFinalCoordinateAtoms decider symbols)
    (directSourceFinalCompactAtomWord (directSourceFormula decider symbols))
    (fun query => CarrierCrossingPointField.pointValue field
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        (directSourceFormula decider symbols)).position query)) atom
    (coordinateAtom_member decider symbols atom member)
  intro other otherMember keyEq
  have otherSource : other ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences := by
    rwa [← directSourceFinalCoordinateAtoms_eq_variableOccurrences]
  have atomEq := directSourceFinalCompactOccurrenceAtomWords_separate decider symbols
    other otherSource atom member keyEq
  rw [atomEq]

end LeanTrominoes.PeriodicCNFStripReduction
end
