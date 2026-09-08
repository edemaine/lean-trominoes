/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateStreamAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionActiveTerminalCompiler

/-! # Canonical terminal coordinates with inactive candidates removed -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
open Computability Turing PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

def activeCanonicalTerminalCoordinateFields (horizontal keepPositive : Bool)
    (tokens : List Token) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues (terminalCoordinateActives tokens)
    (canonicalTerminalCoordinateFields horizontal keepPositive tokens)

noncomputable def activeCanonicalTerminalCoordinateFieldsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (activeCanonicalTerminalCoordinateFields horizontal keepPositive) :=
  UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime id
    terminalCoordinateActives (canonicalTerminalCoordinateFields horizontal keepPositive)
    terminalCoordinateActivesComputableInPolyTime
    (canonicalTerminalCoordinateFieldsComputableInPolyTime horizontal keepPositive)

private theorem select_aligned_candidates
    {Value : Type} (items : List (Candidate Value)) (values : List Nat)
    (field : Value → Nat)
    (aligned : List.Forall₂ (fun candidate value => ∀ item,
      candidate.value = some item → value = field item) items values) :
    UnaryFieldBooleanFilter.selectedValues
        (items.map fun candidate => candidate.value.isSome) values =
      (items.filterMap Candidate.value).map field := by
  rw [UnaryFieldBooleanFilter.selectedValues_eq]
  induction aligned with
  | nil => rfl
  | @cons candidate value candidates values head aligned induction =>
      cases valueEq : candidate.value with
      | none =>
          simpa [DelimitedBinaryWordBooleanFilter.selected, valueEq] using induction
      | some item =>
          have fieldEq := head item valueEq
          simp [DelimitedBinaryWordBooleanFilter.selected, valueEq, fieldEq, induction]


/-- Filtering preserves exactly the canonical coordinates of all physical terminal candidates. -/
theorem activeCanonicalTerminalCoordinateFields_descriptorPairTokens
    (horizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    activeCanonicalTerminalCoordinateFields horizontal keepPositive (descriptorPairTokens pair) =
      ((paddedTerminalCarrierNodeCandidates pair).filterMap Candidate.value).map
        (carrierNodeCanonicalCoordinateFieldAtPeriod horizontal keepPositive pair.1.gridSize) := by
  unfold activeCanonicalTerminalCoordinateFields
  rw [terminalCoordinateActives_descriptorPairTokens]
  rw [select_aligned_candidates _ _ _
    (canonicalTerminalCoordinateCarrierNodeCandidates_forall₂ horizontal keepPositive pair bounds)]
  rw [filterMap_terminalDirectionalCarrierNodeCandidates]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
end
