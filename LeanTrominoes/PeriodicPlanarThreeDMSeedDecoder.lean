/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBooleanSignedDecoder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedSatisfiability

/-! # One-bit decoders preserve finite exact-one prescriptions through planar 3DM -/
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def seedTriple (source : PeriodicCNF V) (v : V) : Triple V :=
  let polarity := occurrencePolarity source v .first
  match occurrenceConnectorKind source v .first with
  | .fixedRed => .fixedRed v .first (if polarity then .bottomLeft else .topLeft)
  | .fixedGreen => .ordinary v .first .fixedGreen (if polarity then .first else .second)
  | .fixedBlue => .ordinary v .first .fixedBlue (if polarity then .first else .second)

def typedSeedRead (source : PeriodicCNF V) (v : V) : PeriodicLiteral (Triple V) :=
  ⟨seedTriple source v,(0,0),true⟩

theorem typedSeed_decode (source : PeriodicCNF V) (a : (problem source).MatchingAssignment) :
    decode (typedSeedRead source) a = assignmentOfMatching source a := by
  funext v c
  cases kind : occurrenceConnectorKind source v .first <;>
    cases polarity : occurrencePolarity source v .first <;>
    simp [decode,typedSeedRead,seedTriple,assignmentOfMatching,occurrenceBoundary,
      kind,polarity,Cell.add]

theorem canonical_seed_inverse (source : PeriodicCNF V) (a : V → Cell → Bool) (v : V) (c : Cell) :
    matchingOfAssignment source a (seedTriple source v) c = a v c := by
  cases kind : occurrenceConnectorKind source v .first <;>
    cases polarity : occurrencePolarity source v .first <;> cases value : a v c <;>
    simp [seedTriple,matchingOfAssignment,occurrenceSignal,kind,polarity,value,
      variableConnectorLiteralSignal,variableOccurrenceSelection,fixedRedConnectorSelection]

theorem typedSeedFactor (source : PeriodicCNF V) (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    LogicalFactor (PeriodicOneInThree.Satisfies source) (problem source).Satisfies
      (typedSeedRead source) Set.univ := by
  constructor
  · intro a ha
    rw [typedSeed_decode]
    exact assignmentOfMatching_satisfies source occurrences arity a ha
  · intro a ha
    refine ⟨matchingOfAssignment source a,matchingOfAssignment_satisfies source occurrences arity a ha,?_⟩
    intro v _ c
    simpa [decode,typedSeedRead,Cell.add] using canonical_seed_inverse source a v c

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
