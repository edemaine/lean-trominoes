/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicBooleanSignedDecoder
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMEncodedSatisfiability

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

theorem seedTriple_mem (source : PeriodicCNF V) (v : V)
    (member : v ∈ occurringVariables source) : seedTriple source v ∈ (problem source).triples := by
  have firstMember : (.first : OccurrenceSlot) ∈ usedSlots source v := by
    rcases usedSlots_cases_of_atom_mem source v member with one | two | three <;>
      simp_all
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨v,member,List.mem_flatMap.mpr ⟨.first,firstMember,?_⟩⟩
  cases kind : occurrenceConnectorKind source v .first <;>
    cases polarity : occurrencePolarity source v .first <;>
    simp [seedTriple,occurrenceTriples,kind,polarity,allFixedRedTriples,allOrdinaryTriples]

def encodedSeedRead (source : PeriodicCNF V) (v : V) : PeriodicLiteral Nat :=
  ⟨(problem source).triples.idxOf (seedTriple source v),(0,0),true⟩

theorem encodedSeed_decode (source : PeriodicCNF V)
    (a : (encodedProblem source).MatchingAssignment) :
    decode (encodedSeedRead source) a =
      assignmentOfMatching source ((problem source).decodeAssignment a) := by
  rw [← typedSeed_decode]
  funext v c
  simp [decode,encodedSeedRead,typedSeedRead,TypedProblem.decodeAssignment,Cell.add]

theorem encodedSeedFactor (source : PeriodicCNF V) (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    LogicalFactor (PeriodicOneInThree.Satisfies source) (encodedProblem source).Satisfies
      (encodedSeedRead source) {v | v ∈ occurringVariables source} := by
  constructor
  · intro a ha
    rw [encodedSeed_decode]
    exact assignmentOfMatching_satisfies source occurrences arity _
      (typed_satisfies_of_encoded_satisfies source a ha)
  · intro a ha
    let matching := matchingOfAssignment source a
    refine ⟨(problem source).encodeAssignment matching,
      encoded_satisfies_of_typed_satisfies source matching
        (matchingOfAssignment_satisfies source occurrences arity a ha),?_⟩
    intro v hv c
    change (problem source).encodeAssignment matching
      ((problem source).triples.idxOf (seedTriple source v)) (Cell.add c (0,0)) = a v c
    rw [(problem source).encodeAssignment_idxOf matching _ (seedTriple_mem source v hv)]
    simpa [Cell.add,matching] using canonical_seed_inverse source a v c

theorem encodedSeeded_iff (source : PeriodicCNF V) (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) (seed : PeriodicCNF.Seed V)
    (supported : SupportedSeed {v | v ∈ occurringVariables source} seed) :
    Prescribed (PeriodicOneInThree.Satisfies source) seed ↔
      Prescribed (encodedProblem source).Satisfies (transportSeed (encodedSeedRead source) seed) :=
  (encodedSeedFactor source occurrences arity).seeded_iff seed supported

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
