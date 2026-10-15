/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMOneDimensional
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicOneInThreePolarityNormalizationRibbonThreeDM
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreePolarityNormalizationFreshGaugeLocality
import LeanTrominoes.SAT.CNF.PeriodicCNFUnitOffsetBounds
import LeanTrominoes.ThreeDM.Line.PeriodicThreeDMLineDecision

/-! # Manhattan locality of the planar 3DM gadget assembly

Internal references have zero offset. Connector references reverse one
source-literal offset. Clause anchoring turns pairwise CNF locality into
the unit-radius bound required by graph locality.
-/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

theorem occurrenceReverseOffset_isUnitOffset {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (bounds : source.HasUnitOffsets)
    (atom : V) (slot : OccurrenceSlot) :
    (occurrenceReverseOffset source atom slot).IsUnitOffset := by
  cases lookup : occurrenceAt source atom slot with
  | none => simp [occurrenceReverseOffset, lookup, Cell.IsUnitOffset]
  | some tagged =>
      have coreLookup : PeriodicOneInThreeToThreeDM.occurrenceAt source atom slot =
          some tagged := by simpa [occurrenceAt] using lookup
      have member := (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
        source atom slot tagged coreLookup).1
      simp only [PeriodicThreeSATThree.taggedLiterals, List.mem_flatMap] at member
      obtain ⟨clause, clauseMember, member⟩ := member
      obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
      have bound := bounds clause.1 (List.fst_mem_of_mem_zipIdx clauseMember)
        literal.1 (List.fst_mem_of_mem_zipIdx literalMember)
      simpa [occurrenceReverseOffset, lookup, PeriodicOneInThreeToThreeDM.reverseOffset,
        Cell.IsUnitOffset] using bound

theorem tripleReferences_isLocal {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (bounds : source.HasUnitOffsets) (triple : Triple V) :
    let references := tripleReferences source triple
    references.red.offset.IsUnitOffset ∧ references.green.offset.IsUnitOffset ∧
      references.blue.offset.IsUnitOffset := by
  cases triple with
  | ordinary atom slot variant triple =>
      have terminal := occurrenceReverseOffset_isUnitOffset bounds atom slot
      have conditional (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot else (0, 0)).IsUnitOffset := by
        split_ifs
        · exact terminal
        · simp [Cell.IsUnitOffset]
      simp only [tripleReferences, ordinaryTripleReferences]
      exact ⟨conditional _, conditional _, conditional _⟩
  | fixedRed atom slot triple =>
      have terminal := occurrenceReverseOffset_isUnitOffset bounds atom slot
      have conditional (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot else (0, 0)).IsUnitOffset := by
        split_ifs
        · exact terminal
        · simp [Cell.IsUnitOffset]
      simp only [tripleReferences, fixedRedTripleReferences]
      exact ⟨conditional _, conditional _, conditional _⟩
  | clause clauseIndex set =>
      simp [tripleReferences, clauseTripleReferences, Cell.IsUnitOffset]

theorem encodedProblem_isLocal {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (bounds : source.HasUnitOffsets) :
    (encodedProblem source).IsLocal := by
  intro encoded member color
  simp only [encodedProblem, TypedProblem.encode, List.mem_map] at member
  obtain ⟨triple, _, rfl⟩ := member
  have references := tripleReferences_isLocal bounds triple
  cases color with
  | red => simpa [TypedProblem.encodeTriple, encodeReference,
      PeriodicThreeDMTriple.reference, problem, Cell.IsUnitOffset] using references.1
  | green => simpa [TypedProblem.encodeTriple, encodeReference,
      PeriodicThreeDMTriple.reference, problem, Cell.IsUnitOffset] using references.2.1
  | blue => simpa [TypedProblem.encodeTriple, encodeReference,
      PeriodicThreeDMTriple.reference, problem, Cell.IsUnitOffset] using references.2.2

theorem normalizedProblem_isLocal {V : Type*} [DecidableEq V]
    {source : PositionedPeriodicCNF V} (placement : PeriodicVariablePlacement V)
    (locality : source.erase.IsLocal) : (normalizedProblem source placement).IsLocal := by
  apply encodedProblem_isLocal
  rw [normalizedSource_eq]
  exact PeriodicCNF.anchorNormalize_hasUnitOffsets locality

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

theorem paddedPeriodicThreeDMProblem_isLocal {V : Type*} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (locality : source.erase.IsLocal)
    (nonempty : ∀ clause ∈ source.erase.clauses, clause ≠ []) :
    (paddedPeriodicThreeDMProblem source placement routes).IsLocal := by
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isLocal
  rw [PositionedPeriodicCNF.erase_scale]
  exact formula_erase_isLocal source placement routes locality nonempty

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
