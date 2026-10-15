/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarThreeDMTerminalOffsets

/-! # Nonzero incidences of one colored element have the same offset -/
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM
set_option maxHeartbeats 1000000

theorem encodedReference_offset_zero_of_local {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) (triple : Triple V) (color : WireColor)
    (localIncidence : IncidenceIsLocal source color triple) :
    (((problem source).encodeTriple triple).reference color).offset = (0,0) := by
  cases color <;> exact localIncidence.2

theorem encodedReferences_offsets_comparable {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3)
    {first second : Triple V} (firstMember : first ∈ triples source) (secondMember : second ∈ triples source)
    (color : WireColor)
    (atomEq : (((problem source).encodeTriple first).reference color).atom =
      (((problem source).encodeTriple second).reference color).atom) :
    (((problem source).encodeTriple first).reference color).offset = (0,0) ∨
      (((problem source).encodeTriple second).reference color).offset = (0,0) ∨
      (((problem source).encodeTriple first).reference color).offset =
        (((problem source).encodeTriple second).reference color).offset := by
  rcases triple_incidence_local_or_routed source first firstMember color with firstLocal | firstRouted
  · exact Or.inl (encodedReference_offset_zero_of_local source first color firstLocal)
  rcases triple_incidence_local_or_routed source second secondMember color with secondLocal | secondRouted
  · exact Or.inr (Or.inl (encodedReference_offset_zero_of_local source second color secondLocal))
  obtain ⟨firstAtom,firstSlot,_,firstUsed,rfl⟩ := firstRouted
  obtain ⟨secondAtom,secondSlot,_,secondUsed,rfl⟩ := secondRouted
  rw [encodeTriple_routedOccurrence_reference,encodeTriple_routedOccurrence_reference] at atomEq ⊢
  exact Or.inr (Or.inr (occurrenceReverseOffset_eq_of_elementIndex_eq width firstUsed secondUsed color atomEq))

theorem encoded_incidence_reference {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) (color : WireColor) (atom : Nat) {incidence : PeriodicThreeDM.Incidence}
    (member : incidence ∈ (encodedProblem source).incidences color atom) :
    ∃ triple ∈ triples source,
      (((problem source).encodeTriple triple).reference color).atom = atom ∧
        incidence.offset = (((problem source).encodeTriple triple).reference color).offset := by
  simp only [PeriodicThreeDM.incidences,List.mem_filterMap] at member
  obtain ⟨index,indexMember,output⟩ := member
  have bound : index < (triples source).length := by
    simpa only [encodedProblem,TypedProblem.encode,problem,List.length_map] using List.mem_range.mp indexMember
  have lookup : (encodedProblem source).triples.getD index default =
      (problem source).encodeTriple ((triples source)[index]) := by
    rw [List.getD_eq_getElem _ _ (List.mem_range.mp indexMember)]
    simp only [encodedProblem,TypedProblem.encode,List.getElem_map,problem]
  split at output
  · rename_i same
    simp only [Option.some.injEq] at output
    subst incidence
    exact ⟨_,List.getElem_mem bound,by simpa only [lookup] using same,by rw [lookup]⟩
  · contradiction

theorem encoded_incidence_offsets_comparable {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3) (color : WireColor) (atom : Nat)
    {first second : PeriodicThreeDM.Incidence}
    (firstMember : first ∈ (encodedProblem source).incidences color atom)
    (secondMember : second ∈ (encodedProblem source).incidences color atom) :
    first.offset = (0,0) ∨ second.offset = (0,0) ∨ first.offset = second.offset := by
  obtain ⟨firstTriple,firstTripleMember,firstAtom,firstOffset⟩ := encoded_incidence_reference source color atom firstMember
  obtain ⟨secondTriple,secondTripleMember,secondAtom,secondOffset⟩ := encoded_incidence_reference source color atom secondMember
  rw [firstOffset,secondOffset]
  exact encodedReferences_offsets_comparable width firstTripleMember secondTripleMember color (firstAtom.trans secondAtom.symm)

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
