/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterization

/-!
# Lookup correctness for normalized 3DM assignments

The rasterizer represents the finite normalized drawing by a list of
location/cell assignments.  This module isolates the exact combinatorial
condition needed to read that list without ambiguity: assigned torus
locations must be duplicate-free.  Under that condition every listed vertex
or route-interior assignment is recovered exactly by `finalCellTypeAt`.

The later geometric separation argument therefore has one explicit target,
`FinalAssignmentsCollisionFree`, rather than having to reason about lookup
priority at every use site.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A successful key lookup comes from a pair in the original association
list.  Unlike the converse lookup lemma below, this direction needs no
duplicate-freedom hypothesis. -/
theorem List.mem_of_lookup_eq_some
    {α β : Type*} [BEq α] [LawfulBEq α]
    {entries : List (α × β)} {key : α} {value : β}
    (lookup : entries.lookup key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp at lookup
  | cons entry entries inductionHypothesis =>
      obtain ⟨entryKey, entryValue⟩ := entry
      by_cases equal : key = entryKey
      · subst entryKey
        simp only [List.lookup_cons, beq_self_eq_true,
          Option.some.injEq] at lookup
        subst entryValue
        simp
      · have beqFalse : (key == entryKey) = false :=
          beq_eq_false_iff_ne.mpr equal
        simp only [List.lookup_cons, beqFalse] at lookup
        exact List.mem_cons_of_mem _ (inductionHypothesis lookup)

/-- A key-value list with no repeated keys returns the value of every pair
that occurs in the list. -/
theorem List.lookup_eq_some_of_mem_of_nodup_keys
    {α β : Type*} [BEq α] [LawfulBEq α]
    {entries : List (α × β)} {key : α} {value : β}
    (member : (key, value) ∈ entries)
    (keysNodup : (entries.map Prod.fst).Nodup) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries inductionHypothesis =>
      obtain ⟨entryKey, entryValue⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at keysNodup
      rcases keysNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at member
      rcases member with pairEqual | tailMember
      · cases pairEqual
        simp
      · have keysDifferent : key ≠ entryKey := by
          intro equal
          apply headFresh
          rw [← equal]
          exact List.mem_map.mpr ⟨(key, value), tailMember, rfl⟩
        have beqFalse : (key == entryKey) = false :=
          beq_eq_false_iff_ne.mpr keysDifferent
        simp [List.lookup_cons, beqFalse,
          inductionHypothesis tailMember tailNodup]

/-- Torus locations occurring in the normalized assignment list, in lookup
order. -/
def PlanarPresentation.finalAssignmentLocations
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  presentation.finalCellAssignments.map Prod.fst

/-- The precise collision-freedom obligation for rasterizing a normalized
presentation: no two vertex or route-interior assignments occupy the same
torus location. -/
def PlanarPresentation.FinalAssignmentsCollisionFree
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : Prop :=
  presentation.finalAssignmentLocations.Nodup

/-- Every collision-free listed assignment is returned exactly by the total
cell lookup. -/
theorem PlanarPresentation.finalCellTypeAt_eq_of_mem
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {location : Cell} {cellType : OrthogonalCellType}
    (member : (location, cellType) ∈ presentation.finalCellAssignments) :
    presentation.finalCellTypeAt location = cellType := by
  have lookup := List.lookup_eq_some_of_mem_of_nodup_keys member collisionFree
  simp [PlanarPresentation.finalCellTypeAt, lookup]

/-- A contracted vertex contributes its advertised final assignment. -/
theorem PlanarPresentation.finalVertexAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    (rasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex),
      presentation.finalVertexCellType vertex) ∈
      presentation.finalCellAssignments := by
  simp only [PlanarPresentation.finalCellAssignments, List.mem_append]
  left
  exact List.mem_map.mpr ⟨vertex, member, rfl⟩

/-- Under collision freedom, the compiled cell at every contracted vertex is
exactly its trichromatic or monochromatic degree-three vertex cell. -/
theorem PlanarPresentation.finalCellTypeAt_vertex
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.finalCellTypeAt
        (rasterLocation presentation.finalNormalizationPeriod
          (presentation.finalNormalizationPosition vertex)) =
      presentation.finalVertexCellType vertex :=
  presentation.finalCellTypeAt_eq_of_mem collisionFree
    (presentation.finalVertexAssignment_mem member)

/-- Every assignment emitted for the interior of a listed normalized edge is
part of the combined final assignment list. -/
theorem PlanarPresentation.routeInteriorAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {assignment : NormalizedCellAssignment}
    (assignmentMember : assignment ∈
      routeInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge)) :
    assignment ∈ presentation.finalCellAssignments := by
  simp only [PlanarPresentation.finalCellAssignments, List.mem_append]
  right
  simp only [PlanarPresentation.finalRouteAssignments, List.mem_flatMap]
  exact ⟨edge, edgeMember, assignmentMember⟩

/-- Under collision freedom, every emitted route-interior assignment is
returned exactly by the compiled lookup. -/
theorem PlanarPresentation.finalCellTypeAt_routeInterior
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {location : Cell} {cellType : OrthogonalCellType}
    (assignmentMember : (location, cellType) ∈
      routeInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge)) :
    presentation.finalCellTypeAt location = cellType :=
  presentation.finalCellTypeAt_eq_of_mem collisionFree
    (presentation.routeInteriorAssignment_mem edgeMember assignmentMember)

end PeriodicThreeDM
end LeanTrominoes
