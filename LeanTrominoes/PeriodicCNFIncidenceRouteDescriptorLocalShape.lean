/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceHorizontalOffsets
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeLocality

/-! # Local affine shapes of forward-CNF incidence route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- The numeric route descriptor of every genuine incidence in a
forward-local formula has one of the finite local affine route shapes. -/
theorem CNFIncidence.numericRouteDescriptor_hasLocalShape_of_forward
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (forward : formula.IsForwardLocal)
    (incidence : CNFIncidence Variable)
    (incidenceMember : incidence ∈ incidencesWithMetadata formula)
    (edgeIndex : Nat) :
    RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape
      (incidence.numericRouteDescriptor formula edgeIndex) := by
  have members :=
    (mem_incidencesWithMetadata_iff formula incidence).mp incidenceMember
  have clauseMember : incidence.clause ∈ formula.clauses :=
    List.fst_mem_of_mem_zipIdx members.1
  have literalMember : incidence.literal ∈ incidence.clause :=
    List.fst_mem_of_mem_zipIdx members.2
  have offsetLocal := incidenceEdge_offset_zero_right_or_left_of_forward
    incidence.clauseIndex incidence.clause incidence.literal literalMember
    (forward incidence.clause clauseMember)
  change incidence.edge.offset = (0, 0) ∨
    incidence.edge.offset = (1, 0) ∨
    incidence.edge.offset = (-1, 0) at offsetLocal
  apply RouteDescriptor.hasLocalShape_of_horizontal_offset
  simpa [CNFIncidence.numericRouteDescriptor] using offsetLocal

/-- Every descriptor in the complete numeric route stream of a forward-local
formula has one of the finite local affine route shapes. -/
theorem numericRouteDescriptors_all_hasLocalShape
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (forward : formula.IsForwardLocal) :
    ∀ descriptor ∈ numericRouteDescriptors formula,
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor := by
  intro descriptor descriptorMember
  unfold numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, taggedMember, descriptorEq⟩
  subst descriptor
  exact CNFIncidence.numericRouteDescriptor_hasLocalShape_of_forward
    formula forward tagged.1
    (List.fst_mem_of_mem_zipIdx taggedMember) tagged.2

end PeriodicCNF
end LeanTrominoes
