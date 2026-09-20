/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Locality under clause normalization and ordering -/
namespace LeanTrominoes

theorem PeriodicClause.anchorNormalize_isLocal {V : Type*}
    {clause : PeriodicClause V} (locality : clause.IsLocal) : clause.anchorNormalize.IsLocal := by
  intro a ha b hb
  change a ∈ clause.map _ at ha
  change b ∈ clause.map _ at hb
  obtain ⟨originalA,memberA,rfl⟩ := List.mem_map.mp ha
  obtain ⟨originalB,memberB,rfl⟩ := List.mem_map.mp hb
  have bound := locality originalA memberA originalB memberB
  simpa only [offsetDistance,PeriodicLiteral.anchorNormalize_offset,Cell.sub,
    sub_sub_sub_cancel_right] using bound

theorem PeriodicCNF.anchorNormalize_isLocal {V : Type*}
    {formula : PeriodicCNF V} (locality : formula.IsLocal) : formula.anchorNormalize.IsLocal := by
  intro c hc
  change c ∈ formula.clauses.map PeriodicClause.anchorNormalize at hc
  obtain ⟨original,member,rfl⟩ := List.mem_map.mp hc
  exact PeriodicClause.anchorNormalize_isLocal (locality original member)

namespace PositionedPeriodicCNF

theorem anchorNormalize_erase_isLocal {V : Type*} {source : PositionedPeriodicCNF V}
    (placement : PeriodicVariablePlacement V) (locality : source.erase.IsLocal) :
    (source.anchorNormalize placement).erase.IsLocal := by
  rw [erase_anchorNormalize]
  exact PeriodicCNF.anchorNormalize_isLocal locality

theorem orderClausesByRouteDirection_erase_isLocal {V : Type*}
    (source : PositionedPeriodicCNF V) (routes : IncidenceRoutes)
    (locality : source.erase.IsLocal) :
    (orderClausesByRouteDirection source routes).erase.IsLocal := by
  intro c hc
  change c ∈ ((orderClausesByRouteDirection source routes).clauses.map PositionedPeriodicClause.literals) at hc
  obtain ⟨positioned,positionedMember,rfl⟩ := List.mem_map.mp hc
  change positioned ∈ source.clauses.zipIdx.map _ at positionedMember
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp positionedMember
  have original := locality tagged.1.literals
    (List.mem_map.mpr ⟨tagged.1,List.fst_mem_of_mem_zipIdx taggedMember,rfl⟩)
  have permutation := orderClauseByRouteDirection_literals_perm routes tagged.2 tagged.1
  intro a ha b hb
  exact original a (permutation.mem_iff.mp ha) b (permutation.mem_iff.mp hb)

end PositionedPeriodicCNF
end LeanTrominoes
