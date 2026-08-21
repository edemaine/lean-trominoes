/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices
import LeanTrominoes.PeriodicCNFRenamingStreams
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorExt

/-! # Numeric route descriptors are invariant under injective atom renaming -/

namespace LeanTrominoes

namespace PeriodicCNF

@[simp] theorem clauseAnchor_renameClause
    {Source Target : Type*} (variableMap : Source → Target)
    (clause : PeriodicClause Source) :
    clauseAnchor (renameClause variableMap clause) = clauseAnchor clause := by
  cases clause <;> rfl

end PeriodicCNF

namespace CNFIncidence

/-- Every numeric field of one incidence route is unchanged by an injective
atom renaming. -/
theorem numericRouteDescriptor_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (formula : PeriodicCNF Source) (incidence : CNFIncidence Source)
    (edgeIndex : Nat) :
    (incidence.rename variableMap).numericRouteDescriptor
        (formula.rename variableMap) edgeIndex =
      incidence.numericRouteDescriptor formula edgeIndex := by
  have countTake (values : List Source) (count : Nat) (value : Source) :
      ((values.map variableMap).take count).count (variableMap value) =
        (values.take count).count value := by
    rw [← List.map_take]
    exact List.count_map_of_injective
      (values.take count) variableMap injective value
  apply PeriodicOrthocrossing.RouteDescriptor.ext
  all_goals
    simp [numericRouteDescriptor,
      PeriodicCNF.variableOccurrences_rename,
      PeriodicCNF.incidencesWithMetadata_rename,
      List.dedup_map_of_injective injective,
      List.idxOf_map_of_injective variableMap injective,
      countTake, List.map_map, Function.comp_def,
      CNFIncidence.rename, PeriodicLiteral.rename,
      PeriodicCNF.clauseAnchor_renameClause]

end CNFIncidence

namespace PeriodicCNF

/-- The complete numeric route stream depends only on the presentation shape,
offsets, and atom-equality pattern. -/
theorem numericRouteDescriptors_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (formula : PeriodicCNF Source) :
    numericRouteDescriptors (rename variableMap formula) =
      numericRouteDescriptors formula := by
  unfold numericRouteDescriptors
  rw [incidencesWithMetadata_rename, List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro tagged taggedMember
  rcases tagged with ⟨incidence, edgeIndex⟩
  exact CNFIncidence.numericRouteDescriptor_rename_of_injective
    variableMap injective formula incidence edgeIndex

end PeriodicCNF
end LeanTrominoes
