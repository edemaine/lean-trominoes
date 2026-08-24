/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorTargetPermutation

/-! # Looking up occurrence descriptors by target index -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every valid rotated occurrence-copy index has an occurrence-prefix
descriptor targeting it. -/
theorem exists_occurrenceRouteDescriptor_targetVertexIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (targetIndex : Nat)
    (targetIndexLt :
      targetIndex < PeriodicCNF.presentationLiteralCount source) :
    ∃ descriptor ∈ occurrenceRouteDescriptors source,
      descriptor.targetVertexIndex = targetIndex := by
  have rangeMember : targetIndex ∈
      List.range (PeriodicCNF.presentationLiteralCount source) :=
    List.mem_range.mpr targetIndexLt
  have mappedMember : targetIndex ∈
      (occurrenceRouteDescriptors source).map
        RouteDescriptor.targetVertexIndex :=
    (occurrenceRouteDescriptors_targetVertexIndices_perm_range
      source).mem_iff.mpr rangeMember
  rcases List.mem_map.mp mappedMember with
    ⟨descriptor, descriptorMember, descriptorTarget⟩
  exact ⟨descriptor, descriptorMember, descriptorTarget⟩

/-- Target vertex index is injective on occurrence-prefix descriptors. -/
theorem occurrenceRouteDescriptor_eq_of_targetVertexIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {first second : RouteDescriptor}
    (firstMember : first ∈ occurrenceRouteDescriptors source)
    (secondMember : second ∈ occurrenceRouteDescriptors source)
    (targetEq : first.targetVertexIndex = second.targetVertexIndex) :
    first = second := by
  exact List.inj_on_of_nodup_map
    (occurrenceRouteDescriptors_targetVertexIndices_nodup source)
    firstMember secondMember targetEq

end PeriodicThreeSATThree
end LeanTrominoes
