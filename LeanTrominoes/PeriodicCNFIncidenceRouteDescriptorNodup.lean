/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingBendNormalizationDegree

/-! # Distinct stored indices of numeric incidence-route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- Numeric incidence descriptors are duplicate-free because each stores its
own unique presentation index. -/
theorem numericRouteDescriptors_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (numericRouteDescriptors formula).Nodup := by
  unfold numericRouteDescriptors
  have taggedNodup :
      formula.incidencesWithMetadata.zipIdx.Nodup :=
    (List.nodup_zipIdx_map_snd
      formula.incidencesWithMetadata).of_map
  apply taggedNodup.map_on
  intro first firstMember second secondMember descriptorsEqual
  have indicesEqual :=
    congrArg RouteDescriptor.edgeIndex descriptorsEqual
  have indicesEqual' : first.2 = second.2 := by
    simpa [CNFIncidence.numericRouteDescriptor] using indicesEqual
  exact tagged_eq_of_mem_zipIdx_of_snd_eq
    firstMember secondMember indicesEqual'

/-- Among listed numeric incidence descriptors, equality of stored edge
indices already identifies the complete descriptor. -/
theorem numericRouteDescriptors_eq_of_edgeIndex_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : RouteDescriptor}
    (firstMember : first ∈ numericRouteDescriptors formula)
    (secondMember : second ∈ numericRouteDescriptors formula)
    (edgeIndexEq : first.edgeIndex = second.edgeIndex) :
    first = second := by
  unfold numericRouteDescriptors at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstTagged, firstTaggedMember, firstEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondTagged, secondTaggedMember, secondEq⟩
  subst first
  subst second
  have indicesEqual : firstTagged.2 = secondTagged.2 := by
    simpa [CNFIncidence.numericRouteDescriptor] using edgeIndexEq
  have taggedEqual := tagged_eq_of_mem_zipIdx_of_snd_eq
    firstTaggedMember secondTaggedMember indicesEqual
  subst secondTagged
  rfl

end PeriodicCNF
end LeanTrominoes
