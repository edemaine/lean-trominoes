/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableAtomNormalization
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-! # Relative offsets of routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Both endpoints of an active routed-variable arm normalize to the same
lifted site offset. -/
theorem routedVariableLink_relativeOffset_eq_zero
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal)
    (site : VariableRouteSite Variable)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMember : link ∈ routedVariableLinksAt source site) :
    (PeriodicEquality.normalizeLink
      (externalWrappedVariableNormalization source) link).relativeOffset =
        (0, 0) := by
  rw [routedVariableLinksAt] at linkMember
  rcases List.mem_map.mp linkMember with
    ⟨taggedNode, taggedNodeMember, linkEq⟩
  subst link
  have nodeMember :
      taggedNode.1 ∈ routedVariableNodes source site :=
    List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMember)
  rcases (mem_routedVariableNodes_iff
      source site taggedNode.1).mp nodeMember with
    ⟨occurrence, occurrenceAtMember, nodeEq⟩
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      source site occurrenceAtMember
  have siteMember : site ∈ drawingVariableRouteSites source := by
    rw [drawingVariableRouteSites, List.mem_dedup]
    exact List.mem_map.mpr
      ⟨occurrence, occurrenceData.1, occurrenceData.2⟩
  rw [drawingCNFRouteOccurrences, List.mem_flatMap]
      at occurrenceData
  rcases occurrenceData.1 with
    ⟨taggedIncidence, taggedMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  change Cell.sub
      (externalWrappedVariableNormalization source (.atom site)).2
      (externalWrappedVariableNormalization source taggedNode.1).2 =
    (0, 0)
  rw [nodeEq]
  rw [externalWrappedVariableNormalization_atom_eq
    source wellFormed isLocal site siteMember]
  rw [externalWrappedVariableNormalization_targetTerminal_eq
    source wellFormed taggedIncidence taggedMember translate]
  have siteEq := occurrenceData.2
  rw [siteEq]
  simp [Cell.sub]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
