/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableAtomNormalization
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNodeOrder
import LeanTrominoes.PeriodicCNFRouteDescriptorTargetTerminalCompactAtomWordSemantics

/-! # Compact atom words of normalized routed-variable links -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT
open FormulaShapeRetainedPlanarMetadataDirection

private theorem taggedIncidence_mem_of_variableRouteOccurrence
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site) :
    (occurrence.incidence, occurrence.edgeIndex) ∈
      formula.incidencesWithMetadata.zipIdx := by
  have drawingMember :=
    (variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember).1
  unfold drawingCNFRouteOccurrences at drawingMember
  rcases List.mem_flatMap.mp drawingMember with
    ⟨taggedIncidence, taggedMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  exact taggedMember

/-- At one represented variable site, normalized equality-link endpoint
words are exactly the target-terminal/source-atom blocks of the selected
route occurrences, in their existing order. -/
theorem routedVariableLinksAt_compactAtomWords_eq_occurrences
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (isLocal : formula.incidenceGraph.IsLocal)
    (sourceWord : Variable → List Bool)
    (site : VariableRouteSite Variable)
    (siteMember : site ∈ drawingVariableRouteSites formula) :
    ((routedVariableLinksAt formula site).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization formula))).flatMap
        (fun link =>
          [RetainedCompactAtomWords.word sourceWord link.first,
            RetainedCompactAtomWords.word sourceWord link.second,
            RetainedCompactAtomWords.word sourceWord link.first,
            RetainedCompactAtomWords.word sourceWord link.second]) =
      ((variableRouteOccurrencesAt formula site).take 3).flatMap
        (fun occurrence =>
          [RouteDescriptorPairAffine.routeDescriptorTargetTerminalCompactAtomWord
                (occurrence.incidence.numericRouteDescriptor
                  formula occurrence.edgeIndex),
            RetainedCompactAtomWords.word sourceWord
              ⟨PeriodicPlanarSATVariable.atom site.1⟩,
            RouteDescriptorPairAffine.routeDescriptorTargetTerminalCompactAtomWord
                (occurrence.incidence.numericRouteDescriptor
                  formula occurrence.edgeIndex),
            RetainedCompactAtomWords.word sourceWord
              ⟨PeriodicPlanarSATVariable.atom site.1⟩]) := by
  unfold routedVariableLinksAt
  rw [routedVariableNodes_eq_map_targetTerminals]
  unfold equalityTakeThreeLinks
  rw [← List.map_take]
  rw [List.map_map]
  rw [List.flatMap_map]
  change
    ((((variableRouteOccurrencesAt formula site).take 3).map
      (fun occurrence =>
        PlanarSATNode.carrier
          (.terminal (occurrence.targetTerminal formula)))).zipIdx).flatMap
        (fun taggedNode =>
          let link : EqualityLink (PlanarSATNode Variable) :=
            ⟨taggedNode.1, .atom site,
              routedVariableEqualityPositions formula site
                taggedNode.1.duplicatorArm⟩
          [RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula link.first).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula link.second).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula link.first).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula link.second).1]) = _
  rw [show
      (((variableRouteOccurrencesAt formula site).take 3).map
          (fun occurrence =>
            PlanarSATNode.carrier
              (.terminal (occurrence.targetTerminal formula)))).zipIdx =
        (((variableRouteOccurrencesAt formula site).take 3).zipIdx.map
          fun taggedOccurrence =>
            (PlanarSATNode.carrier
              (.terminal (taggedOccurrence.1.targetTerminal formula)),
              taggedOccurrence.2)) by
    rw [List.zipIdx_map]
    rfl]
  rw [List.flatMap_map]
  calc
    (((variableRouteOccurrencesAt formula site).take 3).zipIdx.flatMap
        (fun taggedOccurrence =>
          [RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (taggedOccurrence.1.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (taggedOccurrence.1.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1])) =
      (((variableRouteOccurrencesAt formula site).take 3).zipIdx.map
        Prod.fst).flatMap (fun occurrence =>
          [RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (occurrence.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (occurrence.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1]) := by
        rw [List.flatMap_map]
    _ = ((variableRouteOccurrencesAt formula site).take 3).flatMap
        (fun occurrence =>
          [RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (occurrence.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (occurrence.targetTerminal formula)))).1,
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.atom site)).1]) := by
        rw [List.zipIdx_map_fst]
    _ = _ := by
      apply List.flatMap_congr
      intro occurrence occurrenceMember
      have occurrenceMemberFull :
          occurrence ∈ variableRouteOccurrencesAt formula site :=
        List.mem_of_mem_take occurrenceMember
      have taggedMember := taggedIncidence_mem_of_variableRouteOccurrence
        formula site occurrence occurrenceMemberFull
      rw [numericRouteDescriptor_targetTerminalCompactAtomWord
        formula wellFormed sourceWord occurrence.translate
        (occurrence.incidence, occurrence.edgeIndex) taggedMember]
      rw [externalWrappedVariableNormalization_atom_eq
        formula wellFormed isLocal site siteMember]

end PeriodicCNF
end LeanTrominoes
