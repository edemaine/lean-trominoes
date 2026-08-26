/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationArmClassification
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNumericArmOrder
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedLinks
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteFiberArms

/-! # Arm order of canonical routed-variable links -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- At the final neighboring site of one genuine copied occurrence, the
normalized active links have the complete left/middle/right arm order. -/
theorem routedVariableFinalSiteNormalizedLinkArms_eq_full
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    (((routedVariableLinksAt (formula source) (atom, (1, 1))).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization (formula source)))).map
        wrappedNormalizedRoutedVariableLinkArm) =
      routedVariableFullSiteArms := by
  have finalSiteMember : (atom, (1, 1)) ∈
      drawingVariableRouteSites (formula source) := by
    rw [drawingVariableRouteSites_formula_eq_boundary_append_rotated
      source positiveOffsets]
    apply List.mem_append.mpr
    right
    unfold rotatedVariableRouteSiteBlocks
    apply List.mem_flatMap.mpr
    refine ⟨atom, atomMember, ?_⟩
    simp [variableRouteSiteBlock, neighborTranslations,
      neighborCoordinates, Cell.add]
  have linkGlobalMember : ∀ link ∈
      routedVariableLinksAt (formula source) (atom, (1, 1)),
      link ∈ drawingRoutedVariableLinks (formula source) := by
    intro link linkMember
    unfold drawingRoutedVariableLinks
    exact List.mem_flatMap.mpr
      ⟨(atom, (1, 1)), finalSiteMember, linkMember⟩
  calc
    (((routedVariableLinksAt (formula source) (atom, (1, 1))).map
          (PeriodicEquality.normalizeLink
            (externalWrappedVariableNormalization (formula source)))).map
          wrappedNormalizedRoutedVariableLinkArm) =
        (routedVariableLinksAt
          (formula source) (atom, (1, 1))).map
            (fun link => link.first.duplicatorArm) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro link linkMember
      simp only [Function.comp_apply]
      exact wrappedNormalizedRoutedVariableLinkArm_normalizeLink
        (formula source) link (linkGlobalMember link linkMember)
    _ = ((variableRouteOccurrencesAt
          (formula source) (atom, (1, 1))).take 3).map
          (fun occurrence =>
            targetDuplicatorArm
              (occurrence.incidence.numericRouteDescriptor
                (formula source) occurrence.edgeIndex).targetPortRank) :=
      routedVariableLinksAt_arms_eq_numericTargetPortRankArms
        (formula source) (atom, (1, 1))
    _ = routedVariableFullSiteArms := by
      have atomAllMember :=
        (mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
          source atom).mp atomMember
      rcases occurrenceIncidenceAtAtom_eq_some
          source atom atomAllMember with
        ⟨selected, selectedMember, selectedAtom, _lookup⟩
      rw [← selectedAtom]
      rw [variableRouteOccurrenceNumericArmsTakeThreeAt_formula_eq
        source selected selectedMember]
      rcases positiveOffsets selected.1
          (List.fst_mem_of_mem_zipIdx selectedMember) with
        offsetZero | offsetOne
      · rw [offsetZero]
        native_decide
      · rw [offsetOne]
        native_decide

/-- Concatenating the canonical final-site normalized links over rotated
occurrences yields one complete arm triple per occurrence. -/
theorem canonicalWrappedNormalizedRoutedVariableLinkArms_eq_fullSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (canonicalWrappedNormalizedRoutedVariableLinks source).map
        wrappedNormalizedRoutedVariableLinkArm =
      (rotatedOccurrenceVariables source).flatMap
        (fun _atom => routedVariableFullSiteArms) := by
  unfold canonicalWrappedNormalizedRoutedVariableLinks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom atomMember
  exact routedVariableFinalSiteNormalizedLinkArms_eq_full
    source positiveOffsets atom atomMember

end LeanTrominoes.PeriodicThreeSATThree
