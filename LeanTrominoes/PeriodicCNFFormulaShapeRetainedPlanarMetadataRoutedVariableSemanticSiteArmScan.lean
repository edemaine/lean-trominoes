/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSemanticSiteArmScanData
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNumericArmOrder

/-! # Numeric interpretation of semantic routed-variable arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- At every represented site, actual active-link arms are exactly the arms
read from the selected incidences' numeric target-port ranks. -/
theorem routedVariableSemanticSiteArmScan_eq_numericOccurrence
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    routedVariableSemanticSiteArmScan formula =
      routedVariableNumericOccurrenceSiteArmScan formula := by
  unfold routedVariableSemanticSiteArmScan
    routedVariableNumericOccurrenceSiteArmScan
  apply List.map_congr_left
  intro site _siteMember
  exact routedVariableLinksAt_arms_eq_numericTargetPortRankArms
    formula site

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
