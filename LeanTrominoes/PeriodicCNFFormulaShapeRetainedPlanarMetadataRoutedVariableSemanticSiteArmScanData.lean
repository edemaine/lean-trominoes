/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableGadgets
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry

/-! # Semantic routed-variable site-arm scans -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Active routed-variable link arms, grouped in exact site presentation
order. -/
def routedVariableSemanticSiteArmScan
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List (List DuplicatorArm) :=
  (drawingVariableRouteSites formula).map fun site =>
    (routedVariableLinksAt formula site).map fun link =>
      link.first.duplicatorArm

/-- Numeric target-rank arms of the selected routed occurrences, grouped in
the same site presentation order. -/
def routedVariableNumericOccurrenceSiteArmScan
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List (List DuplicatorArm) :=
  (drawingVariableRouteSites formula).map fun site =>
    ((variableRouteOccurrencesAt formula site).take 3).map fun occurrence =>
      targetDuplicatorArm
        (occurrence.incidence.numericRouteDescriptor
          formula occurrence.edgeIndex).targetPortRank

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
