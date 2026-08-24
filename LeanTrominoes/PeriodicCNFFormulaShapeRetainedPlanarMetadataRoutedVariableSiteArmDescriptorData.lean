/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmScanData

/-! # Descriptor interpretation of routed-variable site arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- Descriptor output obtained from an ordered list of active arms at every
routed-variable site. -/
def routedVariableSiteArmDescriptorStream
    (siteArms : List (List DuplicatorArm)) :
    List FormulaShapeDirectionOrdering.Token :=
  siteArms.flatMap fun arms =>
    arms.flatMap routedVariableCurrentArmBlock

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
