/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATDuplicatorArmData

/-! # Finite routed-variable site-arm scans -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- The active arms at one site reached by all three split incidences. -/
def routedVariableFullSiteArms : List DuplicatorArm :=
  [.left, .middle, .right]

/-- The active cycle arms at a site not reached by a next-slice copied
incidence. -/
def routedVariableCycleOnlySiteArms : List DuplicatorArm :=
  [.middle, .right]

/-- The three copied-incidence-only sites beyond the right boundary. -/
def routedVariableNextBoundarySiteArmBlocks :
    List (List DuplicatorArm) :=
  List.replicate 3 [.left]

/-- Nine complete sites for a current-slice copied incidence. -/
def routedVariableCurrentCycleSiteArmBlocks :
    List (List DuplicatorArm) :=
  List.replicate 9 routedVariableFullSiteArms

/-- Three cycle-only sites followed by six complete sites for a next-slice
copied incidence. -/
def routedVariableNextCycleSiteArmBlocks :
    List (List DuplicatorArm) :=
  List.replicate 3 routedVariableCycleOnlySiteArms ++
    List.replicate 6 routedVariableFullSiteArms

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
