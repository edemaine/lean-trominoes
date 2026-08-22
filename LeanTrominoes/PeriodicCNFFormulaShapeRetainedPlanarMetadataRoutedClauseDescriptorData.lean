/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRouteDirections

/-! # Finite retained routed-clause descriptor data -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- Pack a source clause's normalized finite literal profiles with the fixed
invalid axis-direction annotation of every direct clause-star ray. -/
def routedClauseDescriptor
    (profiles : List LiteralProfile) :
    FormulaShapeDirectionOrdering.Token :=
  .clause
    (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
      (profiles.map fun profile => (profile, .invalid)))

/-- The finite routed-clause token read from one normalized source-clause
prototype. -/
def canonicalRoutedClauseDescriptor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    FormulaShapeDirectionOrdering.Token :=
  routedClauseDescriptor
    ((normalizedRoutedClauseAt source site).map
      FormulaShapeDirectionOrdering.literalProfile)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
