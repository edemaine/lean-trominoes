/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Proof-free stored edge routes for the horizontal source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Typed triples of the proof-free normalized horizontal source. -/
def horizontalThreeDMTypedTriplesComputed
    (source : PeriodicCNF Nat) : List (Triple RoutedVariable) :=
  triples (horizontalNormalizedRoutedFormulaComputed source).erase

/-- Total tag lookup in the proof-free typed triple list. -/
def horizontalAssembledRouteTriple?Computed
    (input : PeriodicCNF Nat × PeriodicThreeDM.IncidenceTag) :
    Option (Triple RoutedVariable) :=
  (horizontalThreeDMTypedTriplesComputed input.1)[input.2.tripleIndex]?

/-- Complete proof-free route selected by one encoded incidence tag. -/
def horizontalAssembledRouteAtTagComputed
    (input : PeriodicCNF Nat × PeriodicThreeDM.IncidenceTag) : List Cell :=
  match horizontalAssembledRouteTriple?Computed input with
  | none => []
  | some triple =>
      horizontalTypedIncidenceRouteComputed
        ((input.1, triple), input.2.color)

/-- Encoded periodic 3DM problem of the normalized horizontal source. -/
def horizontalThreeDMProblemComputed
    (source : PeriodicCNF Nat) : PeriodicThreeDM :=
  encodedProblem (horizontalNormalizedRoutedFormulaComputed source).erase

/-- Stable incidence-tag order of the encoded horizontal 3DM problem. -/
def horizontalThreeDMIncidenceTagsComputed
    (source : PeriodicCNF Nat) : List PeriodicThreeDM.IncidenceTag :=
  (horizontalThreeDMProblemComputed source).incidenceTags

/-- Complete stored edge-route list in encoded incidence-tag order. -/
def horizontalThreeDMEdgeRoutesComputed
    (source : PeriodicCNF Nat) : List (List Cell) :=
  (horizontalThreeDMIncidenceTagsComputed source).map fun tag =>
    horizontalAssembledRouteAtTagComputed (source, tag)

end PeriodicCNFStripReduction
end LeanTrominoes
