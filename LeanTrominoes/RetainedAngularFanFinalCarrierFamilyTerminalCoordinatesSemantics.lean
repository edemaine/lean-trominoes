/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierClauseTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation
import LeanTrominoes.RetainedAngularCarrierTaggedTerminalCoordinateFamily

/-! # Terminal coordinates of the final retained carrier family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierFamilyCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Scanning the complete final carrier clause family gives the two semantic
terminal coordinates of every tagged link in exact global clause order. -/
theorem finalCarrierTerminalCoordinates_eq_taggedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := PeriodicThreeSATThree.formula source
    let links :=
      (retainedDrawingCompleteCarrierLinks
        retained.incidenceGraph)
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaCarrierMetadataNormalizedClauses source) =
      retainedCarrierTaggedTerminalCoordinates retained links start := by
  dsimp only
  unfold retainedCarrierTaggedTerminalCoordinates
  rw [formulaCarrierMetadataNormalizedClauses,
    carrierMetadataNormalizedClauses_eq_map_taggedLinks]
  unfold retainedFinalTerminalCoordinatesFrom
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged taggedMember
  exact finalCarrierClauseTerminalCoordinates_eq
    source sourceLocal sourceWidth sourceClausesNonempty
      positiveOffsets tagged.1 tagged.2 taggedMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
