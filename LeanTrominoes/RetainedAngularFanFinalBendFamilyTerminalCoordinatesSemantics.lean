/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendClauseTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation
import LeanTrominoes.RetainedAngularBendTerminalCoordinateFamily

/-! # Terminal coordinates of the final retained bend family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendFamilyCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Scanning the complete final base-bend clause family gives the two semantic
terminal coordinates of every tagged bend in exact global clause order. -/
theorem finalBendTerminalCoordinates_eq_taggedBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := PeriodicThreeSATThree.formula source
    let bends := baseRouteBends retained
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length +
        (formulaCarrierMetadataNormalizedClauses source).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaBaseBendNormalizedClauses source) =
      retainedBendTaggedTerminalCoordinates bends start := by
  dsimp only
  unfold retainedBendTaggedTerminalCoordinates
  rw [formulaBaseBendNormalizedClauses,
    baseBendNormalizedClauses_eq_map_baseTaggedBends]
  unfold retainedFinalTerminalCoordinatesFrom
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged taggedMember
  exact finalBendClauseTerminalCoordinates_eq
    source sourceLocal sourceWidth sourceClausesNonempty
      positiveOffsets tagged.1 tagged.2 taggedMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
