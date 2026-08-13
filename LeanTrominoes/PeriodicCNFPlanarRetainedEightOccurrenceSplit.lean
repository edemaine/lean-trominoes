/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned

/-!
# Fixed-eight occurrence splitting of retained planar SAT

The final retained planar-SAT formula has at most eight occurrences per
protovariable.  Sorting its genuine incidence routes by terminal angle
therefore assigns the eight Figure 7 ports without collisions.  This module
applies the generic fixed-eight split to that exact final formula and records
the semantic, width, occurrence, and positioning facts needed by the later
exact-one conversion.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 800000

/-- Terminal-angle order of occurrences in the final retained incidence
drawing. -/
def retainedDrawingAngularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    OccurrenceOrder
      (retainedPlanarSATFormula source) :=
  PeriodicThreeSATThree.angularOccurrenceOrder
    (retainedPlanarSATFormula source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)

/-- East-first Figure 7 port assignment induced by the retained terminal
rotation order. -/
def retainedDrawingAngularOccurrencePorts
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    OccurrencePorts :=
  occurrencePortsOfAngularOrder
    (retainedPlanarSATFormula source)
    (retainedDrawingAngularOccurrenceOrder source)

/-- Unfolding equation exposing only the computational inputs to the retained
angular port assignment. -/
theorem retainedDrawingAngularOccurrencePorts_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedDrawingAngularOccurrencePorts source =
      occurrencePortsOfAngularOrder
        (retainedPlanarSATFormula source)
        (PeriodicThreeSATThree.angularOccurrenceOrder
          (retainedPlanarSATFormula source)
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source)) :=
  rfl

/-- The final retained planar-SAT source after fixed-eight occurrence
splitting. -/
def retainedDrawingEightOccurrenceSplitFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplit.formula
    (retainedPlanarSATFormula source)
    (retainedDrawingAngularOccurrencePorts source)

/-- Unfolding equation exposing the route-induced angular occurrence split. -/
theorem retainedDrawingEightOccurrenceSplitFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedDrawingEightOccurrenceSplitFormula source =
      PeriodicEightOccurrenceSplit.formula
        (retainedPlanarSATFormula source)
        (occurrencePortsOfAngularOrder
          (retainedPlanarSATFormula source)
          (PeriodicThreeSATThree.angularOccurrenceOrder
            (retainedPlanarSATFormula source)
            (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              source))) :=
  rfl

/-- The retained terminal order fits into the eight fixed ports. -/
theorem retainedDrawingAngularOccurrenceOrder_fitsEightSlots
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FitsEightSlots
      (retainedDrawingAngularOccurrenceOrder source) := by
  have certificate :
      RetainedPlanarSATCertificate source :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have defaultBound :=
    RetainedPlanarSATCertificate.occurrencesAtMostEight
      certificate
  have bound :
      (retainedPlanarSATFormula source).OccurrencesAtMost 8 :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 8
      (retainedPlanarSATFormula source) defaultBound
  exact fitsEightSlots_of_occurrencesAtMostEight
    (retainedDrawingAngularOccurrenceOrder source)
    bound

/-- The angular port assignment is collision-free on genuine retained
occurrences. -/
theorem retainedDrawingAngularOccurrencePorts_collisionFree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingAngularOccurrencePorts source).CollisionFree
      (retainedPlanarSATFormula source) :=
  occurrencePortsOfAngularOrder_collisionFree
    (retainedPlanarSATFormula source)
    (retainedDrawingAngularOccurrenceOrder source)
    (retainedDrawingAngularOccurrenceOrder_fitsEightSlots
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Fixed-eight splitting reduces every retained protovariable to at most
three syntactic occurrences. -/
theorem retainedDrawingEightOccurrenceSplitFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingEightOccurrenceSplitFormula
      source).OccurrencesAtMost 3 :=
  PeriodicEightOccurrenceSplit.formula_occurrencesAtMostThree
    (retainedPlanarSATFormula source)
    (retainedDrawingAngularOccurrencePorts source)
    (retainedDrawingAngularOccurrencePorts_collisionFree
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Fixed-eight splitting preserves the retained width-three bound. -/
theorem retainedDrawingEightOccurrenceSplitFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceWidth : source.WidthAtMost 3) :
    (retainedDrawingEightOccurrenceSplitFormula
      source).WidthAtMost 3 :=
  PeriodicEightOccurrenceSplit.formula_widthAtMostThree
    (retainedDrawingAngularOccurrencePorts source)
    (by
      simpa only [retainedPlanarSATFormula] using
        retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_widthAtMostThree
          source sourceWidth)

/-- The retained fixed-eight formula is satisfiable exactly when the original
local 3SAT-3 source is satisfiable. -/
theorem retainedDrawingEightOccurrenceSplitFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    (retainedDrawingEightOccurrenceSplitFormula
      source).Satisfiable ↔
      source.Satisfiable := by
  exact
    (PeriodicEightOccurrenceSplit.satisfiable_iff
      (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source)).trans
      (by
        simpa only [retainedPlanarSATFormula] using
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_source_satisfiable_iff
            source
            (PeriodicCNF.incidenceGraph_isWellFormed source)
            (PeriodicCNF.incidenceGraph_degreeAtMost
              sourceWidth sourceOccurrences)
            (PeriodicCNF.incidenceGraph_isLocal sourceLocal)
            sourceOccurrences)

/-- Positioned retained split, using the uniform `24 × 24` Figure 7
refinement around each retained planar-SAT variable. -/
def retainedDrawingEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.formula
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDrawingAngularOccurrencePorts source)

/-- Placement paired with the retained fixed-eight split. -/
def retainedDrawingEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.placement
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)

@[simp]
theorem retainedDrawingEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingEightOccurrenceSplitPositionedFormula
      source).erase =
      retainedDrawingEightOccurrenceSplitFormula source := by
  unfold retainedDrawingEightOccurrenceSplitPositionedFormula
    retainedDrawingEightOccurrenceSplitFormula
  exact
    PeriodicEightOccurrenceSplitPositioned.erase_formula
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrencePorts source)

/-- The retained fixed-eight refinement has positive period. -/
theorem retainedDrawingEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedDrawingEightOccurrenceSplitPlacement source).period := by
  apply PeriodicEightOccurrenceSplitPositioned.placement_period_pos
  simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement] using
    drawingPeriodicPlanarSATPlacement_period_pos source

end PeriodicOrthocrossing
end LeanTrominoes
