/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGeometry
import LeanTrominoes.PeriodicPlanarSATOrbitCoRE
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability

/-! # Computable ordinary planar 3SAT-3 endpoint -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
open PeriodicOrthocrossing
set_option maxHeartbeats 300000
variable {V : Type} [Primcodable V] [DecidableEq V]

def input (f : PeriodicCNF V) : Input (Target V) := ((formula f).erase,drawing f)

theorem drawing_primrec : Primrec (drawing (V := V)) :=
  PositionedPeriodicCNF.incidenceDrawing_primrec (formula (V := V)) retainedFigureNineClearancePositionedFormula_primrec
    (placement (V := V)) retainedFigureNineClearancePlacement_period_primrec
    retainedFigureNineClearancePlacement_position_primrec
    (routes (V := V)) retainedFigureNineClearanceIncidenceRoutes_primrec

theorem input_primrec : Primrec (input (V := V)) :=
  Primrec.pair (PositionedPeriodicCNF.erase_primrec.comp retainedFigureNineClearancePositionedFormula_primrec)
    drawing_primrec

omit [Primcodable V] in
theorem input_correct (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) :
    Orbit.ThreeOccurrenceProblem (input f) ↔ f.Satisfiable := by
  have semantics := retainedFigureNineClearancePositionedFormula_satisfiable_iff f hl hw ho
  constructor
  · intro h
    exact semantics.1 h.2.2.2
  · intro h
    refine ⟨?_,
      ⟨retainedFigureNineClearancePositionedFormula_widthAtMostThree f hw,
        compatible f hl hw ho hn⟩,planar f hl hw ho hn,semantics.2 h⟩
    have occurrences := retainedFigureNineClearancePositionedFormula_occurrencesAtMostThree f hl hw ho hn
    exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _ occurrences
end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
