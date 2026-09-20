/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawingComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPlacementComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PeriodicPlanarSATUnboundedCoRE

/-! # The computed planar exact-one endpoint -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
open PeriodicOrthocrossing
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
variable {V : Type} [Primcodable V] [DecidableEq V]
abbrev Target (V : Type) := RetainedOrderedFixedEightOneInThreeVariable V
local instance : DecidableEq (Target V) := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

def positioned (f : PeriodicCNF V) : PositionedPeriodicCNF (Target V) :=
  retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed f

def drawing (f : PeriodicCNF V) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing (positioned f)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement f)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed f)

def input (f : PeriodicCNF V) : Input (Target V) := ((positioned f).erase,drawing f)

theorem positioned_primrec : Primrec (positioned (V := V)) :=
  retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec

theorem drawing_primrec : Primrec (drawing (V := V)) :=
  PositionedPeriodicCNF.incidenceDrawing_primrec positioned positioned_primrec
    _ retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_position_primrec
    _ retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_primrec

theorem input_primrec : Primrec (input (V := V)) :=
  Primrec.pair (PositionedPeriodicCNF.erase_primrec.comp positioned_primrec) drawing_primrec

variable (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
  (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ [])

omit [Primcodable V]
include hl hw ho hn

theorem correct : PeriodicOneInThree.Satisfiable (input f).1 ↔ f.Satisfiable := by
  change PeriodicOneInThree.Satisfiable (positioned f).erase ↔ _
  rw [positioned,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn]
  exact (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_satisfiable_iff
    f hl hw ho hn).trans
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff f hl hw ho)

theorem width : (input f).1.WidthAtMost 3 := by
  change (positioned f).erase.WidthAtMost 3
  rw [positioned,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn]
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_widthAtMostThree f hl hw ho hn

theorem planar : (drawing f).IsContinuouslyPlanar := by
  unfold drawing positioned
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq f hl hw ho hn]
  exact (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady f hl hw ho hn).1

theorem compatible : (drawing f).IsCompatible (input f).1.incidenceGraph := by
  change (drawing f).IsCompatible (positioned f).erase.incidenceGraph
  unfold drawing positioned
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq f hl hw ho hn]
  exact retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isCompatible f hl hw ho hn

theorem occurrences : (input f).1.OccurrencesAtMost 3 := by
  change (positioned f).erase.OccurrencesAtMost 3
  rw [positioned,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn]
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    finalGaugedRibbonFansVariableBEq _ finalGaugedRibbonFansVariableLawfulBEq _ 3 _
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
      f hl hw ho hn).occurrencesAtMostThree

theorem problem_correct : Unbounded.ExactOneProblem (input f) ↔ f.Satisfiable :=
  ⟨fun h => (correct f hl hw ho hn).1 h.2.2,
    fun h => ⟨⟨width f hl hw ho hn,(compatible f hl hw ho hn).2⟩,
      planar f hl hw ho hn,(correct f hl hw ho hn).2 h⟩⟩

theorem threeOccurrenceProblem_correct :
    Unbounded.ExactOneThreeOccurrenceProblem (input f) ↔ f.Satisfiable :=
  ⟨fun h => (problem_correct f hl hw ho hn).1 h.2,
    fun h => ⟨occurrences f hl hw ho hn,(problem_correct f hl hw ho hn).2 h⟩⟩

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
