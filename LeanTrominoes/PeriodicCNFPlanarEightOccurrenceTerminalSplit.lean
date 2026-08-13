/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPorts

/-!
# Terminal-aligned fixed-eight occurrence splitting

The semantic angular split numbers occurrences in cyclic order, but its
absolute first slot need not be the physical northwest ray of Figure 7.
This module instead reads each copied occurrence's compass port directly
from the terminal vector of its routed planar-SAT incidence.

Satisfiability does not depend on port separation, so the terminal-aligned
formula is already proved equivalent to the planarized source.  The single
remaining degree-three obligation is exposed as a
`TerminalPortCertificate`: genuine terminal vectors must be valid compass
rays, and two occurrences of one atom must use different rays.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Physical compass ports read from the canonical direct terminal rays of
the deduplicated wrapped planar-SAT source. -/
def drawingTerminalOccurrencePorts
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    OccurrencePorts :=
  terminalOccurrencePorts
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)

/-- Fixed-eight occurrence splitting whose absolute ports agree with the
physical terminal rays. -/
def drawingTerminalEightOccurrenceSplitFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplit.formula
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    (drawingTerminalOccurrencePorts formula)

/-- The precise geometric obligation needed for the terminal-aligned split
to retain the three-occurrence promise. -/
def DrawingTerminalPortCertificate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  TerminalPortCertificate
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)

theorem drawingTerminalEightOccurrenceSplitFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingTerminalEightOccurrenceSplitFormula formula).Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  exact
    (terminalFormula_satisfiable_iff
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
      (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
        formula)).trans
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
        formula)

theorem drawingTerminalEightOccurrenceSplitFormula_isLocal
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (sourceLocal :
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
        formula).IsLocal) :
    (drawingTerminalEightOccurrenceSplitFormula formula).IsLocal := by
  exact terminalFormula_isLocal
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)
    sourceLocal

theorem drawingTerminalEightOccurrenceSplitFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (sourceWidth :
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
        formula).WidthAtMost 3) :
    (drawingTerminalEightOccurrenceSplitFormula
      formula).WidthAtMost 3 := by
  exact terminalFormula_widthAtMostThree
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)
    sourceWidth

theorem
    drawingTerminalEightOccurrenceSplitFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (certificate : DrawingTerminalPortCertificate formula) :
    (drawingTerminalEightOccurrenceSplitFormula
      formula).OccurrencesAtMost 3 := by
  exact terminalFormula_occurrencesAtMostThree
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)
    certificate

/-- Positioned terminal-aligned split, using the same certified Figure 7
macrocell coordinates as the semantic angular version. -/
def drawingTerminalEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.formula
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (drawingTerminalOccurrencePorts formula)

/-- The terminal-aligned split uses the same uniform refined placement. -/
def drawingTerminalEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.placement
    (wrappedDrawingPeriodicPlanarSATPlacement formula)

@[simp]
theorem drawingTerminalEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingTerminalEightOccurrenceSplitPositionedFormula formula).erase =
      drawingTerminalEightOccurrenceSplitFormula formula := by
  unfold drawingTerminalEightOccurrenceSplitPositionedFormula
    drawingTerminalEightOccurrenceSplitFormula
  rw [PeriodicEightOccurrenceSplitPositioned.erase_formula,
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]

theorem drawingTerminalEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 < (drawingTerminalEightOccurrenceSplitPlacement formula).period := by
  unfold drawingTerminalEightOccurrenceSplitPlacement
  apply PeriodicEightOccurrenceSplitPositioned.placement_period_pos
  exact drawingPeriodicPlanarSATPlacement_period_pos formula

end PeriodicOrthocrossing
end LeanTrominoes
