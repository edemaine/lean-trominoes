/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarSATGeometry
import LeanTrominoes.PositionedPeriodicCNFDeduplication
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-!
# Deduplicated periodic routed SAT presentation

The finite routed SAT block contains neighboring translated copies so that
all geometry meeting a fundamental square is explicit.  After
periodicization, some of those copies are the same protoclause orbit.

This file selects one positioned representative per erased literal list and
then applies the existing opaque variable wrapper.  The resulting source is
semantically equivalent to the full routed periodic SAT formula, but is the
appropriate finite vertex set for a nonoverlapping incidence drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- The routed positioned periodic formula with one representative per
distinct periodic literal list. -/
def deduplicatedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarSATVariable Variable) :=
  ((drawingPositionedPeriodicPlanarSATFormula formula).anchorNormalize
    (drawingPeriodicPlanarSATPlacement formula)).deduplicateByLiterals

/-- Semantic counterpart of the deduplicated positioned source, behind the
opaque routed-variable wrapper. -/
def deduplicatedWrappedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable) :=
  (wrappedDrawingPeriodicPlanarSATFormula formula).anchorNormalize.deduplicate

/-- The wrapped positioned source after putting every clause orbit in its
canonical anchor gauge. -/
def anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  ((wrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).anchorNormalize
      (wrappedDrawingPeriodicPlanarSATPlacement
        formula))

/-- Positioned and wrapped source used by geometry-ordered occurrence
splitting. -/
def deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).deduplicateByLiterals

/-- Positioned erasure agrees exactly with the semantic deduplicated wrapped
formula. -/
@[simp]
theorem
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase =
      deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula := by
  rw [
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_deduplicateByLiterals,
    PositionedPeriodicCNF.erase_anchorNormalize,
    wrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  rfl

/-- Clause-orbit deduplication and opaque wrapping together preserve the
routed periodic SAT semantics. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  exact
    (PeriodicCNF.deduplicate_satisfiable_iff
      (wrappedDrawingPeriodicPlanarSATFormula
        formula).anchorNormalize).trans
      ((PeriodicCNF.anchorNormalize_satisfiable_iff
        (wrappedDrawingPeriodicPlanarSATFormula formula)).trans
        (wrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
          formula))

/-- The deduplicated wrapped source retains every routed clause-width
bound. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_widthAtMost
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (width : Nat)
    (bounded :
      (drawingPeriodicPlanarSATFormula formula).WidthAtMost width) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).WidthAtMost width := by
  apply
    ((PeriodicCNF.deduplicate_widthAtMost_iff
      (wrappedDrawingPeriodicPlanarSATFormula
        formula).anchorNormalize width).mpr)
  apply PeriodicCNF.anchorNormalize_widthAtMost
  exact wrapPeriodicPlanarSATFormula_widthAtMost
    (drawingPeriodicPlanarSATFormula formula) width bounded

end PeriodicOrthocrossing
end LeanTrominoes
