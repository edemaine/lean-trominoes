import LeanTrominoes.PeriodicCNFPlanarSATGeometry
import LeanTrominoes.PositionedPeriodicCNFDeduplication

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

/-- The routed positioned periodic formula with one representative per
distinct periodic literal list. -/
def deduplicatedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarSATVariable Variable) :=
  (drawingPositionedPeriodicPlanarSATFormula formula).deduplicateByLiterals

/-- Semantic counterpart of the deduplicated positioned source, behind the
opaque routed-variable wrapper. -/
def deduplicatedWrappedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable) :=
  wrapPeriodicPlanarSATFormula
    (drawingPeriodicPlanarSATFormula formula).deduplicate

/-- Positioned and wrapped source used by geometry-ordered occurrence
splitting. -/
def deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (deduplicatedDrawingPositionedPeriodicPlanarSATFormula formula).rename
    WrappedPeriodicVariable.mk

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
  rw [deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_rename,
    deduplicatedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_deduplicateByLiterals,
    drawingPositionedPeriodicPlanarSATFormula_erase]
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
    (wrapPeriodicPlanarSATFormula_satisfiable_iff
      (drawingPeriodicPlanarSATFormula formula).deduplicate).trans
        (PeriodicCNF.deduplicate_satisfiable_iff
          (drawingPeriodicPlanarSATFormula formula))

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
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact
    ((PeriodicCNF.deduplicate_widthAtMost_iff
      (drawingPeriodicPlanarSATFormula formula) width).mpr bounded)

end PeriodicOrthocrossing
end LeanTrominoes
