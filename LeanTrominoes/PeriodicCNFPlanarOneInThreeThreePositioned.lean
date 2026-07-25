import LeanTrominoes.PeriodicCNFPlanarOneInThreeThree
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned
import LeanTrominoes.PlanarOneInThree

/-!
# Positioned periodic Figure 9 replacement

This file places Figure 9 directly on a positioned periodic CNF, retaining
literal offsets.  Erasing the generated clause positions gives exactly
`PeriodicOneInThree.formula`, so all logical correctness and incidence
accounting established for that reduction transfer unchanged.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Replace one positioned periodic disjunction by its local Figure 9
exact-one clauses. -/
def clauseGadget {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    List
      (PositionedPeriodicClause
        (OneInThreeVariable Variable)) :=
  (PeriodicOneInThree.clauseClauses
      clauseIndex source.literals).zipIdx.map fun taggedClause =>
    ⟨PlanarOneInThree.generatedClausePosition
        source.position taggedClause.2,
      taggedClause.1⟩

/-- Apply Figure 9 independently at every positioned protoclauses. -/
def formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF (OneInThreeVariable Variable) :=
  ⟨source.clauses.zipIdx.flatMap fun taggedClause =>
    clauseGadget taggedClause.2 taggedClause.1⟩

@[simp]
theorem clauseGadget_literals {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    (clauseGadget clauseIndex source).map
        PositionedPeriodicClause.literals =
      PeriodicOneInThree.clauseClauses
        clauseIndex source.literals := by
  simpa [clauseGadget, List.map_map,
    Function.comp_def] using
      List.zipIdx_map_fst 0
        (PeriodicOneInThree.clauseClauses
          clauseIndex source.literals)

/-- Erasing positions gives exactly the verified periodic Figure 9
reduction. -/
@[simp]
theorem erase_formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    (formula source).erase =
      PeriodicOneInThree.formula source.erase := by
  unfold formula PositionedPeriodicCNF.erase
    PeriodicOneInThree.formula
  simp only [List.map_flatMap]
  rw [List.zipIdx_map]
  simp [List.flatMap_map, clauseGadget_literals]

end PeriodicOneInThreePositioned

namespace PeriodicOrthocrossing

/-- Positioned direct Figure 9 image of the occurrence-split routed planar
formula, before the final opaque output wrapper. -/
def drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.formula
    (drawingPositionedPeriodicPlanarThreeSATThreeFormula formula)

@[simp]
theorem
    drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula
      formula).erase =
        drawingPeriodicPlanarOneInThreeThreeRawFormula formula := by
  simp [drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula,
    drawingPeriodicPlanarOneInThreeThreeRawFormula]

/-- Positioned exact-one endpoint with the same opaque variable wrapper as
the logical occurrence-three formula. -/
def drawingPositionedPeriodicPlanarOneInThreeThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula
    formula).rename WrappedPeriodicVariable.mk

@[simp]
theorem drawingPositionedPeriodicPlanarOneInThreeThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarOneInThreeThreeFormula
      formula).erase =
        drawingPeriodicPlanarOneInThreeThreeFormula formula := by
  rw [drawingPositionedPeriodicPlanarOneInThreeThreeFormula,
    PositionedPeriodicCNF.erase_rename,
    drawingPositionedPeriodicPlanarOneInThreeThreeRawFormula_erase]
  rfl

/-- The positioned endpoint has width at most three after positions are
erased. -/
theorem
    drawingPositionedPeriodicPlanarOneInThreeThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarOneInThreeThreeFormula
      formula).erase.WidthAtMost 3 := by
  rw [drawingPositionedPeriodicPlanarOneInThreeThreeFormula_erase]
  exact drawingPeriodicPlanarOneInThreeThreeFormula_widthAtMostThree
    formula

/-- The positioned endpoint retains the exact occurrence-three certificate
after positions are erased. -/
theorem
    drawingPositionedPeriodicPlanarOneInThreeThreeFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingPositionedPeriodicPlanarOneInThreeThreeFormula
      formula).erase.OccurrencesAtMost 3 := by
  rw [drawingPositionedPeriodicPlanarOneInThreeThreeFormula_erase]
  exact
    drawingPeriodicPlanarOneInThreeThreeFormula_occurrencesAtMostThree
      formula sourceWidth

/-- End-to-end exact-one semantics of the positioned periodic endpoint. -/
theorem
    drawingPositionedPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPositionedPeriodicPlanarOneInThreeThreeFormula
          formula).erase ↔
      formula.Satisfiable := by
  rw [
    drawingPositionedPeriodicPlanarOneInThreeThreeFormula_erase,
    drawingPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff
      formula sourceWidth sourceOccurrences]

end PeriodicOrthocrossing
end LeanTrominoes
