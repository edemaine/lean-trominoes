import LeanTrominoes.PeriodicCNFPlanarOneInThreeThreePositioned
import LeanTrominoes.PeriodicOneInThreeNoUnitsOccurrences

/-!
# Positioned elimination of exact-one unit clauses

The positioned Figure 9 reduction can emit unit clauses when a source clause
has fewer than three literals.  The logical unit-elimination reduction is
already verified, but its clause positions must also be retained before the
subsequent planar 3DM replacement.

This file places each replacement in a constant-size refinement of the source
clause cell.  Unit clauses use a two-clause diamond, empty clauses use the
three binary sides of a triangle, and clauses of arity at least two retain a
single central clause.  Erasing positions is proved definitionally equal to
the verified `PeriodicOneInThreeNoUnits.formula`.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Constant refinement leaving room for every unit-elimination gadget. -/
def gadgetScale : Int := 6

/-- Position of one generated clause inside a refined source-clause cell. -/
def generatedClausePosition {Variable : Type*}
    (source : PositionedPeriodicClause Variable)
    (generatedIndex : Nat) : Cell :=
  let localOffset : Cell :=
    match source.literals with
    | [] =>
        match generatedIndex with
        | 0 => (3, 1)
        | 1 => (5, 4)
        | _ => (1, 4)
    | [_] =>
        match generatedIndex with
        | 0 => (3, 2)
        | _ => (3, 4)
    | _ :: _ :: _ => (3, 3)
  Cell.add (Cell.scale gadgetScale source.position) localOffset

/-- Replace one positioned exact-one clause by positioned clauses of arity
two or three. -/
def clauseGadget {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    List
      (PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)) :=
  (PeriodicOneInThreeNoUnits.clauseClauses
      clauseIndex source.literals).zipIdx.map fun taggedClause =>
    ⟨generatedClausePosition source taggedClause.2,
      taggedClause.1⟩

/-- Eliminate units in every positioned prototype clause. -/
def formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable Variable) :=
  ⟨source.clauses.zipIdx.flatMap fun taggedClause =>
    clauseGadget taggedClause.2 taggedClause.1⟩

@[simp]
theorem clauseGadget_literals {Variable : Type*}
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    (clauseGadget clauseIndex source).map
        PositionedPeriodicClause.literals =
      PeriodicOneInThreeNoUnits.clauseClauses
        clauseIndex source.literals := by
  unfold clauseGadget
  rw [List.map_map]
  change
    (PeriodicOneInThreeNoUnits.clauseClauses
      clauseIndex source.literals).zipIdx.map Prod.fst =
        PeriodicOneInThreeNoUnits.clauseClauses
          clauseIndex source.literals
  exact List.zipIdx_map_fst 0
    (PeriodicOneInThreeNoUnits.clauseClauses
      clauseIndex source.literals)

/-- Forgetting positions recovers exactly the verified logical
unit-elimination reduction. -/
@[simp]
theorem erase_formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    (formula source).erase =
      PeriodicOneInThreeNoUnits.formula source.erase := by
  unfold formula PositionedPeriodicCNF.erase
    PeriodicOneInThreeNoUnits.formula
  simp only [List.map_flatMap]
  rw [List.zipIdx_map]
  simp [List.flatMap_map, clauseGadget_literals]

end PeriodicOneInThreeNoUnitsPositioned

namespace PeriodicOrthocrossing

/-- Positioned, unit-free exact-one endpoint of the complete planarized
periodic SAT reduction. -/
def drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (drawingPositionedPeriodicPlanarOneInThreeThreeFormula source)

@[simp]
theorem
    drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase =
        PeriodicOneInThreeNoUnits.formula
          (drawingPeriodicPlanarOneInThreeThreeFormula source) := by
  simp [drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula]

/-- End-to-end satisfiability of the positioned, unit-free exact-one
endpoint. -/
theorem
    drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase ↔
      source.Satisfiable := by
  rw [
    drawingPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
    PeriodicOneInThreeNoUnits.satisfiable_iff,
    drawingPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff
      source sourceWidth sourceOccurrences]

end PeriodicOrthocrossing
end LeanTrominoes
