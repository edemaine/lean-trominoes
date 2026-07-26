import LeanTrominoes.PeriodicCNFPlanarOneInThreeNoUnitsPositioned

/-!
# Variable placements for the positioned planar exact-one reduction

The positioned formula layers retain clause vertices, while the variable
positions used to create them were previously passed as transient function
arguments.  This file packages the companion data needed by the geometric
3DM assembly.

A placement records the integer-grid side length of one semantic lattice
period and one canonical position for each protovariable.  Consequently a
literal occurrence at offset `d` is drawn at the variable position translated
by `period * d`.  Clause-local auxiliaries are stored at an anchor offset in
the logical reductions, so their canonical protovariable positions subtract
that translation.  The lemmas below verify that adding the anchor back lands
at the intended local gadget vertex.
-/

namespace LeanTrominoes

/-- Canonical protovariable positions and the drawing-grid length of one
semantic lattice step. -/
structure PeriodicVariablePlacement (Variable : Type*) where
  period : Nat
  position : Variable → Cell

namespace PeriodicVariablePlacement

/-- Drawing-grid translation corresponding to a semantic lattice offset. -/
def translation {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (offset : Cell) : Cell :=
  Cell.scale placement.period offset

/-- Physical endpoint of one periodic literal occurrence in the prototype
clause at translate zero. -/
def literalPosition {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable) : Cell :=
  Cell.add (placement.position literal.atom)
    (placement.translation literal.offset)

end PeriodicVariablePlacement

namespace PositionedPeriodicCNF

/-- Position of a prototype clause by presentation index, with a harmless
total default for indices that do not occur. -/
def clausePosition {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex : Nat) : Cell :=
  (source.clauses[clauseIndex]?.map
    PositionedPeriodicClause.position).getD (0, 0)

end PositionedPeriodicCNF

namespace PeriodicThreeSATThreePositioned

/-- Occurrence splitting refines both the period and every original-variable
macrocell by the same factor. -/
def placement {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement (ThreeOccurrenceVariable Variable) where
  period := (refinementScale source).toNat * sourcePlacement.period
  position :=
    occurrenceVariablePosition source sourcePlacement.position

end PeriodicThreeSATThreePositioned

namespace PeriodicOneInThreePositioned

/-- Integer-grid vertex of every Figure 9 auxiliary inside its source-clause
box.  Padding vertices occupy the lower routing band next to their unit
clauses. -/
def auxiliaryLocalPosition : OneInThreeAux → Cell
  | .firstChoice => (4, 3)
  | .secondChoice => (8, 3)
  | .firstSlack => (2, 7)
  | .secondSlack => (10, 7)
  | .firstPadding => (3, 8)
  | .secondPadding => (6, 8)
  | .thirdPadding => (9, 8)

/-- Intended physical position of a Figure 9 auxiliary occurrence at the
anchor of its source clause. -/
def auxiliaryOccurrencePosition {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex : Nat) (kind : OneInThreeAux) : Cell :=
  Cell.add
    (Cell.scale PlanarOneInThree.gadgetScale
      (source.clausePosition clauseIndex))
    (auxiliaryLocalPosition kind)

/-- Variable placement induced by the positioned Figure 9 replacement. -/
def placement {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement (OneInThreeVariable Variable) where
  period :=
    PlanarOneInThree.gadgetScale.toNat * sourcePlacement.period
  position
    | .inl atom =>
        Cell.scale PlanarOneInThree.gadgetScale
          (sourcePlacement.position atom)
    | .inr ((clauseIndex, clause), kind) =>
        Cell.sub
          (auxiliaryOccurrencePosition source clauseIndex kind)
          (Cell.scale
            (PlanarOneInThree.gadgetScale *
              (sourcePlacement.period : Int))
            (PeriodicOneInThree.anchor clause))

/-- Figure 9 refinement preserves positivity of the physical period. -/
theorem placement_period_pos {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourcePeriodPositive : 0 < sourcePlacement.period) :
    0 < (placement source sourcePlacement).period := by
  simpa [placement, PlanarOneInThree.gadgetScale] using
    Nat.mul_pos (by decide : 0 < 12) sourcePeriodPositive

/-- Restoring the logical anchor translates every Figure 9 auxiliary to its
declared local gadget vertex. -/
@[simp]
theorem placement_auxiliary_at_anchor {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    Cell.add
        ((placement source sourcePlacement).position
          (.inr ((clauseIndex, clause), kind)))
        ((placement source sourcePlacement).translation
          (PeriodicOneInThree.anchor clause)) =
      auxiliaryOccurrencePosition source clauseIndex kind := by
  simp [placement, PeriodicVariablePlacement.translation,
    PlanarOneInThree.gadgetScale, Cell.add, Cell.sub]

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnitsPositioned

/-- Local auxiliary vertices for the empty-clause triangle and unit-clause
diamond.  Roles unused by a particular source clause remain harmless total
values. -/
def auxiliaryLocalPosition : OneInThreeNoUnitAux → Cell
  | .first => (2, 3)
  | .second => (4, 3)
  | .third => (3, 5)

/-- Intended physical position of a unit-elimination auxiliary occurrence at
the anchor of its source exact-one clause. -/
def auxiliaryOccurrencePosition {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex : Nat) (kind : OneInThreeNoUnitAux) : Cell :=
  Cell.add
    (Cell.scale gadgetScale (source.clausePosition clauseIndex))
    (auxiliaryLocalPosition kind)

/-- Variable placement induced by unit-clause elimination. -/
def placement {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable) where
  period := gadgetScale.toNat * sourcePlacement.period
  position
    | .inl atom =>
        Cell.scale gadgetScale (sourcePlacement.position atom)
    | .inr ((clauseIndex, clause), kind) =>
        Cell.sub
          (auxiliaryOccurrencePosition source clauseIndex kind)
          (Cell.scale (gadgetScale * (sourcePlacement.period : Int))
            (PeriodicOneInThree.anchor clause))

/-- Unit-clause elimination preserves positivity of the physical period. -/
theorem placement_period_pos {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourcePeriodPositive : 0 < sourcePlacement.period) :
    0 < (placement source sourcePlacement).period := by
  simpa [placement, gadgetScale] using
    Nat.mul_pos (by decide : 0 < 6) sourcePeriodPositive

/-- Restoring the logical anchor translates every unit-elimination auxiliary
to its declared local gadget vertex. -/
@[simp]
theorem placement_auxiliary_at_anchor {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    Cell.add
        ((placement source sourcePlacement).position
          (.inr ((clauseIndex, clause), kind)))
        ((placement source sourcePlacement).translation
          (PeriodicOneInThree.anchor clause)) =
      auxiliaryOccurrencePosition source clauseIndex kind := by
  simp [placement, PeriodicVariablePlacement.translation,
    gadgetScale, Cell.add, Cell.sub]

end PeriodicOneInThreeNoUnitsPositioned

namespace PeriodicOrthocrossing

/-- The routed planar SAT drawing is the `20 × 20` macro-refinement of the
generic incidence-graph drawing. -/
def drawingPeriodicPlanarSATPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarSATVariable Variable) where
  period :=
    planarMacroScale.toNat *
      drawingGridSize (PeriodicCNF.incidenceGraph formula)
  position := drawingPeriodicPlanarSATVariablePosition formula

/-- The routed planar SAT placement has a positive physical period. -/
theorem drawingPeriodicPlanarSATPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 < (drawingPeriodicPlanarSATPlacement formula).period := by
  simp only [drawingPeriodicPlanarSATPlacement,
    planarMacroScale]
  exact Nat.mul_pos (by decide)
    (drawingGridSize_pos (PeriodicCNF.incidenceGraph formula))

/-- Placement transported through the opaque routed-variable wrapper. -/
def wrappedDrawingPeriodicPlanarSATPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicPlanarSATVariable Variable) where
  period := (drawingPeriodicPlanarSATPlacement formula).period
  position := fun wrapped =>
    (drawingPeriodicPlanarSATPlacement formula).position wrapped.original

/-- Placement of all post-planarization occurrence copies. -/
def drawingPeriodicPlanarThreeSATThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  PeriodicThreeSATThreePositioned.placement
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)

/-- Placement of the raw Figure 9 exact-one variables. -/
def drawingPeriodicPlanarOneInThreeThreeRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.placement
    (drawingPositionedPeriodicPlanarThreeSATThreeFormula formula)
    (drawingPeriodicPlanarThreeSATThreePlacement formula)

/-- Placement transported through the opaque exact-one output wrapper. -/
def drawingPeriodicPlanarOneInThreeThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) where
  period :=
    (drawingPeriodicPlanarOneInThreeThreeRawPlacement formula).period
  position := fun wrapped =>
    (drawingPeriodicPlanarOneInThreeThreeRawPlacement formula).position
      wrapped.original

/-- End-to-end placement of the unit-free exact-one formula consumed by the
planar 3DM construction. -/
def drawingPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (drawingPositionedPeriodicPlanarOneInThreeThreeFormula formula)
    (drawingPeriodicPlanarOneInThreeThreePlacement formula)

end PeriodicOrthocrossing

end LeanTrominoes
