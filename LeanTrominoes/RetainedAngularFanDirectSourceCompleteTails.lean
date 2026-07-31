import LeanTrominoes.RetainedAngularFanDirectSourcePrefixSelections

/-!
# Concrete complete tails for direct source clauses

The direct-source atlas was initially indexed only by clause kind and
literal position.  Those same finite indices also determine the underlying
two-point local incidence route, hence its factor-four fan center and scaled
terminal length.

This file packages those concrete parameters.  The terminal direction is
stored through the atlas choice, while an exhaustive check proves that the
result is exactly the factor-four scaling of the terminal datum classified
from the local incidence route.  A second finite check proves that all
literals of one direct clause produce the same outer demand gate, for every
choice of their occurrence slots.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicThreeSATThree

/-- The fixed local direct incidence represented by one atlas entry. -/
def retainedDirectSourceLocalRouteAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    List Cell :=
  match kind with
  | .crossover clauseIndex =>
      crossoverStraightIncidenceDrawing.routes
        clauseIndex.val index.val
  | .duplicator arm clauseIndex =>
      (duplicatorArmStraightIncidenceDrawing arm).routes
        clauseIndex.val index.val
  | .routedClause =>
      (routedClausePortStraightIncidenceDrawing
        retainedDirectRoutedClauseRepresentativeLiterals).routes
          0 index.val

/-- Every represented direct incidence is exactly one clause-to-variable
segment. -/
theorem retainedDirectSourceLocalRouteAt_length :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      (retainedDirectSourceLocalRouteAt kind index).length = 2 := by
  native_decide

/-- The retained terminal datum classified from one unscaled local direct
incidence. -/
def retainedDirectSourceLocalTerminalAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedTerminalData :=
  classifiedRetainedTerminalData
    (routeTerminalVector
      (retainedDirectSourceLocalRouteAt kind index))

/-- The factor-four center used by the hardness construction, after the
combined fan refinement. -/
def retainedDirectSourceFanCenterAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  Cell.scale retainedTerminalFanTotalRefinement
    ((scalePolyline 4
      (retainedDirectSourceLocalRouteAt kind index)).getLastD
        (0, 0))

/-- The concrete factor-four terminal attached to an atlas entry.  Keeping
the checked atlas direction definitionally visible lets its coordinated
escape certificate be used without dependent casts. -/
def retainedDirectSourceFanTerminalAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedTerminalData :=
  ((retainedDirectSourcePrefixChoiceAt kind index).direction,
    4 * (retainedDirectSourceLocalTerminalAt kind index).2)

/-- Atlas direction matching upgrades the concrete terminal to exactly the
factor-four scaling of the classified local terminal datum. -/
theorem retainedDirectSourceFanTerminalAt_eq_scale :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      retainedDirectSourceFanTerminalAt kind index =
        scaleRetainedTerminalData 4
          (retainedDirectSourceLocalTerminalAt kind index) := by
  native_decide

/-- Every direct local incidence has a positive classified terminal
length. -/
theorem retainedDirectSourceLocalTerminalAt_length_positive :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      0 < (retainedDirectSourceLocalTerminalAt kind index).2 := by
  native_decide

/-- Consequently every concrete factor-four fan terminal is positive. -/
theorem retainedDirectSourceFanTerminalAt_length_positive
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    0 < (retainedDirectSourceFanTerminalAt kind index).2 := by
  rw [retainedDirectSourceFanTerminalAt_eq_scale]
  exact scaleRetainedTerminalData_length_pos
    (by omega)
    (retainedDirectSourceLocalTerminalAt_length_positive kind index)

/-- Every concrete direct terminal has room for the fixed 64-block source
escape. -/
theorem retainedDirectSourceFanTerminalAt_escape_fits
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    retainedTerminalFanOuterSourceEscapeLength ≤
      retainedTerminalFanOuterRadialLength
        (retainedDirectSourceFanTerminalAt kind index) := by
  rw [retainedDirectSourceFanTerminalAt_eq_scale]
  exact retainedTerminalFanOuterSourceEscape_fits_scale_four
    (retainedDirectSourceLocalTerminalAt kind index)
    (retainedDirectSourceLocalTerminalAt_length_positive kind index)

/-- The atlas entry instantiated at its concrete factor-four center,
terminal length, and occurrence slot. -/
def retainedDirectSourceFanEscapeAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalFanOuterSourceEscapeCertificate
      (retainedDirectSourceFanCenterAt kind index)
      (retainedDirectSourceFanTerminalAt kind index)
      slot :=
  retainedDirectSourceEscapeCertificateAt
    kind index
    (retainedDirectSourceFanCenterAt kind index)
    (retainedDirectSourceFanTerminalAt kind index).2
    slot

/-- The fixed post-escape complete tail selected by one direct incidence and
occurrence slot. -/
def retainedDirectSourceFanCompleteTailAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanOuterCoordinatedEscapedCompleteTail
    (retainedDirectSourceFanCenterAt kind index)
    (retainedDirectSourceFanTerminalAt kind index)
    slot

/-- The complete coordinated direct-source outer route. -/
def retainedDirectSourceFanCompleteRouteAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
    (retainedDirectSourceFanCenterAt kind index)
    (retainedDirectSourceFanTerminalAt kind index)
    slot
    (retainedDirectSourceFanEscapeAt kind index slot)

/-- Every pair of literals in one direct clause has the same concrete outer
demand gate, independently of their variable-side occurrence slots. -/
theorem retainedDirectSourceFanDemand_gates_eq :
    ∀ (kind : RetainedDirectClauseKind)
      (firstIndex secondIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      (retainedAngularFanOuterDemand
        (retainedDirectSourceFanCenterAt kind firstIndex)
        (retainedDirectSourceFanTerminalAt kind firstIndex)
        firstSlot).gate =
      (retainedAngularFanOuterDemand
        (retainedDirectSourceFanCenterAt kind secondIndex)
        (retainedDirectSourceFanTerminalAt kind secondIndex)
        secondSlot).gate := by
  native_decide

/-- For every finite direct-source atlas entry, the common outer gate is
exactly the fully refined clause endpoint of its factor-four local route. -/
theorem retainedDirectSourceFanDemand_gate_eq_scaledLocalHead :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      (retainedAngularFanOuterDemand
        (retainedDirectSourceFanCenterAt kind index)
        (retainedDirectSourceFanTerminalAt kind index)
        slot).gate =
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale 4
          ((retainedDirectSourceLocalRouteAt kind index).headD
            (0, 0))) := by
  native_decide

/-- A genuine metadata-selected literal pair needs only the three concrete
strict tail interactions; all centers, terminal data, escapes, and the
common gate are recovered from its atlas indices. -/
theorem
    RetainedDirectSourcePrefixPairSelection.concreteCompleteRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : PeriodicOrthocrossing.DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstEscapeAvoidSecondTail :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanEscapeAt
          selection.kind selection.firstIndex firstSlot).route
        (retainedDirectSourceFanCompleteTailAt
          selection.kind selection.secondIndex secondSlot))
    (firstTailAvoidSecondEscape :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteTailAt
          selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourceFanEscapeAt
          selection.kind selection.secondIndex secondSlot).route)
    (tailsAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteTailAt
          selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourceFanCompleteTailAt
          selection.kind selection.secondIndex secondSlot)) :
    RoutesAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          selection.kind selection.secondIndex secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedDirectSourceFanCompleteRouteAt
          selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          selection.kind selection.secondIndex secondSlot) := by
  unfold retainedDirectSourceFanCompleteRouteAt retainedDirectSourceFanEscapeAt
  unfold retainedDirectSourceFanCompleteTailAt at firstEscapeAvoidSecondTail firstTailAvoidSecondEscape tailsAvoid
  unfold retainedDirectSourceFanTerminalAt at firstEscapeAvoidSecondTail firstTailAvoidSecondEscape tailsAvoid ⊢
  exact
    selection.coordinatedCompleteRoutes_separated
      (retainedDirectSourceFanCenterAt
        selection.kind selection.firstIndex)
      (retainedDirectSourceFanCenterAt
        selection.kind selection.secondIndex)
      (4 *
        (retainedDirectSourceLocalTerminalAt
          selection.kind selection.firstIndex).2)
      (4 *
        (retainedDirectSourceLocalTerminalAt
          selection.kind selection.secondIndex).2)
      firstSlot secondSlot
      (by
        simpa [retainedDirectSourceFanTerminalAt] using
          retainedDirectSourceFanDemand_gates_eq
            selection.kind selection.firstIndex selection.secondIndex
            firstSlot secondSlot)
      firstEscapeAvoidSecondTail
      firstTailAvoidSecondEscape tailsAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
