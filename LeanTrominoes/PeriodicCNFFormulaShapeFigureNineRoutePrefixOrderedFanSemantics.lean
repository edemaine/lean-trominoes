/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixSemantics

/-! # Active connectors after the canonical clockwise clause ordering -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix

open FormulaShapeDirectionOrdering
open PlanarOneInThreeNoUnitsFigureNine

/-- The paired profile sort preserves the first direction at each active
slot of the canonically reordered geometric route family. -/
theorem exitFanData_direction_ordered_ofClause
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3)
    (slot : Fin 3) (active : slot.val < clause.literals.length) :
    (exitFanData (orderedDirectedProfile
      (DirectedClauseProfile.ofClause routes clauseIndex clause))).direction slot =
      AxisDirection.polylineFirstDirection
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes clauseIndex slot.val) := by
  let annotate : PeriodicLiteral Variable × Nat →
      UnaryProgramClauseProfile.LiteralProfile × AxisDirection :=
    fun tagged => (literalProfile tagged.1,
      AxisDirection.polylineFirstDirection (routes clauseIndex tagged.2))
  have sortedMap := List.map_insertionSort
    (r := PositionedPeriodicCNF.clauseLiteralDirectionLE routes clauseIndex)
    (s := directionLE) annotate clause.literals.zipIdx (by
      intro first _ second _
      rfl)
  have sortedLt : slot.val <
      (PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).length := by
    simpa only [PositionedPeriodicCNF.clauseLiteralOrder,
      List.length_insertionSort, List.length_zipIdx] using active
  change (((orderedDirectedProfile
    (DirectedClauseProfile.ofClause routes clauseIndex clause)).taggedLiterals[
      slot.val]?).map Prod.snd).getD .invalid = _
  rw [taggedLiterals_orderedDirectedProfile,
    DirectedClauseProfile.ofClause_taggedLiterals routes clauseIndex clause nonempty width]
  change ((((clause.literals.zipIdx.map annotate).insertionSort directionLE)[
    slot.val]?).map Prod.snd).getD .invalid = _
  rw [← sortedMap]
  change ((((PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).map
    annotate)[slot.val]?).map Prod.snd).getD .invalid = _
  rw [List.getElem?_map, List.getElem?_eq_getElem sortedLt]
  exact (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
    placement routes (List.mk_mem_zipIdx_iff_getElem?.mpr clauseLookup)
    (List.getElem?_eq_getElem sortedLt)).symm

/-- Only the direction at the selected active slot affects its connector;
the finite profile and geometric fan therefore give the same point list. -/
theorem exitFanData_extendedRoute_ordered_ofClause
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3)
    (slot : Fin 3) (active : slot.val < clause.literals.length) :
    (exitFanData (orderedDirectedProfile
      (DirectedClauseProfile.ofClause routes clauseIndex clause))).extendedRoute slot =
      (PositionedPeriodicCNF.clauseExitFanData
        (PositionedPeriodicCNF.orderClauseByRouteDirection routes clauseIndex clause)
        clauseIndex
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes)).extendedRoute slot := by
  have directionEq := exitFanData_direction_ordered_ofClause
    source placement routes clauseIndex clause clauseLookup nonempty width slot active
  unfold ComposedClauseExitFanData.extendedRoute ComposedClauseExitFanData.route
  rw [directionEq]
  rfl

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix
