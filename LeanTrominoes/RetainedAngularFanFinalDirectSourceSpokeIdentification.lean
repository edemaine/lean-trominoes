/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoiceSpokePairs
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Identifying selected direct-source spokes with final suffixes

The finite direct-source certificate positions a factor-eight copy of the
Figure 7 spoke at the selected local endpoint.  The final coordinated route
retains the pre-existing scaled occurrence suffix.  This module proves that
these are literally the same polyline: both are translations of the same
scaled local spoke and their heads are the validated common splice point.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A direct-source atlas spoke starts at the corresponding refined
fan-boundary point around its local center. -/
@[simp]
theorem retainedDirectSourceFigure7SpokeAt_head?
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    (retainedDirectSourceFigure7SpokeAt kind index slot).head? =
      some
        (Cell.add
          (retainedDirectSourceFanCenterAt kind index)
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val))) := by
  simp only [retainedDirectSourceFigure7SpokeAt,
    PeriodicOrthocrossing.translatePolyline, List.head?_map,
    scalePolyline_head?, spokeRoute_head?, Option.map_some]
  apply congrArg some
  rcases retainedDirectSourceFanCenterAt kind index with ⟨x, y⟩
  rcases pointEq :
      spokeClausePosition (angularPortOfIndex slot.val) with ⟨px, py⟩
  simp [pointEq, angularFanBoundaryOffset,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- The selected spoke begins exactly where the selected coordinated prefix
ends. -/
@[simp]
theorem RetainedDirectSourceRouteChoice.figure7Spoke_head?
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (choice.figure7Spoke slot).head? =
      (choice.completeRoute slot).getLast? := by
  rw [choice.completeRoute_getLast?]
  simp only [RetainedDirectSourceRouteChoice.figure7Spoke,
    PeriodicOrthocrossing.translatePolyline, List.head?_map,
    retainedDirectSourceFigure7SpokeAt_head?, Option.map_some]

/-- A choice-positioned spoke is one translation of the factor-eight local
Figure 7 spoke. -/
theorem RetainedDirectSourceRouteChoice.figure7Spoke_eq_translate
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    choice.figure7Spoke slot =
      translatePolyline
        (Cell.add
          (Cell.sub
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
          (retainedDirectSourceFanPositioningOffset choice.origin))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (spokeRoute (angularPortOfIndex slot.val))) := by
  unfold RetainedDirectSourceRouteChoice.figure7Spoke
    retainedDirectSourceFigure7SpokeAt
  exact translatePolyline_add _ _ _

end PeriodicEightOccurrenceSplit

namespace OccurrenceSplitRing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Scaling a positioned occurrence suffix scales its translation and its
local Figure 7 spoke independently. -/
theorem scalePolyline_angularOccurrenceSuffix_eq_translate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex) =
      LeanTrominoes.PeriodicOrthocrossing.translatePolyline
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanOccurrenceOrigin
            sourcePlacement literal.atom
            (incidenceRelativeOffset clause literal)))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (spokeRoute
            (angularPortOfIndex
              (angularOccurrenceIndex order literal
                clauseIndex literalIndex)))) := by
  rw [angularOccurrenceSuffix,
    angularFanSpokeRouteAt_eq_map_add]
  unfold scalePolyline
    LeanTrominoes.PeriodicOrthocrossing.translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  exact PeriodicOrthocrossing.cell_scale_add _ _ _

end OccurrenceSplitRing

namespace PeriodicOrthocrossing

/-- Two translations of one nonempty polyline are equal when their heads
are equal. -/
theorem translatePolyline_eq_of_head?_eq
    (firstOffset secondOffset : Cell)
    (route : List Cell)
    (nonempty : route ≠ [])
    (headsEqual :
      (translatePolyline firstOffset route).head? =
        (translatePolyline secondOffset route).head?) :
    translatePolyline firstOffset route =
      translatePolyline secondOffset route := by
  cases route with
  | nil => contradiction
  | cons head tail =>
      rcases firstOffset with ⟨firstX, firstY⟩
      rcases secondOffset with ⟨secondX, secondY⟩
      rcases head with ⟨headX, headY⟩
      simp only [translatePolyline, List.map_cons,
        List.head?_cons, Option.some.injEq, Cell.add,
        Prod.mk.injEq] at headsEqual
      have offsetsEqual : (firstX, firstY) = (secondX, secondY) := by
        apply Prod.ext <;> simp_all
      rw [offsetsEqual]

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- A selected direct-source spoke is the scaled positioned occurrence
suffix whenever they use the same occurrence slot and validated splice
point. -/
theorem
    RetainedDirectSourceRouteChoice.figure7Spoke_eq_scaledAngularOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex)
    (boundary :
      (choice.completeRoute slot).getLast? =
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)).head?) :
    choice.figure7Spoke slot =
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex) := by
  have headsEqual :
      (choice.figure7Spoke slot).head? =
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)).head? :=
    (choice.figure7Spoke_head? slot).trans boundary
  rw [choice.figure7Spoke_eq_translate,
    OccurrenceSplitRing.scalePolyline_angularOccurrenceSuffix_eq_translate]
      at headsEqual ⊢
  rw [slotVal] at headsEqual ⊢
  apply translatePolyline_eq_of_head?_eq _ _ _ ?_ headsEqual
  cases angularPortOfIndex
      (angularOccurrenceIndex order literal
        clauseIndex literalIndex) <;>
    native_decide

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- A genuine final retained occurrence's bounded coordinated slot has the
exact angular-order index used by its existing Figure 7 suffix. -/
theorem retainedFinalCoordinatedOccurrenceSlot_val
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
    (retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex).val =
      angularOccurrenceIndex
        (angularOccurrenceOrder source.erase routes)
        literal clauseIndex literalIndex := by
  dsimp only
  have fits :
      FitsEightSlots
        (angularOccurrenceOrder
          ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).scale retainedAngularFanSourceClearanceFactor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              formula))) := by
    rw [PositionedPeriodicCNF.erase_scale,
      angularOccurrenceOrder_scaleIncidenceRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase
        retainedAngularFanSourceClearanceFactor_pos
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)]
    simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor)
      scaledClauseMember literalMember
  have copyMember :
      (literal.atom, clauseIndex, literalIndex) ∈
        occurrenceVariables
          ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).scale retainedAngularFanSourceClearanceFactor).erase
          literal.atom :=
    occurrenceVariables_mem _ taggedMember
  have indexLt :
      angularOccurrenceIndex
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          literal clauseIndex literalIndex < 8 := by
    simpa [angularOccurrenceIndex, indexedOccurrence,
      retainedAngularTerminalSlot_val] using
      (retainedAngularTerminalSlot
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula))
        fits literal.atom
        (literal.atom, clauseIndex, literalIndex)
        copyMember).isLt
  exact boundedRetainedTerminalSlot_val_of_lt indexLt

/-- For every successful final direct choice, its certified positioned
spoke is literally the scaled Figure 7 suffix retained by the final route. -/
theorem
    retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    let source :=
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor
    let placement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    choice.figure7Spoke slot =
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) := by
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale retainedAngularFanSourceClearanceFactor
  let placement :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have slotVal :
      slot.val =
        angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex := by
    simpa [source, routes, slot] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have boundary :
      (choice.completeRoute slot).getLast? =
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)).head? := by
    simpa [source, placement, routes, slot] using
      retainedFinalCoordinatedDirectOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
  exact
    choice.figure7Spoke_eq_scaledAngularOccurrenceSuffix
      placement (angularOccurrenceOrder source.erase routes)
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex slot slotVal boundary

end PeriodicOrthocrossing
end LeanTrominoes
