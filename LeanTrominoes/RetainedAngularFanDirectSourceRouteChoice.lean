/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourcePositionedRoutes

/-!
# Checked route choices for direct source metadata

The coordinated direct-source atlas is indexed by finite local clause and
literal positions.  Actual planar-SAT clauses instead carry an unbounded
presentation index in `DrawingPlanarSATClauseSource`.  This file provides the
total checked bridge between those two interfaces.

A successful choice records both the finite atlas entry and the physical
origin of its local component.  It therefore determines a positioned
coordinated route for any occurrence slot.  Invalid indices, and the two
non-direct source families, return `none`; later global integration can retain
the ordinary angular-fan route in exactly those cases.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicThreeSATThree
open PeriodicOrthocrossing

/-- A checked finite-atlas entry for one direct source incidence, together
with the origin that positions its local component in the planar-SAT
drawing. -/
structure RetainedDirectSourceRouteChoice where
  origin : Cell
  kind : RetainedDirectClauseKind
  index : Fin (retainedDirectSourcePrefixChoices kind).length

/-- Check a raw planar-SAT clause source and literal presentation index
against the finite coordinated-route atlas. -/
def retainedDirectSourceRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match source with
  | .crossover crossing localClauseIndex =>
      if localClauseIndexLt : localClauseIndex < 26 then
        let kind : RetainedDirectClauseKind :=
          .crossover ⟨localClauseIndex, localClauseIndexLt⟩
        if literalIndexLt :
            literalIndex <
              (retainedDirectSourcePrefixChoices kind).length then
          some {
            origin := crossingMacroOrigin crossing
            kind := kind
            index := ⟨literalIndex, literalIndexLt⟩
          }
        else
          none
      else
        none
  | .carrier _ _ =>
      none
  | .bend _ _ =>
      none
  | .routedClause site =>
      if literalIndexLt :
          literalIndex <
            (routedClausePortLiterals formula site).length then
        let portIndex :
            Fin (routedClausePortLiterals formula site).length :=
          ⟨literalIndex, literalIndexLt⟩
        let arm :=
          ((routedClausePortLiterals formula site).get portIndex).1
        some {
          origin := routedClauseOrigin formula site
          kind := .routedClause
          index := retainedDirectRoutedClauseArmIndex arm
        }
      else
        none
  | .routedVariable site _ arm _ localClauseIndex =>
      if localClauseIndexLt : localClauseIndex < 2 then
        let kind : RetainedDirectClauseKind :=
          .duplicator arm ⟨localClauseIndex, localClauseIndexLt⟩
        if literalIndexLt :
            literalIndex <
              (retainedDirectSourcePrefixChoices kind).length then
          some {
            origin := routedVariableOrigin formula site
            kind := kind
            index := ⟨literalIndex, literalIndexLt⟩
          }
        else
          none
      else
        none

/-- A successful lookup carries the exact retained terminal direction of the
actual positioned local incidence route. -/
def RetainedDirectSourceRouteChoice.Matches
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice) : Prop :=
  (retainedDirectSourcePrefixChoiceAt
      choice.kind choice.index).direction =
    classifiedRetainedTerminalDirection
      (routeTerminalVector
        ((source.incidenceDrawing formula).routes
          source.localClauseIndex literalIndex))

/-- A successful choice identifies not just the terminal direction but the
entire positioned local incidence route represented by its atlas entry. -/
def RetainedDirectSourceRouteChoice.Represents
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice) : Prop :=
  translatePolyline choice.origin
      (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
    (source.incidenceDrawing formula).routes
      source.localClauseIndex literalIndex

/-- Selecting a routed-clause atlas entry by physical arm recovers the
actual local route, independently of the clause's literal order and signs. -/
theorem retainedDirectRoutedClauseArmRoute_eq
    (literals : List (DuplicatorArm × Bool))
    (literalIndex : Fin literals.length) :
    (routedClausePortStraightIncidenceDrawing
        retainedDirectRoutedClauseRepresentativeLiterals).routes
        0 (retainedDirectRoutedClauseArmIndex
          (literals.get literalIndex).1).val =
      (routedClausePortStraightIncidenceDrawing literals).routes
        0 literalIndex.val := by
  generalize armEq :
    (literals.get literalIndex).1 = arm
  cases arm <;>
    simp_all [routedClausePortStraightIncidenceDrawing,
      routedClausePortFormula, straightIncidenceDrawing,
      straightIncidenceRoutes, straightIncidenceRoute,
      retainedDirectRoutedClauseRepresentativeLiterals,
      retainedDirectRoutedClauseArmIndex,
      DuplicatorArm.portPosition]

/-- Every successful total lookup represents the complete actual local
incidence route selected by the source and presentation index. -/
theorem retainedDirectSourceRouteChoice?_represents_of_eq_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice? formula source literalIndex =
        some choice) :
    choice.Represents formula source literalIndex := by
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next localClauseIndexLt =>
        split at lookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at lookup
          subst choice
          simp [RetainedDirectSourceRouteChoice.Represents,
            retainedDirectSourceLocalRouteAt,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex,
            drawingPlanarSATCrossoverIncidenceDrawing,
            EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate,
            translatePolyline]
        next => contradiction
      next => contradiction
  | carrier link localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | bend routeBend localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | routedClause site =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next literalIndexLt =>
        simp only [Option.some.injEq] at lookup
        subst choice
        simp only [RetainedDirectSourceRouteChoice.Represents,
          retainedDirectSourceLocalRouteAt,
          retainedDirectRoutedClauseArmIndex,
          DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          drawingPlanarSATRoutedClauseIncidenceDrawing,
          EmbeddedCNFIncidenceDrawing.translate,
          translatePolyline]
        apply congrArg (List.map (routedClauseOrigin formula site).add)
        exact retainedDirectRoutedClauseArmRoute_eq
          (routedClausePortLiterals formula site)
          ⟨literalIndex, literalIndexLt⟩
      next => contradiction
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next localClauseIndexLt =>
        split at lookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at lookup
          subst choice
          simp [RetainedDirectSourceRouteChoice.Represents,
            retainedDirectSourceLocalRouteAt,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex,
            drawingPlanarSATRoutedVariableIncidenceDrawing,
            EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate,
            translatePolyline]
        next => contradiction
      next => contradiction

/-- Every genuine crossover literal makes the checked lookup succeed and
selects its exact positioned terminal direction. -/
theorem exists_retainedDirectSourceRouteChoice_crossover
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause, .crossover crossing localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ choice,
      retainedDirectSourceRouteChoice?
          formula (.crossover crossing localClauseIndex) literalIndex =
        some choice ∧
      choice.Matches formula
        (.crossover crossing localClauseIndex) literalIndex := by
  have localClauseIndexLt : localClauseIndex < 26 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2
    simpa [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      crossoverFormula] using indexLt
  let clauseIndex : Fin 26 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).length :=
    List.snd_lt_of_mem_zipIdx valid.2
  have localClauseEq :
      (drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have literalIndexLt :
      literalIndex <
        (retainedDirectSourcePrefixChoices
          (.crossover clauseIndex)).length := by
    rw [retainedDirectCrossoverPrefixChoices_length]
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseLiteralsLength :
        clause.literals.length =
          (retainedDirectCrossoverClauseAt
            clauseIndex).literals.length := by
      rw [← localClauseEq]
      simp [drawingPlanarSATCrossoverFormulaAt,
        scopedCrossoverInstance, instantiateFormula,
        retainedDirectCrossoverClauseAt,
        EmbeddedClause.place, EmbeddedClause.rename,
        EmbeddedClause.map, clauseIndex]
    simpa [clauseLiteralsLength] using literalLt
  let atlasIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length :=
    ⟨literalIndex, literalIndexLt⟩
  let choice : RetainedDirectSourceRouteChoice := {
    origin := crossingMacroOrigin crossing
    kind := .crossover clauseIndex
    index := atlasIndex
  }
  refine ⟨choice, ?_, ?_⟩
  · simp [retainedDirectSourceRouteChoice?,
      localClauseIndexLt, literalIndexLt,
      clauseIndex, atlasIndex, choice]
  · simpa [RetainedDirectSourceRouteChoice.Matches,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex,
      clauseIndex, atlasIndex, choice] using
        retainedDirectCrossoverPrefixChoice_positionedDirection
          formula crossing clauseIndex atlasIndex

/-- Every genuine routed-variable literal makes the checked lookup succeed
and selects its exact positioned terminal direction. -/
theorem exists_retainedDirectSourceRouteChoice_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause,
        .routedVariable site armIndex arm link localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ choice,
      retainedDirectSourceRouteChoice?
          formula
          (.routedVariable site armIndex arm link localClauseIndex)
          literalIndex =
        some choice ∧
      choice.Matches formula
        (.routedVariable site armIndex arm link localClauseIndex)
        literalIndex := by
  have localClauseIndexLt : localClauseIndex < 2 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2.2.2
    simpa [drawingPlanarSATRoutedVariableFormulaAt,
      equalityInstance] using indexLt
  let clauseIndex : Fin 2 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2.2.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATRoutedVariableFormulaAt link).length :=
    List.snd_lt_of_mem_zipIdx valid.2.2.2
  have localClauseEq :
      (drawingPlanarSATRoutedVariableFormulaAt link).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have literalIndexLt :
      literalIndex <
        (retainedDirectSourcePrefixChoices
          (.duplicator arm clauseIndex)).length := by
    rw [retainedDirectDuplicatorPrefixChoices_length]
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseLiteralsLength :
        clause.literals.length =
          (retainedDirectDuplicatorClauseAt
            arm clauseIndex).literals.length := by
      rw [← localClauseEq]
      simp [drawingPlanarSATRoutedVariableFormulaAt,
        retainedDirectDuplicatorClauseAt,
        duplicatorArmFormula, equalityInstance,
        EmbeddedClause.rename, EmbeddedClause.map,
        clauseIndex]
      interval_cases localClauseIndex <;> rfl
    simpa [clauseLiteralsLength] using literalLt
  let atlasIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length :=
    ⟨literalIndex, literalIndexLt⟩
  let choice : RetainedDirectSourceRouteChoice := {
    origin := routedVariableOrigin formula site
    kind := .duplicator arm clauseIndex
    index := atlasIndex
  }
  refine ⟨choice, ?_, ?_⟩
  · simp [retainedDirectSourceRouteChoice?,
      localClauseIndexLt, literalIndexLt,
      clauseIndex, atlasIndex, choice]
  · simpa [RetainedDirectSourceRouteChoice.Matches,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex,
      clauseIndex, atlasIndex, choice] using
        retainedDirectDuplicatorPrefixChoice_positionedDirection
          formula site arm link clauseIndex atlasIndex

/-- Every genuine routed-clause literal makes the checked lookup succeed and
selects the atlas entry belonging to its physical arm. -/
theorem exists_retainedDirectSourceRouteChoice_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : ClauseRouteSite)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause, .routedClause site⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ choice,
      retainedDirectSourceRouteChoice?
          formula (.routedClause site) literalIndex =
        some choice ∧
      choice.Matches formula (.routedClause site) literalIndex := by
  have literalIndexLt :
      literalIndex <
        (routedClausePortLiterals formula site).length := by
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseEq :
        clause =
          (routedClauseAt formula site).rename
            planarSATExternalVariableMap := by
      simpa using valid.2
    rw [clauseEq] at literalLt
    simpa [routedClausePortLiterals, routedClauseAt,
      EmbeddedClause.rename, EmbeddedClause.map] using literalLt
  let portIndex :
      Fin (routedClausePortLiterals formula site).length :=
    ⟨literalIndex, literalIndexLt⟩
  let arm :=
    ((routedClausePortLiterals formula site).get portIndex).1
  let choice : RetainedDirectSourceRouteChoice := {
    origin := routedClauseOrigin formula site
    kind := .routedClause
    index := retainedDirectRoutedClauseArmIndex arm
  }
  refine ⟨choice, ?_, ?_⟩
  · simp [retainedDirectSourceRouteChoice?,
      literalIndexLt, portIndex, arm, choice]
  · simpa [RetainedDirectSourceRouteChoice.Matches,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex,
      portIndex, arm, choice] using
        retainedDirectRoutedClauseArmChoice_positionedDirection
          formula site portIndex

/-- The direct-source trichotomy for genuine retained metadata always
produces a successful checked route choice with the exact local direction. -/
theorem
    DrawingPlanarSATClauseMetadata.exists_retainedDirectSourceRouteChoice
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex)) :
    ∃ choice,
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex =
        some choice ∧
      choice.Matches formula metadata.source literalIndex := by
  rcases metadata with ⟨clause, source⟩
  rcases directCases with
      ⟨crossing, localClauseIndex, rfl⟩ |
      ⟨⟨site, rfl⟩ |
        ⟨site, armIndex, arm, link,
          localClauseIndex, rfl⟩⟩
  · exact exists_retainedDirectSourceRouteChoice_crossover
      formula clause crossing localClauseIndex valid literalMember
  · exact exists_retainedDirectSourceRouteChoice_routedClause
      formula clause site valid literalMember
  · exact exists_retainedDirectSourceRouteChoice_routedVariable
      formula clause site armIndex arm link localClauseIndex
      valid literalMember

/-- The positioned coordinated route selected by a successful direct-source
lookup. -/
def RetainedDirectSourceRouteChoice.completeRoute
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    List Cell :=
  retainedDirectSourcePositionedFanCompleteRouteAt
    choice.origin choice.kind choice.index slot

/-- A selected coordinated route begins at the translated concrete source
gate. -/
@[simp]
theorem RetainedDirectSourceRouteChoice.completeRoute_head?
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (choice.completeRoute slot).head? =
      some
        (Cell.add
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedAngularFanOuterDemand
            (retainedDirectSourceFanCenterAt choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt choice.kind choice.index)
            slot).gate) := by
  simp only [RetainedDirectSourceRouteChoice.completeRoute,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    PeriodicOrthocrossing.translatePolyline, List.head?_map,
    retainedDirectSourceFanCompleteRouteAt,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_head?,
    Option.map_some]

/-- The positioned route head is the fully refined factor-four image of the
represented local clause endpoint. -/
theorem RetainedDirectSourceRouteChoice.completeRoute_head_eq_scaledLocalHead
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (choice.completeRoute slot).head? =
      some
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale 4
            (Cell.add choice.origin
              ((retainedDirectSourceLocalRouteAt
                choice.kind choice.index).headD (0, 0))))) := by
  rw [choice.completeRoute_head?,
    retainedDirectSourceFanDemand_gate_eq_scaledLocalHead]
  rcases choice.origin with ⟨originX, originY⟩
  rcases (retainedDirectSourceLocalRouteAt
    choice.kind choice.index).headD (0, 0) with ⟨headX, headY⟩
  simp [retainedDirectSourceFanPositioningOffset,
    Cell.add, Cell.scale]
  constructor <;> ring

/-- A selected coordinated route ends at the unchanged translated Figure 7
fan boundary for its occurrence slot. -/
@[simp]
theorem RetainedDirectSourceRouteChoice.completeRoute_getLast?
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (choice.completeRoute slot).getLast? =
      some
        (Cell.add
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (Cell.add
            (retainedDirectSourceFanCenterAt choice.kind choice.index)
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val)))) := by
  simp only [RetainedDirectSourceRouteChoice.completeRoute,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    PeriodicOrthocrossing.translatePolyline, List.getLast?_map,
    retainedDirectSourceFanCompleteRouteAt,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_getLast?
      _ _ _
      (retainedDirectSourceFanEscapeAt choice.kind choice.index slot)
      (retainedDirectSourceFanTerminalAt_length_positive
        choice.kind choice.index)
      (retainedDirectSourceFanTerminalAt_escape_fits
        choice.kind choice.index),
    Option.map_some]

/-- Specializing the generic last-point scaling law to the source-clearance
factor gives an integer-typed rewrite for the concrete local route. -/
private theorem scalePolyline_four_getLastD
    (route : List Cell) :
    (scalePolyline (4 : Int) route).getLastD (0, 0) =
      Cell.scale 4 (route.getLastD (0, 0)) := by
  simpa using scalePolyline_getLastD 4 route

/-- The positioned route ends at the fully refined factor-four local
variable endpoint plus the unchanged Figure 7 boundary offset. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_getLast_eq_scaledLocalLast
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (choice.completeRoute slot).getLast? =
      some
        (Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale 4
              (Cell.add choice.origin
                ((retainedDirectSourceLocalRouteAt
                  choice.kind choice.index).getLastD (0, 0)))))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val))) := by
  rw [choice.completeRoute_getLast?]
  unfold retainedDirectSourceFanPositioningOffset
    retainedDirectSourceFanCenterAt
  rw [scalePolyline_four_getLastD]
  rcases choice.origin with ⟨originX, originY⟩
  rcases (retainedDirectSourceLocalRouteAt
    choice.kind choice.index).getLastD (0, 0) with ⟨lastX, lastY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

/-- Every positioned coordinated direct-source route is orthogonal. -/
theorem RetainedDirectSourceRouteChoice.completeRoute_orthogonal
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline (choice.completeRoute slot) := by
  apply OrthogonalPolyline.translate
  unfold retainedDirectSourceFanCompleteRouteAt
  exact
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_orthogonal
      (retainedDirectSourceFanCenterAt choice.kind choice.index)
      (retainedDirectSourceFanTerminalAt choice.kind choice.index)
      slot
      (retainedDirectSourceFanEscapeAt choice.kind choice.index slot)
      (retainedDirectSourceFanTerminalAt_length_positive
        choice.kind choice.index)
      (retainedDirectSourceFanTerminalAt_escape_fits
        choice.kind choice.index)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
