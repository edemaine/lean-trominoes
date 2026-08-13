/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicGridDrawingRibbonSeparation
import LeanTrominoes.PeriodicOrthocrossingSegments
import LeanTrominoes.PeriodicThreeSATThreeGeometricOrder
import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.RetainedAngularTerminalGateDistinctness
import LeanTrominoes.RetainedTerminalSplicePoint

/-!
# Source geometry sufficient for retained terminal-vector distinctness

Two occurrences of one periodic variable may leave on the same retained
ray, but the complete backwards terminal vectors still have to differ.
This file derives that fact from the source drawing's endpoint-only contact
certificate and the local syntactic condition that a clause does not repeat
an incidence key `(atom, offset)`.

The key argument aligns the two translated variable endpoints.  Equal
terminal vectors then align the two penultimate route points.  Endpoint-only
contact forces both penultimate points to be route heads, so both routes are
single segments.  Their aligned clause endpoints are consequently equal.
Uniqueness of representatives in the fundamental square identifies the
clause.  Equality of the aligned direct routes also identifies the literal
offset, so incidence-key distinctness inside that clause identifies the
literal.  This weaker condition deliberately permits a periodic clause to
mention the same atom at different offsets.
-/

namespace LeanTrominoes

namespace PositionedPeriodicClause

/-- No physical periodic incidence `(atom, offset)` is repeated within a
positioned clause.  Literal polarity is intentionally irrelevant. -/
irreducible_def IncidenceKeysNodup
    {Variable : Type*}
    (clause : PositionedPeriodicClause Variable) : Prop :=
  (clause.literals.map fun literal =>
    (literal.atom, literal.offset)).Nodup

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

/-- Every positioned clause lists each physical periodic incidence at most
once. -/
irreducible_def AllIncidenceKeysNodup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) : Prop :=
  ∀ clause ∈ source.clauses, clause.IncidenceKeysNodup

private theorem incidenceKeysNodup_of_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (literals : List (PeriodicLiteral Variable))
    (atomsNodup :
      (literals.map PeriodicLiteral.atom).Nodup) :
    (literals.map fun literal =>
      (literal.atom, literal.offset)).Nodup := by
  induction literals with
  | nil =>
      simp
  | cons literal literals induction =>
      simp only [List.map_cons, List.nodup_cons] at atomsNodup ⊢
      constructor
      · intro keyMember
        apply atomsNodup.1
        rcases List.mem_map.mp keyMember with
          ⟨tailLiteral, tailMember, keyEqual⟩
        exact List.mem_map.mpr
          ⟨tailLiteral, tailMember,
            congrArg Prod.fst keyEqual⟩
      · exact induction atomsNodup.2

/-- Atom distinctness is a stronger, convenient sufficient condition for
incidence-key distinctness. -/
theorem allIncidenceKeysNodup_of_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (atomsNodup : source.AllAtomsNodup) :
    source.AllIncidenceKeysNodup := by
  rw [AllIncidenceKeysNodup]
  intro clause clauseMember
  have distinct := atomsNodup clause clauseMember
  unfold PositionedPeriodicClause.AtomsNodup at distinct
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
  exact incidenceKeysNodup_of_atomsNodup clause.literals distinct

end PositionedPeriodicCNF

namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- A tagged metadata incidence occurs at the same numeric index in the
flat route list of the positioned incidence drawing. -/
private theorem route_zipIdx_mem_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (routes tagged.1.clauseIndex tagged.1.literalIndex,
      tagged.2) ∈
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).edgeRoutes.zipIdx := by
  change
    (routes tagged.1.clauseIndex tagged.1.literalIndex,
      tagged.2) ∈
      (PositionedPeriodicCNF.incidenceEdgeRoutes
        source routes).zipIdx
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
    List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨tagged, taggedMember, by cases tagged; rfl⟩

/-- The point at list index `length - 2` is the total last-entrance lookup
on every genuine polyline. -/
private theorem get_penultimate_eq_polylineLastEntrance
    (route : List Cell)
    (routeLength : 2 ≤ route.length) :
    route.get ⟨route.length - 2, by omega⟩ =
      polylineLastEntrance route := by
  generalize reversedEq : route.reverse = reversed
  cases reversed with
  | nil =>
      have routeEq : route = [] := by
        simpa using congrArg List.reverse reversedEq
      subst route
      simp at routeLength
  | cons target rest =>
      cases rest with
      | nil =>
          have routeEq : route = [target] := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp at routeLength
      | cons entrance rest =>
          have routeEq :
              route =
                (target :: entrance :: rest).reverse := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp [polylineLastEntrance, polylineFirstExit]

/-- Compatible nonloop incidence routes have a genuine penultimate point. -/
private theorem route_length_ge_two_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (compatible :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).IsCompatible
          source.erase.incidenceGraph)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    2 ≤
      (routes tagged.1.clauseIndex
        tagged.1.literalIndex).length := by
  apply
    PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
      source.erase.incidenceGraph
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes)
      compatible
      (PeriodicCNF.incidenceGraph_edgesAreLoopless source.erase)
  exact List.fst_mem_of_mem_zipIdx
    (route_zipIdx_mem_of_tagged
      source placement routes taggedMember)

/-- Strengthened occurrence lookup retaining the atom field that is
definitionally present in the selected metadata incidence. -/
private theorem exists_taggedIncidence_of_mem_occurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    ∃ tagged : CNFIncidence Variable × Nat,
      tagged ∈
          (PeriodicCNF.incidencesWithMetadata source).zipIdx ∧
        tagged.1.clauseIndex = copy.2.1 ∧
        tagged.1.literalIndex = copy.2.2 ∧
        tagged.1.literal.atom = atom := by
  simp only [occurrenceVariables, List.mem_filterMap] at copyMember
  rcases copyMember with
    ⟨taggedLiteral, taggedLiteralMember, selected⟩
  by_cases sameAtom : taggedLiteral.1.atom = atom
  · simp only [sameAtom, ↓reduceIte, Option.some.injEq]
      at selected
    subst copy
    simp only [taggedLiterals, List.mem_flatMap,
      List.mem_map] at taggedLiteralMember
    rcases taggedLiteralMember with
      ⟨taggedClause, taggedClauseMember,
        sourceTaggedLiteral, sourceTaggedLiteralMember,
        taggedLiteralEq⟩
    subst taggedLiteral
    let incidence : CNFIncidence Variable :=
      ⟨taggedClause.2, taggedClause.1,
        sourceTaggedLiteral.2, sourceTaggedLiteral.1⟩
    have incidenceMember :
        incidence ∈
          PeriodicCNF.incidencesWithMetadata source := by
      simp only [PeriodicCNF.incidencesWithMetadata,
        List.mem_flatMap, List.mem_map]
      exact
        ⟨taggedClause, taggedClauseMember,
          sourceTaggedLiteral, sourceTaggedLiteralMember, rfl⟩
    rcases List.mem_iff_getElem.mp incidenceMember with
      ⟨index, indexLt, incidenceAt⟩
    refine ⟨(incidence, index), ?_, rfl, rfl, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨indexLt, incidenceAt⟩
    · exact sameAtom
  · simp [sameAtom] at selected

/-- Equal backwards vectors from translated copies of one target align
after undoing the two endpoint translations. -/
private theorem align_of_terminal_vectors_equal
    (period : Int)
    (first second target firstOffset secondOffset : Cell)
    (equal :
      Cell.sub first
          (Cell.add target (Cell.scale period firstOffset)) =
        Cell.sub second
          (Cell.add target (Cell.scale period secondOffset))) :
    Cell.add first
        (Cell.scale period (Cell.neg firstOffset)) =
      Cell.add second
        (Cell.scale period (Cell.neg secondOffset)) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases target with ⟨targetX, targetY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  simp only [Cell.add, Cell.sub, Cell.neg, Cell.scale,
    Prod.mk.injEq] at equal ⊢
  constructor <;> ring_nf at equal ⊢ <;> omega

/-- Endpoint-only contacts and per-clause incidence-key distinctness make
the full terminal vectors injective among occurrences of each variable. -/
theorem retainedOccurrenceTerminalVectorsInjective_of_endpointContacts
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (compatible :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).IsCompatible
          source.erase.incidenceGraph)
    (endpointContacts :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).RoutePointsMeetOnlyAtEndpoints)
    (incidenceKeysNodup : source.AllIncidenceKeysNodup) :
    RetainedOccurrenceTerminalVectorsInjective
      source.erase routes := by
  intro first firstAllMember second secondAllMember
    atomsEqual vectorsEqual
  let atom := first.1
  have firstMember :
      first ∈ occurrenceVariables source.erase atom :=
    (mem_occurrenceVariables_iff
      source.erase atom first).mpr ⟨firstAllMember, rfl⟩
  have secondMember :
      second ∈ occurrenceVariables source.erase atom :=
    (mem_occurrenceVariables_iff
      source.erase atom second).mpr
        ⟨secondAllMember, atomsEqual.symm⟩
  by_contra copiesDifferent
  rcases
      exists_taggedIncidence_of_mem_occurrenceVariables
        source.erase atom first firstMember with
    ⟨firstTagged, firstTaggedMember,
      firstClauseIndex, firstLiteralIndex, firstTaggedAtom⟩
  rcases
      exists_taggedIncidence_of_mem_occurrenceVariables
        source.erase atom second secondMember with
    ⟨secondTagged, secondTaggedMember,
      secondClauseIndex, secondLiteralIndex, secondTaggedAtom⟩
  let drawing :=
    PositionedPeriodicCNF.incidenceDrawing
      source placement routes
  let firstRoute :=
    routes firstTagged.1.clauseIndex
      firstTagged.1.literalIndex
  let secondRoute :=
    routes secondTagged.1.clauseIndex
      secondTagged.1.literalIndex
  have firstRouteLength : 2 ≤ firstRoute.length :=
    route_length_ge_two_of_tagged
      source placement routes compatible firstTaggedMember
  have secondRouteLength : 2 ≤ secondRoute.length :=
    route_length_ge_two_of_tagged
      source placement routes compatible secondTaggedMember
  let firstPointIndex : Fin firstRoute.length :=
    ⟨firstRoute.length - 2, by omega⟩
  let secondPointIndex : Fin secondRoute.length :=
    ⟨secondRoute.length - 2, by omega⟩
  let firstIndexed : IndexedRoutePoint :=
    { routeIndex := firstTagged.2
      pointIndex := firstPointIndex
      routeLength := firstRoute.length
      point := firstRoute.get firstPointIndex }
  let secondIndexed : IndexedRoutePoint :=
    { routeIndex := secondTagged.2
      pointIndex := secondPointIndex
      routeLength := secondRoute.length
      point := secondRoute.get secondPointIndex }
  have firstIndexedMember :
      firstIndexed ∈ drawing.indexedRoutePoints := by
    exact PeriodicGridDrawing.indexedRoutePoint_mem_of_route_mem
      (route_zipIdx_mem_of_tagged
        source placement routes firstTaggedMember)
      firstPointIndex
  have secondIndexedMember :
      secondIndexed ∈ drawing.indexedRoutePoints := by
    exact PeriodicGridDrawing.indexedRoutePoint_mem_of_route_mem
      (route_zipIdx_mem_of_tagged
        source placement routes secondTaggedMember)
      secondPointIndex
  have routeIndicesDifferent :
      firstTagged.2 ≠ secondTagged.2 := by
    intro routeIndicesEqual
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstTaggedMember secondTaggedMember routeIndicesEqual
    have clauseIndicesEqual :
        first.2.1 = second.2.1 := by
      rw [← firstClauseIndex, ← secondClauseIndex, taggedEqual]
    have literalIndicesEqual :
        first.2.2 = second.2.2 := by
      rw [← firstLiteralIndex, ← secondLiteralIndex, taggedEqual]
    apply copiesDifferent
    apply Prod.ext
    · exact atomsEqual
    · exact Prod.ext clauseIndicesEqual literalIndicesEqual
  have pointKeysDifferent :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed (Cell.neg firstTagged.1.edge.offset) ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed (Cell.neg secondTagged.1.edge.offset) := by
    intro keysEqual
    exact routeIndicesDifferent
      (congrArg (fun key => key.1) keysEqual)
  have firstEndpoints :=
    compatible.2.2.2.2.2
      (firstTagged.1.edge, firstTagged.2)
      (PeriodicCNF.tagged_incidence_edge_mem
        source.erase firstTaggedMember)
  have secondEndpoints :=
    compatible.2.2.2.2.2
      (secondTagged.1.edge, secondTagged.2)
      (PeriodicCNF.tagged_incidence_edge_mem
        source.erase secondTaggedMember)
  rw [PositionedPeriodicCNF.incidenceDrawing_edgeRoute_of_tagged
      source placement routes firstTaggedMember] at firstEndpoints
  rw [PositionedPeriodicCNF.incidenceDrawing_edgeRoute_of_tagged
      source placement routes secondTaggedMember] at secondEndpoints
  have firstLast :
      firstRoute.getLastD (0, 0) =
        Cell.add
          (drawing.vertexPosition source.erase.incidenceGraph
            firstTagged.1.edge.target)
          (drawing.periodTranslation
            firstTagged.1.edge.offset) := by
    simpa [firstRoute] using
      congrArg (fun value => value.getD (0, 0))
        firstEndpoints.2
  have secondLast :
      secondRoute.getLastD (0, 0) =
        Cell.add
          (drawing.vertexPosition source.erase.incidenceGraph
            secondTagged.1.edge.target)
          (drawing.periodTranslation
            secondTagged.1.edge.offset) := by
    simpa [secondRoute] using
      congrArg (fun value => value.getD (0, 0))
        secondEndpoints.2
  have targetVerticesEqual :
      firstTagged.1.edge.target =
        secondTagged.1.edge.target := by
    simp only [CNFIncidence.edge_target]
    exact congrArg CNFVertex.variable
      (firstTaggedAtom.trans secondTaggedAtom.symm)
  have alignedPointsEqual :
      Cell.add firstIndexed.point
          (drawing.periodTranslation
            (Cell.neg firstTagged.1.edge.offset)) =
        Cell.add secondIndexed.point
          (drawing.periodTranslation
            (Cell.neg secondTagged.1.edge.offset)) := by
    have terminalVectorsEqual :
        routeTerminalVector firstRoute =
          routeTerminalVector secondRoute := by
      unfold occurrenceTerminalVector at vectorsEqual
      rw [← firstClauseIndex, ← firstLiteralIndex,
        ← secondClauseIndex, ← secondLiteralIndex]
        at vectorsEqual
      simpa [firstRoute, secondRoute] using vectorsEqual
    rw [routeTerminalVector_eq_sub_lastEntrance
        firstRoute firstRouteLength,
      routeTerminalVector_eq_sub_lastEntrance
        secondRoute secondRouteLength,
      ← get_penultimate_eq_polylineLastEntrance
        firstRoute firstRouteLength,
      ← get_penultimate_eq_polylineLastEntrance
        secondRoute secondRouteLength,
      firstLast, secondLast, targetVerticesEqual]
      at terminalVectorsEqual
    change
      Cell.add (firstRoute.get firstPointIndex)
          (drawing.periodTranslation
            (Cell.neg firstTagged.1.edge.offset)) =
        Cell.add (secondRoute.get secondPointIndex)
          (drawing.periodTranslation
            (Cell.neg secondTagged.1.edge.offset))
    simpa [PeriodicGridDrawing.periodTranslation] using
      align_of_terminal_vectors_equal
        drawing.gridSize
        (firstRoute.get firstPointIndex)
        (secondRoute.get secondPointIndex)
        (drawing.vertexPosition source.erase.incidenceGraph
          secondTagged.1.edge.target)
        firstTagged.1.edge.offset
        secondTagged.1.edge.offset
        terminalVectorsEqual
  have penultimateEndpoints :=
    endpointContacts
      firstIndexed firstIndexedMember
      secondIndexed secondIndexedMember
      (Cell.neg firstTagged.1.edge.offset)
      (Cell.neg secondTagged.1.edge.offset)
      pointKeysDifferent alignedPointsEqual
  have firstRouteLengthEq : firstRoute.length = 2 := by
    rcases penultimateEndpoints.1 with head | last
    · change firstRoute.length - 2 = 0 at head
      omega
    · change firstRoute.length - 2 + 1 =
          firstRoute.length at last
      omega
  have secondRouteLengthEq : secondRoute.length = 2 := by
    rcases penultimateEndpoints.2 with head | last
    · change secondRoute.length - 2 = 0 at head
      omega
    · change secondRoute.length - 2 + 1 =
          secondRoute.length at last
      omega
  have alignedSourcesEqual :
      Cell.add
          (drawing.vertexPosition source.erase.incidenceGraph
            firstTagged.1.edge.source)
          (drawing.periodTranslation
            (Cell.neg firstTagged.1.edge.offset)) =
        Cell.add
          (drawing.vertexPosition source.erase.incidenceGraph
            secondTagged.1.edge.source)
          (drawing.periodTranslation
            (Cell.neg secondTagged.1.edge.offset)) := by
    have firstHead :
        firstRoute.get firstPointIndex =
          drawing.vertexPosition source.erase.incidenceGraph
            firstTagged.1.edge.source := by
      have firstPointZero : firstPointIndex.val = 0 := by
        simp [firstPointIndex, firstRouteLengthEq]
      have firstNonempty : firstRoute ≠ [] := by
        exact List.ne_nil_of_length_pos (by omega)
      rw [show firstPointIndex =
          ⟨0, by omega⟩ by apply Fin.ext; exact firstPointZero]
      change firstRoute[0] =
        drawing.vertexPosition source.erase.incidenceGraph
          firstTagged.1.edge.source
      rw [← List.head_eq_getElem_zero firstNonempty]
      exact Option.some.inj
        ((List.head?_eq_some_head firstNonempty).symm.trans
          firstEndpoints.1)
    have secondHead :
        secondRoute.get secondPointIndex =
          drawing.vertexPosition source.erase.incidenceGraph
            secondTagged.1.edge.source := by
      have secondPointZero : secondPointIndex.val = 0 := by
        simp [secondPointIndex, secondRouteLengthEq]
      have secondNonempty : secondRoute ≠ [] := by
        exact List.ne_nil_of_length_pos (by omega)
      rw [show secondPointIndex =
          ⟨0, by omega⟩ by apply Fin.ext; exact secondPointZero]
      change secondRoute[0] =
        drawing.vertexPosition source.erase.incidenceGraph
          secondTagged.1.edge.source
      rw [← List.head_eq_getElem_zero secondNonempty]
      exact Option.some.inj
        ((List.head?_eq_some_head secondNonempty).symm.trans
          secondEndpoints.1)
    change
      Cell.add (firstRoute.get firstPointIndex)
          (drawing.periodTranslation
            (Cell.neg firstTagged.1.edge.offset)) =
        Cell.add (secondRoute.get secondPointIndex)
          (drawing.periodTranslation
            (Cell.neg secondTagged.1.edge.offset))
      at alignedPointsEqual
    rw [firstHead, secondHead] at alignedPointsEqual
    exact alignedPointsEqual
  have sourcePrototypePositionsEqual :
      drawing.vertexPosition source.erase.incidenceGraph
          firstTagged.1.edge.source =
        drawing.vertexPosition source.erase.incidenceGraph
          secondTagged.1.edge.source := by
    have firstSourceMember :=
      compatible.1.2 firstTagged.1.edge
        (List.fst_mem_of_mem_zipIdx
          (PeriodicCNF.tagged_incidence_edge_mem
            source.erase firstTaggedMember)) |>.1
    have secondSourceMember :=
      compatible.1.2 secondTagged.1.edge
        (List.fst_mem_of_mem_zipIdx
          (PeriodicCNF.tagged_incidence_edge_mem
            source.erase secondTaggedMember)) |>.1
    have firstBounds :=
      compatible.2.2.2.2.1
        (drawing.vertexPosition source.erase.incidenceGraph
          firstTagged.1.edge.source)
        (compatible.vertexPosition_mem firstSourceMember)
    have secondBounds :=
      compatible.2.2.2.2.1
        (drawing.vertexPosition source.erase.incidenceGraph
          secondTagged.1.edge.source)
        (compatible.vertexPosition_mem secondSourceMember)
    rcases firstTagged.1.edge.offset with
      ⟨firstOffsetX, firstOffsetY⟩
    rcases secondTagged.1.edge.offset with
      ⟨secondOffsetX, secondOffsetY⟩
    simp only [PeriodicGridDrawing.PositionInFundamentalSquare]
      at firstBounds secondBounds
    have horizontalEqual :=
      congrArg Prod.fst alignedSourcesEqual
    have verticalEqual :=
      congrArg Prod.snd alignedSourcesEqual
    simp only [Cell.add, Cell.neg, Cell.sub,
      PeriodicGridDrawing.periodTranslation, Cell.scale]
      at horizontalEqual verticalEqual
    have periodPositive : (0 : Int) < drawing.gridSize := by
      exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
    have horizontal :=
      periodic_coordinate_unique periodPositive
        ⟨firstBounds.1.le, firstBounds.2.1⟩
        ⟨secondBounds.1.le, secondBounds.2.1⟩
        horizontalEqual
    have vertical :=
      periodic_coordinate_unique periodPositive
        ⟨firstBounds.2.2.1.le, firstBounds.2.2.2⟩
        ⟨secondBounds.2.2.1.le, secondBounds.2.2.2⟩
        verticalEqual
    exact Prod.ext horizontal.1 vertical.1
  have sourceVerticesEqual :
      firstTagged.1.edge.source =
        secondTagged.1.edge.source := by
    have firstEdgeMember :=
      List.fst_mem_of_mem_zipIdx
        (PeriodicCNF.tagged_incidence_edge_mem
          source.erase firstTaggedMember)
    have secondEdgeMember :=
      List.fst_mem_of_mem_zipIdx
        (PeriodicCNF.tagged_incidence_edge_mem
          source.erase secondTaggedMember)
    exact compatible.vertexPosition_injective_on
      (compatible.1.2 firstTagged.1.edge firstEdgeMember).1
      (compatible.1.2 secondTagged.1.edge secondEdgeMember).1
      sourcePrototypePositionsEqual
  have clauseIndicesEqual :
      first.2.1 = second.2.1 := by
    simpa [CNFIncidence.edge] using
      firstClauseIndex.symm.trans
        ((congrArg (fun vertex =>
            match vertex with
            | .variable _ => 0
            | .clause index => index)
          sourceVerticesEqual).trans secondClauseIndex)
  have edgeOffsetsEqual :
      firstTagged.1.edge.offset =
        secondTagged.1.edge.offset := by
    have horizontalEqual :=
      congrArg Prod.fst alignedSourcesEqual
    have verticalEqual :=
      congrArg Prod.snd alignedSourcesEqual
    rw [sourcePrototypePositionsEqual] at horizontalEqual verticalEqual
    rcases firstOffsetEq : firstTagged.1.edge.offset with
      ⟨firstOffsetX, firstOffsetY⟩
    rcases secondOffsetEq : secondTagged.1.edge.offset with
      ⟨secondOffsetX, secondOffsetY⟩
    simp only [Cell.add, Cell.neg, Cell.sub,
      PeriodicGridDrawing.periodTranslation, Cell.scale,
      firstOffsetEq, secondOffsetEq]
      at horizontalEqual verticalEqual
    have periodPositive : (0 : Int) < drawing.gridSize := by
      exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
    apply Prod.ext
    · nlinarith
    · nlinarith
  rcases
      PositionedPeriodicCNF.incidenceMetadata_of_tagged
        source firstTaggedMember with
    ⟨firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember, firstIncidenceEq⟩
  rcases
      PositionedPeriodicCNF.incidenceMetadata_of_tagged
        source secondTaggedMember with
    ⟨secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember, secondIncidenceEq⟩
  have taggedClausesEqual :
      (firstClause, firstTagged.1.clauseIndex) =
        (secondClause, secondTagged.1.clauseIndex) := by
    apply tagged_eq_of_mem_zipIdx_of_snd_eq
      firstClauseMember secondClauseMember
    simpa [firstClauseIndex, secondClauseIndex] using
      clauseIndicesEqual
  have clausesEqual : firstClause = secondClause :=
    congrArg Prod.fst taggedClausesEqual
  subst secondClause
  have firstAtom :
      firstLiteral.atom = atom := by
    have literalAtomEqual :
        firstTagged.1.literal.atom = firstLiteral.atom :=
      congrArg (fun incidence : CNFIncidence Variable =>
        incidence.literal.atom) firstIncidenceEq
    exact literalAtomEqual.symm.trans firstTaggedAtom
  have secondAtom :
      secondLiteral.atom = atom := by
    have literalAtomEqual :
        secondTagged.1.literal.atom = secondLiteral.atom :=
      congrArg (fun incidence : CNFIncidence Variable =>
        incidence.literal.atom) secondIncidenceEq
    exact literalAtomEqual.symm.trans secondTaggedAtom
  have literalOffsetsEqual :
      firstLiteral.offset = secondLiteral.offset := by
    have taggedClausesEqual :
        firstTagged.1.clause = secondTagged.1.clause := by
      have firstClauseEq :
          firstTagged.1.clause = firstClause.literals :=
        congrArg (fun incidence : CNFIncidence Variable =>
          incidence.clause) firstIncidenceEq
      have secondClauseEq :
          secondTagged.1.clause = firstClause.literals := by
        simpa using
          congrArg (fun incidence : CNFIncidence Variable =>
            incidence.clause) secondIncidenceEq
      exact firstClauseEq.trans secondClauseEq.symm
    have taggedOffsetsEqual :
        firstTagged.1.literal.offset =
          secondTagged.1.literal.offset := by
      have normalizedOffsetsEqual := edgeOffsetsEqual
      simp only [CNFIncidence.edge_offset,
        taggedClausesEqual] at normalizedOffsetsEqual
      rcases firstLiteralOffsetEq :
          firstTagged.1.literal.offset with
        ⟨firstOffsetX, firstOffsetY⟩
      rcases secondLiteralOffsetEq :
          secondTagged.1.literal.offset with
        ⟨secondOffsetX, secondOffsetY⟩
      rcases PeriodicCNF.clauseAnchor secondTagged.1.clause with
        ⟨anchorX, anchorY⟩
      simp only [Cell.sub, Prod.mk.injEq,
        firstLiteralOffsetEq, secondLiteralOffsetEq]
        at normalizedOffsetsEqual
      exact Prod.ext (by omega) (by omega)
    have firstLiteralOffsetEqual :
        firstTagged.1.literal.offset = firstLiteral.offset :=
      congrArg (fun incidence : CNFIncidence Variable =>
        incidence.literal.offset) firstIncidenceEq
    have secondLiteralOffsetEqual :
        secondTagged.1.literal.offset = secondLiteral.offset :=
      congrArg (fun incidence : CNFIncidence Variable =>
        incidence.literal.offset) secondIncidenceEq
    exact firstLiteralOffsetEqual.symm.trans
      (taggedOffsetsEqual.trans secondLiteralOffsetEqual)
  have literalIndicesEqual :
      first.2.2 = second.2.2 := by
    have clauseIncidenceKeysNodup :
        firstClause.IncidenceKeysNodup := by
      rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
        at incidenceKeysNodup
      exact incidenceKeysNodup firstClause
        (List.fst_mem_of_mem_zipIdx firstClauseMember)
    rw [PositionedPeriodicClause.IncidenceKeysNodup]
      at clauseIncidenceKeysNodup
    have firstIndexLt :
        firstTagged.1.literalIndex <
          firstClause.literals.length :=
      List.snd_lt_of_mem_zipIdx firstLiteralMember
    have secondIndexLt :
        secondTagged.1.literalIndex <
          firstClause.literals.length :=
      List.snd_lt_of_mem_zipIdx secondLiteralMember
    have keysEqualAtIndices :
        (firstClause.literals.map fun literal =>
          (literal.atom, literal.offset))[
            firstTagged.1.literalIndex]'(by
              simpa using firstIndexLt) =
          (firstClause.literals.map fun literal =>
            (literal.atom, literal.offset))[
            secondTagged.1.literalIndex]'(by
              simpa using secondIndexLt) := by
      simp only [List.getElem_map]
      have firstAt :
          firstClause.literals[
            firstTagged.1.literalIndex] = firstLiteral :=
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            firstLiteralMember)).2
      have secondAt :
          firstClause.literals[
            secondTagged.1.literalIndex] = secondLiteral :=
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            secondLiteralMember)).2
      rw [firstAt, secondAt]
      exact Prod.ext
        (firstAtom.trans secondAtom.symm)
        literalOffsetsEqual
    have taggedLiteralIndicesEqual :
        firstTagged.1.literalIndex =
          secondTagged.1.literalIndex :=
      clauseIncidenceKeysNodup.getElem_inj_iff.mp
        keysEqualAtIndices
    exact firstLiteralIndex.symm.trans
      (taggedLiteralIndicesEqual.trans secondLiteralIndex)
  apply copiesDifferent
  apply Prod.ext
  · exact atomsEqual
  · exact Prod.ext clauseIndicesEqual literalIndicesEqual

/-- Transport the endpoint-contact argument across a named presentation of
the same positioned incidence drawing. -/
theorem retainedOccurrenceTerminalVectorsInjective_of_drawing_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (drawing : PeriodicGridDrawing)
    (drawingEq :
      drawing =
        PositionedPeriodicCNF.incidenceDrawing
          source placement routes)
    (compatible :
      drawing.IsCompatible source.erase.incidenceGraph)
    (endpointContacts :
      drawing.RoutePointsMeetOnlyAtEndpoints)
    (incidenceKeysNodup : source.AllIncidenceKeysNodup) :
    RetainedOccurrenceTerminalVectorsInjective
      source.erase routes := by
  subst drawing
  exact
    retainedOccurrenceTerminalVectorsInjective_of_endpointContacts
      source placement routes compatible endpointContacts
      incidenceKeysNodup

end PeriodicEightOccurrenceSplit
end LeanTrominoes
