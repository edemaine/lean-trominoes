/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.OrthogonalPolylineLinearSeparation

/-!
# Complete-tail separation for direct source clauses

The coordinated 64-block prefixes handle the only permitted contact at a
shared direct-clause gate.  This file proves that everything after those
prefixes is contact-free.

Expanding two long staircase routes against one another would give a
quadratic finite check.  Instead, each route is folded once to obtain its
minimum and maximum under an integer linear functional.  Four candidate
normals suffice for every direct component:

* the angular bisector;
* an `8 : 1` bias toward the earlier ray, whose `8 / 9` slope exceeds the
  maximum lane-displacement ratio `56 / 64`;
* the two limiting ray-boundary normals.

An exhaustive check over the finite direct-component atlas and the eight
occurrence slots selects one of these half-planes for each of the two
escape--tail interactions and the tail--tail interaction.  The generic
linear-separation theorem then upgrades these one-dimensional envelopes to
complete continuous route separation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Maximum listed linear value of a route.  The `headD` seed makes the
definition total; membership bounds below do not require nonemptiness. -/
def routeLinearMaximum (normal : Cell) (route : List Cell) : Int :=
  route.foldl
    (fun bound point => max bound (Cell.linearValue normal point))
    (Cell.linearValue normal (route.headD (0, 0)))

/-- Minimum listed linear value of a route. -/
def routeLinearMinimum (normal : Cell) (route : List Cell) : Int :=
  route.foldl
    (fun bound point => min bound (Cell.linearValue normal point))
    (Cell.linearValue normal (route.headD (0, 0)))

private theorem initial_le_foldl_max
    (values : List Cell) (normal : Cell) (initial : Int) :
    initial ≤
      values.foldl
        (fun bound point =>
          max bound (Cell.linearValue normal point))
        initial := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left _ _) (induction _)

private theorem foldl_min_le_initial
    (values : List Cell) (normal : Cell) (initial : Int) :
    values.foldl
        (fun bound point =>
          min bound (Cell.linearValue normal point))
        initial ≤
      initial := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact le_trans (induction _) (min_le_left _ _)

private theorem linearValue_le_foldl_max_of_mem
    (normal : Cell) (route : List Cell) (initial : Int)
    {point : Cell} (pointMember : point ∈ route) :
    Cell.linearValue normal point ≤
      route.foldl
        (fun bound listedPoint =>
          max bound (Cell.linearValue normal listedPoint))
        initial := by
  induction route generalizing initial point with
  | nil => simp at pointMember
  | cons head tail induction =>
      simp only [List.mem_cons] at pointMember
      simp only [List.foldl_cons]
      rcases pointMember with rfl | pointMember
      · exact le_trans (le_max_right _ _)
          (initial_le_foldl_max tail normal _)
      · exact induction _ pointMember

private theorem foldl_min_le_linearValue_of_mem
    (normal : Cell) (route : List Cell) (initial : Int)
    {point : Cell} (pointMember : point ∈ route) :
    route.foldl
        (fun bound listedPoint =>
          min bound (Cell.linearValue normal listedPoint))
        initial ≤
      Cell.linearValue normal point := by
  induction route generalizing initial point with
  | nil => simp at pointMember
  | cons head tail induction =>
      simp only [List.mem_cons] at pointMember
      simp only [List.foldl_cons]
      rcases pointMember with rfl | pointMember
      · exact le_trans
          (foldl_min_le_initial tail normal _)
          (min_le_right _ _)
      · exact induction _ pointMember

/-- Every listed point lies below the computed route maximum. -/
theorem linearValue_le_routeLinearMaximum
    (normal : Cell) (route : List Cell)
    {point : Cell} (pointMember : point ∈ route) :
    Cell.linearValue normal point ≤
      routeLinearMaximum normal route := by
  unfold routeLinearMaximum
  exact linearValue_le_foldl_max_of_mem
    normal route _ pointMember

/-- Every listed point lies above the computed route minimum. -/
theorem routeLinearMinimum_le_linearValue
    (normal : Cell) (route : List Cell)
    {point : Cell} (pointMember : point ∈ route) :
    routeLinearMinimum normal route ≤
      Cell.linearValue normal point := by
  unfold routeLinearMinimum
  exact foldl_min_le_linearValue_of_mem
    normal route _ pointMember

/-- Two routes have disjoint computed envelopes under one normal, in either
orientation. -/
def RoutesLinearlySeparatedBy
    (normal : Cell) (first second : List Cell) : Prop :=
  routeLinearMaximum normal first <
      routeLinearMinimum normal second ∨
    routeLinearMaximum normal second <
      routeLinearMinimum normal first

instance (normal : Cell) (first second : List Cell) :
    Decidable (RoutesLinearlySeparatedBy normal first second) := by
  unfold RoutesLinearlySeparatedBy
  infer_instance

/-- A disjoint computed envelope gives contact-free continuous separation,
with the second disjunct handled by reversing the route order. -/
theorem routesStrictlyAvoidEachOther_of_linearlySeparatedBy
    (normal : Cell) (first second : List Cell)
    (separated :
      RoutesLinearlySeparatedBy normal first second) :
    RoutesStrictlyAvoidEachOther first second := by
  rcases separated with firstBeforeSecond | secondBeforeFirst
  · exact
      routesStrictlyAvoidEachOther_of_linear_separated
        normal (routeLinearMaximum normal first)
        (fun _ pointMember =>
          linearValue_le_routeLinearMaximum
            normal first pointMember)
        (fun _ pointMember =>
          lt_of_lt_of_le firstBeforeSecond
            (routeLinearMinimum_le_linearValue
              normal second pointMember))
  · exact
      (routesStrictlyAvoidEachOther_of_linear_separated
        normal (routeLinearMaximum normal second)
        (fun _ pointMember =>
          linearValue_le_routeLinearMaximum
            normal second pointMember)
        (fun _ pointMember =>
          lt_of_lt_of_le secondBeforeFirst
            (routeLinearMinimum_le_linearValue
              normal first pointMember))).symm

/-- A finite family contains a computed linear separator for two routes. -/
def RoutesLinearlySeparatedBySome :
    List Cell → List Cell → List Cell → Prop
  | [], _, _ => False
  | normal :: normals, first, second =>
      RoutesLinearlySeparatedBy normal first second ∨
        RoutesLinearlySeparatedBySome normals first second

instance (normals : List Cell) (first second : List Cell) :
    Decidable (RoutesLinearlySeparatedBySome normals first second) := by
  induction normals with
  | nil => exact isFalse id
  | cons normal normals induction =>
      simp only [RoutesLinearlySeparatedBySome]
      exact instDecidableOr

/-- Extracting the selected normal from a finite family gives strict route
separation. -/
theorem routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
    (normals : List Cell) (first second : List Cell)
    (separated :
      RoutesLinearlySeparatedBySome normals first second) :
    RoutesStrictlyAvoidEachOther first second := by
  induction normals with
  | nil => exact False.elim separated
  | cons normal normals induction =>
      change
        RoutesLinearlySeparatedBy normal first second ∨
          RoutesLinearlySeparatedBySome normals first second
        at separated
      rcases separated with separated | separated
      · exact
          routesStrictlyAvoidEachOther_of_linearlySeparatedBy
            normal first second separated
      · exact induction separated

/-- One primitive inward displacement selected by a direct atlas entry. -/
def retainedDirectSourceInwardPrimitiveAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  (retainedTerminalFanOuterInwardRayOfLength
    (retainedDirectSourcePrefixChoiceAt kind index).direction 1).vector

/-- The primitive belonging to the smaller retained angular rank. -/
def retainedDirectSourceEarlierPrimitive
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  if
    (retainedDirectSourcePrefixChoiceAt
      kind firstIndex).direction.angularRank <
    (retainedDirectSourcePrefixChoiceAt
      kind secondIndex).direction.angularRank
  then
    retainedDirectSourceInwardPrimitiveAt kind firstIndex
  else
    retainedDirectSourceInwardPrimitiveAt kind secondIndex

/-- The primitive belonging to the larger retained angular rank. -/
def retainedDirectSourceLaterPrimitive
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  if
    (retainedDirectSourcePrefixChoiceAt
      kind firstIndex).direction.angularRank <
    (retainedDirectSourcePrefixChoiceAt
      kind secondIndex).direction.angularRank
  then
    retainedDirectSourceInwardPrimitiveAt kind secondIndex
  else
    retainedDirectSourceInwardPrimitiveAt kind firstIndex

/-- Rotate a cell vector counterclockwise by a quarter turn. -/
def rotateCellQuarterTurn (vector : Cell) : Cell :=
  (-vector.2, vector.1)

/-- A separator normal between two angularly ordered inward primitives.
For opposite rays the primitive itself is the separating normal.  Otherwise
`weight = 1` is the bisector, `weight = 8` supplies the tight lane margin,
and `weight = 0` is the later-ray boundary. -/
def retainedDirectSourcePairNormalWithWeight
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (weight : Nat) : Cell :=
  let earlier :=
    retainedDirectSourceEarlierPrimitive
      kind firstIndex secondIndex
  let later :=
    retainedDirectSourceLaterPrimitive
      kind firstIndex secondIndex
  if Cell.add earlier later = (0, 0) then
    earlier
  else
    rotateCellQuarterTurn
      (Cell.add (Cell.scale weight earlier) later)

/-- The limiting earlier-ray boundary normal. -/
def retainedDirectSourceEarlierBoundaryNormal
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  rotateCellQuarterTurn
    (retainedDirectSourceEarlierPrimitive
      kind firstIndex secondIndex)

/-- Four half-plane directions suffice for every direct-source piece pair:
bisector, tight earlier bias, later boundary, and earlier boundary. -/
def retainedDirectSourcePairCandidateNormals
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length) :
    List Cell :=
  [retainedDirectSourcePairNormalWithWeight
      kind firstIndex secondIndex 1,
    retainedDirectSourcePairNormalWithWeight
      kind firstIndex secondIndex 8,
    retainedDirectSourcePairNormalWithWeight
      kind firstIndex secondIndex 0,
    retainedDirectSourceEarlierBoundaryNormal
      kind firstIndex secondIndex]

/-- The three post-prefix interactions required for one direct-clause
literal pair all have a computed separator from the four-normal family. -/
def RetainedDirectClauseKind.SourceCompleteTailsSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length),
    firstIndex ≠ secondIndex →
    ∀ firstSlot secondSlot : RetainedTerminalSlot,
      RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals
            kind firstIndex secondIndex)
          (retainedDirectSourceFanEscapeAt
            kind firstIndex firstSlot).route
          (retainedDirectSourceFanCompleteTailAt
            kind secondIndex secondSlot) ∧
        RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals
            kind firstIndex secondIndex)
          (retainedDirectSourceFanCompleteTailAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFanEscapeAt
            kind secondIndex secondSlot).route ∧
        RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals
            kind firstIndex secondIndex)
          (retainedDirectSourceFanCompleteTailAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFanCompleteTailAt
            kind secondIndex secondSlot)

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceCompleteTailsSeparated := by
  unfold RetainedDirectClauseKind.SourceCompleteTailsSeparated
  let firstDecidable :
      ∀ firstIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            firstIndex ≠ secondIndex →
            ∀ firstSlot secondSlot : RetainedTerminalSlot,
              RoutesLinearlySeparatedBySome
                  (retainedDirectSourcePairCandidateNormals
                    kind firstIndex secondIndex)
                  (retainedDirectSourceFanEscapeAt
                    kind firstIndex firstSlot).route
                  (retainedDirectSourceFanCompleteTailAt
                    kind secondIndex secondSlot) ∧
                RoutesLinearlySeparatedBySome
                  (retainedDirectSourcePairCandidateNormals
                    kind firstIndex secondIndex)
                  (retainedDirectSourceFanCompleteTailAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFanEscapeAt
                    kind secondIndex secondSlot).route ∧
                RoutesLinearlySeparatedBySome
                  (retainedDirectSourcePairCandidateNormals
                    kind firstIndex secondIndex)
                  (retainedDirectSourceFanCompleteTailAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFanCompleteTailAt
                    kind secondIndex secondSlot)) :=
    fun firstIndex => by
      letI :
          ∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            Decidable
              (firstIndex ≠ secondIndex →
              ∀ firstSlot secondSlot : RetainedTerminalSlot,
                RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                    (retainedDirectSourceFanEscapeAt
                      kind firstIndex firstSlot).route
                    (retainedDirectSourceFanCompleteTailAt
                      kind secondIndex secondSlot) ∧
                  RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                    (retainedDirectSourceFanCompleteTailAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFanEscapeAt
                      kind secondIndex secondSlot).route ∧
                  RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                    (retainedDirectSourceFanCompleteTailAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFanCompleteTailAt
                      kind secondIndex secondSlot)) :=
        fun secondIndex => by
          letI :
              ∀ firstSlot : RetainedTerminalSlot,
                Decidable
                  (∀ secondSlot : RetainedTerminalSlot,
                    RoutesLinearlySeparatedBySome
                        (retainedDirectSourcePairCandidateNormals
                          kind firstIndex secondIndex)
                        (retainedDirectSourceFanEscapeAt
                          kind firstIndex firstSlot).route
                        (retainedDirectSourceFanCompleteTailAt
                          kind secondIndex secondSlot) ∧
                      RoutesLinearlySeparatedBySome
                        (retainedDirectSourcePairCandidateNormals
                          kind firstIndex secondIndex)
                        (retainedDirectSourceFanCompleteTailAt
                          kind firstIndex firstSlot)
                        (retainedDirectSourceFanEscapeAt
                          kind secondIndex secondSlot).route ∧
                      RoutesLinearlySeparatedBySome
                        (retainedDirectSourcePairCandidateNormals
                          kind firstIndex secondIndex)
                        (retainedDirectSourceFanCompleteTailAt
                          kind firstIndex firstSlot)
                        (retainedDirectSourceFanCompleteTailAt
                          kind secondIndex secondSlot)) :=
            fun _ => Fintype.decidableForallFintype
          letI :
              Decidable
                (∀ firstSlot secondSlot : RetainedTerminalSlot,
                RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                    (retainedDirectSourceFanEscapeAt
                      kind firstIndex firstSlot).route
                    (retainedDirectSourceFanCompleteTailAt
                      kind secondIndex secondSlot) ∧
                  RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                    (retainedDirectSourceFanCompleteTailAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFanEscapeAt
                      kind secondIndex secondSlot).route ∧
                  RoutesLinearlySeparatedBySome
                    (retainedDirectSourcePairCandidateNormals
                      kind firstIndex secondIndex)
                  (retainedDirectSourceFanCompleteTailAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFanCompleteTailAt
                    kind secondIndex secondSlot)) :=
            Fintype.decidableForallFintype
          infer_instance
      exact Fintype.decidableForallFintype
  letI := firstDecidable
  exact Fintype.decidableForallFintype

/-- Exhaustive certification of all three strict post-prefix interactions
for every direct component and all occurrence slots. -/
theorem retainedDirectSourceCompleteTails_separated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceCompleteTailsSeparated := by
  native_decide

/-- The finite half-plane certificates upgraded to continuous strict
separation of the three concrete piece pairs. -/
theorem retainedDirectSourceFanPieces_strictlySeparated
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanEscapeAt
          kind firstIndex firstSlot).route
        (retainedDirectSourceFanCompleteTailAt
          kind secondIndex secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteTailAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFanEscapeAt
          kind secondIndex secondSlot).route ∧
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteTailAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFanCompleteTailAt
          kind secondIndex secondSlot) := by
  have separated :=
    retainedDirectSourceCompleteTails_separated
      kind firstIndex secondIndex indicesDifferent
        firstSlot secondSlot
  exact
    ⟨routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
        _ _ _ separated.1,
      routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
        _ _ _ separated.2.1,
      routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
        _ _ _ separated.2.2⟩

/-- A metadata-selected direct literal pair now has separated complete
coordinated routes with no remaining geometric hypotheses. -/
theorem
    RetainedDirectSourcePrefixPairSelection.completeRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : PeriodicOrthocrossing.DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
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
  have pieces :=
    retainedDirectSourceFanPieces_strictlySeparated
      selection.kind selection.firstIndex selection.secondIndex
      selection.indicesDifferent firstSlot secondSlot
  exact
    selection.concreteCompleteRoutes_separated
      firstSlot secondSlot pieces.1 pieces.2.1 pieces.2.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
