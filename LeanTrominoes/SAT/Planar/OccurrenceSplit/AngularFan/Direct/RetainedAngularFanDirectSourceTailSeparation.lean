/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineLinearSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictSeparationCheck
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceEnvelopeTable
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedRayLinearHull

/-!
# Complete-tail separation for direct source clauses

The coordinated 64-block prefixes handle the only permitted contact at a
shared direct-clause gate.  This file proves that everything after those
prefixes is contact-free.

Expanding two long staircase routes against one another would give a
quadratic finite check.  Instead, each escape route and a constant-size hull of each tail are folded
to bound an integer linear functional. The repeated radial staircase is
bounded analytically by its initial and final primitive blocks.  Four candidate
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



set_option synthInstance.maxSize 65536

private theorem foldl_max_le (normal : Cell) (route : List Cell) (initial upper : Int)
    (initialBound : initial ≤ upper)
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    route.foldl (fun bound point => max bound (Cell.linearValue normal point)) initial ≤ upper := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (max_le initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem foldl_min_ge (normal : Cell) (route : List Cell) (initial lower : Int)
    (initialBound : lower ≤ initial)
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ route.foldl (fun bound point => min bound (Cell.linearValue normal point)) initial := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (le_min initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem maximum_le_of_bounded (normal : Cell) (route : List Cell) (upper : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    routeLinearMaximum normal route ≤ upper := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_max_le normal (head :: tail) _ upper
      (bounded _ (by simp)) bounded

private theorem minimum_ge_of_bounded (normal : Cell) (route : List Cell) (lower : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ routeLinearMinimum normal route := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_min_ge normal (head :: tail) _ lower
      (bounded _ (by simp)) bounded

private def fastTailBounds (normal : Cell) (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : Int × Int :=
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let lane := retainedTerminalFanOuterLaneShiftRouteAt escapePoint terminal.1 slot
  let localRoute := retainedTerminalFanOuterLocalRouteAt center terminal.1 slot
  let ray := retainedTerminalFanOuterEscapedRemainingRay terminal
  let rayStart := Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let rayHull := ray.linearHull rayStart
  (max (max (routeLinearMaximum normal lane) (routeLinearMaximum normal localRoute))
      (routeLinearMaximum normal rayHull),
   min (min (routeLinearMinimum normal lane) (routeLinearMinimum normal localRoute))
      (routeLinearMinimum normal rayHull))

private theorem fastTailBounds_pointwise (normal center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) {point : Cell}
    (member : point ∈ retainedTerminalFanOuterCoordinatedEscapedCompleteTail center terminal slot) :
    (fastTailBounds normal center terminal slot).2 ≤ Cell.linearValue normal point ∧
      Cell.linearValue normal point ≤ (fastTailBounds normal center terminal slot).1 := by
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let lane := retainedTerminalFanOuterLaneShiftRouteAt escapePoint terminal.1 slot
  let localRoute := retainedTerminalFanOuterLocalRouteAt center terminal.1 slot
  let ray := retainedTerminalFanOuterEscapedRemainingRay terminal
  let rayStart := Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let rayHull := ray.linearHull rayStart
  change point ∈ joinAtEndpoint (joinAtEndpoint lane (ray.rasterize rayStart)) localRoute at member
  change min (min (routeLinearMinimum normal lane) (routeLinearMinimum normal localRoute))
      (routeLinearMinimum normal rayHull) ≤ Cell.linearValue normal point ∧
    Cell.linearValue normal point ≤
      max (max (routeLinearMaximum normal lane) (routeLinearMaximum normal localRoute))
        (routeLinearMaximum normal rayHull)
  rcases mem_joinAtEndpoint member with radialMember | localMember
  · rcases mem_joinAtEndpoint radialMember with laneMember | rayMember
    · have lo := routeLinearMinimum_le_linearValue normal lane laneMember
      have hi := linearValue_le_routeLinearMaximum normal lane laneMember
      constructor <;> omega
    · have bounds := ray.rasterize_linearBounds_of_hull rayStart normal
        (routeLinearMinimum normal rayHull) (routeLinearMaximum normal rayHull)
        (fun p hp => ⟨routeLinearMinimum_le_linearValue normal rayHull hp,
          linearValue_le_routeLinearMaximum normal rayHull hp⟩) rayMember
      constructor <;> omega
  · have lo := routeLinearMinimum_le_linearValue normal localRoute localMember
    have hi := linearValue_le_routeLinearMaximum normal localRoute localMember
    constructor <;> omega

private theorem fastTailBounds_envelope (normal center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    routeLinearMaximum normal (retainedTerminalFanOuterCoordinatedEscapedCompleteTail center terminal slot) ≤
        (fastTailBounds normal center terminal slot).1 ∧
      (fastTailBounds normal center terminal slot).2 ≤
        routeLinearMinimum normal (retainedTerminalFanOuterCoordinatedEscapedCompleteTail center terminal slot) := by
  have nonempty : retainedTerminalFanOuterCoordinatedEscapedCompleteTail center terminal slot ≠ [] := by
    intro empty
    have head := retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head? center terminal slot
    simp [empty] at head
  constructor
  · exact maximum_le_of_bounded _ _ _ nonempty (fun point member =>
      (fastTailBounds_pointwise normal center terminal slot member).2)
  · exact minimum_ge_of_bounded _ _ _ nonempty (fun point member =>
      (fastTailBounds_pointwise normal center terminal slot member).1)

private def computedEnvelope (normal : Cell) (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : SourceRouteEnvelope :=
  let escape := (retainedDirectSourceFanEscapeAt kind index slot).route
  ((routeLinearMaximum normal escape, routeLinearMinimum normal escape),
   fastTailBounds normal (retainedDirectSourceFanCenterAt kind index)
     (retainedDirectSourceFanTerminalAt kind index) slot)
private def computedPairEnvelopes (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length) : SourcePairEnvelopes :=
  (retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex).map fun normal =>
    (List.ofFn (computedEnvelope normal kind firstIndex),
     List.ofFn (computedEnvelope normal kind secondIndex))
private def computedEnvelopeTable (kind : RetainedDirectClauseKind) : SourceEnvelopeTable :=
  List.ofFn fun firstIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
  List.ofFn fun secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
    if firstIndex.val < secondIndex.val then computedPairEnvelopes kind firstIndex secondIndex else []

private theorem envelopeTable_case0 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 0) = computedEnvelopeTable (.crossover 0) := by
  decide +kernel

private theorem envelopeTable_case1 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 1) = computedEnvelopeTable (.crossover 1) := by
  decide +kernel

private theorem envelopeTable_case2 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 2) = computedEnvelopeTable (.crossover 2) := by
  decide +kernel

private theorem envelopeTable_case3 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 3) = computedEnvelopeTable (.crossover 3) := by
  decide +kernel

private theorem envelopeTable_case4 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 4) = computedEnvelopeTable (.crossover 4) := by
  decide +kernel

private theorem envelopeTable_case5 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 5) = computedEnvelopeTable (.crossover 5) := by
  decide +kernel

private theorem envelopeTable_case6 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 6) = computedEnvelopeTable (.crossover 6) := by
  decide +kernel

private theorem envelopeTable_case7 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 7) = computedEnvelopeTable (.crossover 7) := by
  decide +kernel

private theorem envelopeTable_case8 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 8) = computedEnvelopeTable (.crossover 8) := by
  decide +kernel

private theorem envelopeTable_case9 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 9) = computedEnvelopeTable (.crossover 9) := by
  decide +kernel

private theorem envelopeTable_case10 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 10) = computedEnvelopeTable (.crossover 10) := by
  decide +kernel

private theorem envelopeTable_case11 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 11) = computedEnvelopeTable (.crossover 11) := by
  decide +kernel

private theorem envelopeTable_case12 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 12) = computedEnvelopeTable (.crossover 12) := by
  decide +kernel

private theorem envelopeTable_case13 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 13) = computedEnvelopeTable (.crossover 13) := by
  decide +kernel

private theorem envelopeTable_case14 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 14) = computedEnvelopeTable (.crossover 14) := by
  decide +kernel

private theorem envelopeTable_case15 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 15) = computedEnvelopeTable (.crossover 15) := by
  decide +kernel

private theorem envelopeTable_case16 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 16) = computedEnvelopeTable (.crossover 16) := by
  decide +kernel

private theorem envelopeTable_case17 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 17) = computedEnvelopeTable (.crossover 17) := by
  decide +kernel

private theorem envelopeTable_case18 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 18) = computedEnvelopeTable (.crossover 18) := by
  decide +kernel

private theorem envelopeTable_case19 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 19) = computedEnvelopeTable (.crossover 19) := by
  decide +kernel

private theorem envelopeTable_case20 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 20) = computedEnvelopeTable (.crossover 20) := by
  decide +kernel

private theorem envelopeTable_case21 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 21) = computedEnvelopeTable (.crossover 21) := by
  decide +kernel

private theorem envelopeTable_case22 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 22) = computedEnvelopeTable (.crossover 22) := by
  decide +kernel

private theorem envelopeTable_case23 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 23) = computedEnvelopeTable (.crossover 23) := by
  decide +kernel

private theorem envelopeTable_case24 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 24) = computedEnvelopeTable (.crossover 24) := by
  decide +kernel

private theorem envelopeTable_case25 :
    retainedDirectSourceCachedEnvelopeTable (.crossover 25) = computedEnvelopeTable (.crossover 25) := by
  decide +kernel

private theorem envelopeTable_case26 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .left 0) = computedEnvelopeTable (.duplicator .left 0) := by
  decide +kernel

private theorem envelopeTable_case27 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .left 1) = computedEnvelopeTable (.duplicator .left 1) := by
  decide +kernel

private theorem envelopeTable_case28 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .middle 0) = computedEnvelopeTable (.duplicator .middle 0) := by
  decide +kernel

private theorem envelopeTable_case29 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .middle 1) = computedEnvelopeTable (.duplicator .middle 1) := by
  decide +kernel

private theorem envelopeTable_case30 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .right 0) = computedEnvelopeTable (.duplicator .right 0) := by
  decide +kernel

private theorem envelopeTable_case31 :
    retainedDirectSourceCachedEnvelopeTable (.duplicator .right 1) = computedEnvelopeTable (.duplicator .right 1) := by
  decide +kernel

private theorem envelopeTable_case32 :
    retainedDirectSourceCachedEnvelopeTable .routedClause = computedEnvelopeTable .routedClause := by
  decide +kernel

private theorem cachedEnvelopeTable_eq_computed (kind : RetainedDirectClauseKind) :
    retainedDirectSourceCachedEnvelopeTable kind = computedEnvelopeTable kind := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact envelopeTable_case0
    · exact envelopeTable_case1
    · exact envelopeTable_case2
    · exact envelopeTable_case3
    · exact envelopeTable_case4
    · exact envelopeTable_case5
    · exact envelopeTable_case6
    · exact envelopeTable_case7
    · exact envelopeTable_case8
    · exact envelopeTable_case9
    · exact envelopeTable_case10
    · exact envelopeTable_case11
    · exact envelopeTable_case12
    · exact envelopeTable_case13
    · exact envelopeTable_case14
    · exact envelopeTable_case15
    · exact envelopeTable_case16
    · exact envelopeTable_case17
    · exact envelopeTable_case18
    · exact envelopeTable_case19
    · exact envelopeTable_case20
    · exact envelopeTable_case21
    · exact envelopeTable_case22
    · exact envelopeTable_case23
    · exact envelopeTable_case24
    · exact envelopeTable_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact envelopeTable_case26
      · exact envelopeTable_case27
    | middle =>
      fin_cases index
      · exact envelopeTable_case28
      · exact envelopeTable_case29
    | right =>
      fin_cases index
      · exact envelopeTable_case30
      · exact envelopeTable_case31
  | routedClause => exact envelopeTable_case32

private def separated (a b : Int × Int) : Bool :=
  decide (a.1 < b.2 ∨ b.1 < a.2)

private def pairCheck (items : SourcePairEnvelopes)
    (firstSlot secondSlot : RetainedTerminalSlot) (firstTail secondTail : Bool) : Bool :=
  items.any fun pair =>
    let first := pair.1.getD firstSlot.val ((0, 0), (0, 0))
    let second := pair.2.getD secondSlot.val ((0, 0), (0, 0))
    separated (if firstTail then first.2 else first.1)
      (if secondTail then second.2 else second.1)

private theorem some_iff_any (normals : List Cell) (first second : List Cell) :
    RoutesLinearlySeparatedBySome normals first second ↔
      normals.any (fun normal => decide (RoutesLinearlySeparatedBy normal first second)) = true := by
  induction normals with
  | nil => simp [RoutesLinearlySeparatedBySome]
  | cons normal normals ih => simp [RoutesLinearlySeparatedBySome, ih]

private theorem getD_ofFn_eq {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (fallback : α) :
    (List.ofFn f).getD i.val fallback = f i := by
  simp

private def selectedRoute (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (isTail : Bool) : List Cell :=
  if isTail then retainedDirectSourceFanCompleteTailAt kind index slot
    else (retainedDirectSourceFanEscapeAt kind index slot).route

private def selectedBounds (normal : Cell) (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (isTail : Bool) : Int × Int :=
  if isTail then (computedEnvelope normal kind index slot).2
    else (computedEnvelope normal kind index slot).1

private theorem selectedBounds_sound (normal : Cell) (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (isTail : Bool) :
    routeLinearMaximum normal (selectedRoute kind index slot isTail) ≤
        (selectedBounds normal kind index slot isTail).1 ∧
      (selectedBounds normal kind index slot isTail).2 ≤
        routeLinearMinimum normal (selectedRoute kind index slot isTail) := by
  cases isTail with
  | false => exact ⟨le_refl _, le_refl _⟩
  | true => exact fastTailBounds_envelope normal _ _ slot

private theorem pairCheck_sound (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot) (firstTail secondTail : Bool)
    (checked : pairCheck (computedPairEnvelopes kind firstIndex secondIndex)
      firstSlot secondSlot firstTail secondTail = true) :
    RoutesLinearlySeparatedBySome
      (retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex)
      (selectedRoute kind firstIndex firstSlot firstTail)
      (selectedRoute kind secondIndex secondSlot secondTail) := by
  simp only [pairCheck, computedPairEnvelopes, List.any_map, Function.comp_def,
    getD_ofFn_eq, List.any_eq_true] at checked
  rcases checked with ⟨normal, normalMember, separatedCheck⟩
  change separated (selectedBounds normal kind firstIndex firstSlot firstTail)
    (selectedBounds normal kind secondIndex secondSlot secondTail) = true at separatedCheck
  simp only [separated, decide_eq_true_eq] at separatedCheck
  rw [some_iff_any]
  apply List.any_eq_true.mpr
  refine ⟨normal, normalMember, ?_⟩
  simp only [decide_eq_true_eq]
  have firstBound := selectedBounds_sound normal kind firstIndex firstSlot firstTail
  have secondBound := selectedBounds_sound normal kind secondIndex secondSlot secondTail
  rcases separatedCheck with h | h
  · exact Or.inl (lt_of_le_of_lt firstBound.1 (lt_of_lt_of_le h secondBound.2))
  · exact Or.inr (lt_of_le_of_lt secondBound.1 (lt_of_lt_of_le h firstBound.2))

private theorem tablePair_eq (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length)
    (different : firstIndex.val < secondIndex.val) :
    ((computedEnvelopeTable kind).getD firstIndex.val []).getD secondIndex.val [] =
      computedPairEnvelopes kind firstIndex secondIndex := by
  simp only [computedEnvelopeTable, getD_ofFn_eq, if_pos different]

private def tableCheck (kind : RetainedDirectClauseKind) (table : SourceEnvelopeTable) :=
  finiteAll fun firstIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
      guardedCheck (firstIndex.val < secondIndex.val)
        (finiteAll fun firstSlot : RetainedTerminalSlot =>
          finiteAll fun secondSlot : RetainedTerminalSlot =>
            let pair := (table.getD firstIndex.val []).getD secondIndex.val []
            pairCheck pair firstSlot secondSlot false true &&
              pairCheck pair firstSlot secondSlot true false &&
              pairCheck pair firstSlot secondSlot true true)

private theorem normals_symm : ∀ (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length),
    retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex =
      retainedDirectSourcePairCandidateNormals kind secondIndex firstIndex := by
  decide +kernel

private theorem separatedSome_symm (normals : List Cell) (first second : List Cell)
    (h : RoutesLinearlySeparatedBySome normals first second) :
    RoutesLinearlySeparatedBySome normals second first := by
  induction normals with
  | nil => exact False.elim h
  | cons normal normals ih =>
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (ih h)

private theorem tableCheck_sound (kind : RetainedDirectClauseKind)
    (table : SourceEnvelopeTable)
    (tableEq : table = computedEnvelopeTable kind)
    (checked : tableCheck kind table = true) : kind.SourceCompleteTailsSeparated := by
  subst table
  simp only [tableCheck, finiteAll_eq_true, guardedCheck_eq_true, Bool.and_eq_true] at checked
  have ordered : ∀ firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length,
      firstIndex.val < secondIndex.val → ∀ firstSlot secondSlot : RetainedTerminalSlot,
      RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex)
          (retainedDirectSourceFanEscapeAt kind firstIndex firstSlot).route
          (retainedDirectSourceFanCompleteTailAt kind secondIndex secondSlot) ∧
        RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex)
          (retainedDirectSourceFanCompleteTailAt kind firstIndex firstSlot)
          (retainedDirectSourceFanEscapeAt kind secondIndex secondSlot).route ∧
        RoutesLinearlySeparatedBySome
          (retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex)
          (retainedDirectSourceFanCompleteTailAt kind firstIndex firstSlot)
          (retainedDirectSourceFanCompleteTailAt kind secondIndex secondSlot) := by
    intro firstIndex secondIndex different firstSlot secondSlot
    have h := checked firstIndex secondIndex different firstSlot secondSlot
    rw [tablePair_eq kind firstIndex secondIndex different] at h
    exact ⟨pairCheck_sound kind firstIndex secondIndex firstSlot secondSlot false true h.1.1,
      pairCheck_sound kind firstIndex secondIndex firstSlot secondSlot true false h.1.2,
      pairCheck_sound kind firstIndex secondIndex firstSlot secondSlot true true h.2⟩
  intro firstIndex secondIndex different firstSlot secondSlot
  by_cases before : firstIndex.val < secondIndex.val
  · exact ordered firstIndex secondIndex before firstSlot secondSlot
  · have differentVals : firstIndex.val ≠ secondIndex.val := fun h => different (Fin.ext h)
    have reverseBefore : secondIndex.val < firstIndex.val := by omega
    have h := ordered secondIndex firstIndex reverseBefore secondSlot firstSlot
    rw [normals_symm kind secondIndex firstIndex] at h
    exact ⟨separatedSome_symm _ _ _ h.2.1,
      separatedSome_symm _ _ _ h.1, separatedSome_symm _ _ _ h.2.2⟩

private def sourceTailsCheck (kind : RetainedDirectClauseKind) : Bool :=
  tableCheck kind (retainedDirectSourceCachedEnvelopeTable kind)

private theorem sourceTailsCheck_sound (kind : RetainedDirectClauseKind)
    (checked : sourceTailsCheck kind = true) : kind.SourceCompleteTailsSeparated :=
  tableCheck_sound kind _ (cachedEnvelopeTable_eq_computed kind) checked

private theorem sourceTails_case0 : sourceTailsCheck (.crossover 0) = true := by
  decide +kernel

private theorem sourceTails_case1 : sourceTailsCheck (.crossover 1) = true := by
  decide +kernel

private theorem sourceTails_case2 : sourceTailsCheck (.crossover 2) = true := by
  decide +kernel

private theorem sourceTails_case3 : sourceTailsCheck (.crossover 3) = true := by
  decide +kernel

private theorem sourceTails_case4 : sourceTailsCheck (.crossover 4) = true := by
  decide +kernel

private theorem sourceTails_case5 : sourceTailsCheck (.crossover 5) = true := by
  decide +kernel

private theorem sourceTails_case6 : sourceTailsCheck (.crossover 6) = true := by
  decide +kernel

private theorem sourceTails_case7 : sourceTailsCheck (.crossover 7) = true := by
  decide +kernel

private theorem sourceTails_case8 : sourceTailsCheck (.crossover 8) = true := by
  decide +kernel

private theorem sourceTails_case9 : sourceTailsCheck (.crossover 9) = true := by
  decide +kernel

private theorem sourceTails_case10 : sourceTailsCheck (.crossover 10) = true := by
  decide +kernel

private theorem sourceTails_case11 : sourceTailsCheck (.crossover 11) = true := by
  decide +kernel

private theorem sourceTails_case12 : sourceTailsCheck (.crossover 12) = true := by
  decide +kernel

private theorem sourceTails_case13 : sourceTailsCheck (.crossover 13) = true := by
  decide +kernel

private theorem sourceTails_case14 : sourceTailsCheck (.crossover 14) = true := by
  decide +kernel

private theorem sourceTails_case15 : sourceTailsCheck (.crossover 15) = true := by
  decide +kernel

private theorem sourceTails_case16 : sourceTailsCheck (.crossover 16) = true := by
  decide +kernel

private theorem sourceTails_case17 : sourceTailsCheck (.crossover 17) = true := by
  decide +kernel

private theorem sourceTails_case18 : sourceTailsCheck (.crossover 18) = true := by
  decide +kernel

private theorem sourceTails_case19 : sourceTailsCheck (.crossover 19) = true := by
  decide +kernel

private theorem sourceTails_case20 : sourceTailsCheck (.crossover 20) = true := by
  decide +kernel

private theorem sourceTails_case21 : sourceTailsCheck (.crossover 21) = true := by
  decide +kernel

private theorem sourceTails_case22 : sourceTailsCheck (.crossover 22) = true := by
  decide +kernel

private theorem sourceTails_case23 : sourceTailsCheck (.crossover 23) = true := by
  decide +kernel

private theorem sourceTails_case24 : sourceTailsCheck (.crossover 24) = true := by
  decide +kernel

private theorem sourceTails_case25 : sourceTailsCheck (.crossover 25) = true := by
  decide +kernel

private theorem sourceTails_case26 : sourceTailsCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem sourceTails_case27 : sourceTailsCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem sourceTails_case28 : sourceTailsCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem sourceTails_case29 : sourceTailsCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem sourceTails_case30 : sourceTailsCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem sourceTails_case31 : sourceTailsCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem sourceTails_case32 : sourceTailsCheck (.routedClause) = true := by
  decide +kernel

/-- Exhaustive certification of all three strict post-prefix interactions
for every direct component and all occurrence slots. -/
theorem retainedDirectSourceCompleteTails_separated :
    ∀ kind : RetainedDirectClauseKind, kind.SourceCompleteTailsSeparated := by
  intro kind
  cases kind with
  | crossover index =>
    fin_cases index
    · exact sourceTailsCheck_sound _ sourceTails_case0
    · exact sourceTailsCheck_sound _ sourceTails_case1
    · exact sourceTailsCheck_sound _ sourceTails_case2
    · exact sourceTailsCheck_sound _ sourceTails_case3
    · exact sourceTailsCheck_sound _ sourceTails_case4
    · exact sourceTailsCheck_sound _ sourceTails_case5
    · exact sourceTailsCheck_sound _ sourceTails_case6
    · exact sourceTailsCheck_sound _ sourceTails_case7
    · exact sourceTailsCheck_sound _ sourceTails_case8
    · exact sourceTailsCheck_sound _ sourceTails_case9
    · exact sourceTailsCheck_sound _ sourceTails_case10
    · exact sourceTailsCheck_sound _ sourceTails_case11
    · exact sourceTailsCheck_sound _ sourceTails_case12
    · exact sourceTailsCheck_sound _ sourceTails_case13
    · exact sourceTailsCheck_sound _ sourceTails_case14
    · exact sourceTailsCheck_sound _ sourceTails_case15
    · exact sourceTailsCheck_sound _ sourceTails_case16
    · exact sourceTailsCheck_sound _ sourceTails_case17
    · exact sourceTailsCheck_sound _ sourceTails_case18
    · exact sourceTailsCheck_sound _ sourceTails_case19
    · exact sourceTailsCheck_sound _ sourceTails_case20
    · exact sourceTailsCheck_sound _ sourceTails_case21
    · exact sourceTailsCheck_sound _ sourceTails_case22
    · exact sourceTailsCheck_sound _ sourceTails_case23
    · exact sourceTailsCheck_sound _ sourceTails_case24
    · exact sourceTailsCheck_sound _ sourceTails_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact sourceTailsCheck_sound _ sourceTails_case26
      · exact sourceTailsCheck_sound _ sourceTails_case27
    | middle =>
      fin_cases index
      · exact sourceTailsCheck_sound _ sourceTails_case28
      · exact sourceTailsCheck_sound _ sourceTails_case29
    | right =>
      fin_cases index
      · exact sourceTailsCheck_sound _ sourceTails_case30
      · exact sourceTailsCheck_sound _ sourceTails_case31
  | routedClause => exact sourceTailsCheck_sound _ sourceTails_case32

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
