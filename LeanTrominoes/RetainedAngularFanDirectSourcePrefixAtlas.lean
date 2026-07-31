import LeanTrominoes.RetainedAngularFanOuterCoordinatedPrefixes
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Finite coordinated-prefix atlas for direct clause components

The direct planar-SAT components have only 33 clause shapes: 26 crossover
clauses, two clauses for each of three duplicator arms, and one routed source
clause.  This file records a two-block source prefix for every incidence in
those shapes.

Most entries coordinate only the first primitive block and then append one
canonical block.  Four three-incidence crossover clauses require a genuinely
joint two-block choice.  Exhaustive finite checks certify every entry's
endpoint and orthogonality and every distinct pair's continuous separation,
with their common origin as the only permitted listed contact.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A source incidence together with its selected relative two-block route. -/
structure RetainedDirectSourcePrefixChoice where
  direction : RetainedTerminalDirection
  route : List Cell
  deriving DecidableEq, Repr

/-- The eleven terminal directions, addressed by their retained angular
rank.  The fallback is irrelevant to the finite atlas. -/
def retainedTerminalDirectionOfAngularRank :
    Nat → RetainedTerminalDirection
  | 0 => .compass .east
  | 1 => .routedClause .left
  | 2 => .compass .southeast
  | 3 => .compass .south
  | 4 => .routedClause .right
  | 5 => .compass .southwest
  | 6 => .compass .west
  | 7 => .compass .northwest
  | 8 => .compass .north
  | 9 => .compass .northeast
  | 10 => .routedClause .middle
  | _ => .compass .east

/-- Extend a coordinated first primitive block by one canonical block. -/
def retainedDirectSourcePrefixFromFirstBlock
    (direction : RetainedTerminalDirection)
    (firstBlock : List Cell) : List Cell :=
  let checkpoint :=
    (retainedTerminalFanOuterInwardRayOfLength direction 1).vector
  joinAtEndpoint firstBlock
    ((retainedTerminalFanOuterInwardRayOfLength direction 1).rasterize
      checkpoint)

/-- Atlas entry whose supplied route reaches the one-block checkpoint. -/
def retainedDirectSourceFirstBlockChoice
    (rank : Nat) (route : List Cell) :
    RetainedDirectSourcePrefixChoice :=
  let direction := retainedTerminalDirectionOfAngularRank rank
  ⟨direction,
    retainedDirectSourcePrefixFromFirstBlock direction route⟩

/-- Atlas entry whose supplied route already reaches the two-block
checkpoint. -/
def retainedDirectSourceTwoBlockChoice
    (rank : Nat) (route : List Cell) :
    RetainedDirectSourcePrefixChoice :=
  ⟨retainedTerminalDirectionOfAngularRank rank, route⟩

private def p06 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 0 [(0, 0), (-1, 0)],
    retainedDirectSourceFirstBlockChoice 6
      [(0, 0), (0, -1), (1, -1), (1, 0)]]

private def p25 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 2
      [(0, 0), (-1, 0), (-1, -1)],
    retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (0, -1), (1, -1)]]

private def p876 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceTwoBlockChoice 8
      [(0, 0), (-1, 0), (-1, 1), (0, 1), (0, 2)],
    retainedDirectSourceTwoBlockChoice 7
      [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)],
    retainedDirectSourceTwoBlockChoice 6
      [(0, 0), (0, -1), (2, -1), (2, 0)]]

private def p356 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceTwoBlockChoice 3
      [(0, 0), (-1, 0), (-1, -1), (0, -1), (0, -2)],
    retainedDirectSourceTwoBlockChoice 5
      [(0, 0), (1, 0), (1, -2), (2, -2)],
    retainedDirectSourceTwoBlockChoice 6
      [(0, 0), (0, 1), (2, 1), (2, 0)]]

private def p96 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 9
      [(0, 0), (-1, 0), (-1, 1)],
    retainedDirectSourceFirstBlockChoice 6
      [(0, 0), (0, -1), (1, -1), (1, 0)]]

private def p57 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (-1, 0), (-1, -1), (1, -1)],
    retainedDirectSourceFirstBlockChoice 7
      [(0, 0), (1, 0), (1, 1)]]

private def p26 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 2
      [(0, 0), (-1, 0), (-1, -1)],
    retainedDirectSourceFirstBlockChoice 6
      [(0, 0), (0, -1), (1, -1), (1, 0)]]

private def p85 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 8
      [(0, 0), (-1, 0), (-1, 1), (0, 1)],
    retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (0, -1), (1, -1)]]

private def p386 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 3
      [(0, 0), (-1, 0), (-1, -1), (0, -1)],
    retainedDirectSourceFirstBlockChoice 8 [(0, 0), (0, 1)],
    retainedDirectSourceFirstBlockChoice 6 [(0, 0), (1, 0)]]

private def p37 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 3
      [(0, 0), (-1, 0), (-1, -1), (0, -1)],
    retainedDirectSourceFirstBlockChoice 7
      [(0, 0), (1, 0), (1, 1)]]

private def p38 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 3
      [(0, 0), (-1, 0), (-1, -1), (0, -1)],
    retainedDirectSourceFirstBlockChoice 8
      [(0, 0), (1, 0), (1, 1), (0, 1)]]

private def p28 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 2
      [(0, 0), (-1, 0), (-1, -1)],
    retainedDirectSourceFirstBlockChoice 8
      [(0, 0), (0, -1), (1, -1), (1, 1), (0, 1)]]

private def p038 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 0 [(0, 0), (-1, 0)],
    retainedDirectSourceFirstBlockChoice 3 [(0, 0), (0, -1)],
    retainedDirectSourceFirstBlockChoice 8
      [(0, 0), (1, 0), (1, 1), (0, 1)]]

private def p93 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 9
      [(0, 0), (-1, 0), (-1, 1)],
    retainedDirectSourceFirstBlockChoice 3 [(0, 0), (0, -1)]]

private def p29 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 2
      [(0, 0), (-1, 0), (-1, -1)],
    retainedDirectSourceFirstBlockChoice 9
      [(0, 0), (0, -1), (1, -1), (1, 1), (-1, 1)]]

private def p07 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 0 [(0, 0), (-1, 0)],
    retainedDirectSourceFirstBlockChoice 7
      [(0, 0), (0, -1), (1, -1), (1, 1)]]

private def p098 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceTwoBlockChoice 0 [(0, 0), (-2, 0)],
    retainedDirectSourceTwoBlockChoice 9
      [(0, 0), (1, 0), (1, 1), (-2, 1), (-2, 2)],
    retainedDirectSourceTwoBlockChoice 8
      [(0, 0), (0, -1), (2, -1), (2, 2), (0, 2)]]

private def p05 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 0 [(0, 0), (-1, 0)],
    retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (0, -1), (1, -1)]]

private def p023 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceTwoBlockChoice 0 [(0, 0), (-2, 0)],
    retainedDirectSourceTwoBlockChoice 2
      [(0, 0), (0, -1), (-2, -1), (-2, -2)],
    retainedDirectSourceTwoBlockChoice 3
      [(0, 0), (1, 0), (1, -2), (0, -2)]]

private def p97 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 9
      [(0, 0), (-1, 0), (-1, 1)],
    retainedDirectSourceFirstBlockChoice 7
      [(0, 0), (0, -1), (1, -1), (1, 1)]]

private def p75 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 7
      [(0, 0), (-1, 0), (-1, 1), (1, 1)],
    retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (0, -1), (1, -1)]]

private def p83 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 8
      [(0, 0), (-1, 0), (-1, 1), (0, 1)],
    retainedDirectSourceFirstBlockChoice 3 [(0, 0), (0, -1)]]

private def p68 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 6
      [(0, 0), (-1, 0), (-1, -1), (1, -1), (1, 0)],
    retainedDirectSourceFirstBlockChoice 8 [(0, 0), (0, 1)]]

private def p52 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 5
      [(0, 0), (-1, 0), (-1, 1), (1, 1), (1, -1)],
    retainedDirectSourceFirstBlockChoice 2
      [(0, 0), (0, -1), (-1, -1)]]

private def p1104 : List RetainedDirectSourcePrefixChoice :=
  [retainedDirectSourceFirstBlockChoice 1
      [(0, 0), (-1, 0), (-1, -1), (-3, -1), (-3, -2),
        (-6, -2), (-6, -3), (-8, -3), (-8, -4), (-9, -4)],
    retainedDirectSourceFirstBlockChoice 10
      [(0, 0), (1, 0), (1, 1), (-4, 1)],
    retainedDirectSourceFirstBlockChoice 4
      [(0, 0), (0, -2), (1, -2), (1, -4)]]

/-- A direct source component, indexed exactly as its fixed local formula. -/
inductive RetainedDirectClauseKind where
  | crossover (clauseIndex : Fin 26)
  | duplicator (arm : DuplicatorArm) (clauseIndex : Fin 2)
  | routedClause
  deriving DecidableEq, Repr, Fintype

/-- The coordinated prefix choices for every incidence of a direct clause. -/
def retainedDirectSourcePrefixChoices :
    RetainedDirectClauseKind → List RetainedDirectSourcePrefixChoice
  | .crossover clauseIndex =>
      match clauseIndex.val with
      | 0 => p06
      | 1 => p25
      | 2 => p876
      | 3 => p356
      | 4 => p96
      | 5 => p57
      | 6 => p26
      | 7 => p57
      | 8 => p85
      | 9 => p386
      | 10 => p37
      | 11 => p38
      | 12 => p06
      | 13 => p06
      | 14 => p38
      | 15 => p28
      | 16 => p038
      | 17 => p93
      | 18 => p29
      | 19 => p07
      | 20 => p29
      | 21 => p05
      | 22 => p098
      | 23 => p023
      | 24 => p97
      | 25 => p06
      | _ => []
  | .duplicator .left clauseIndex =>
      match clauseIndex.val with
      | 0 => p26
      | 1 => p07
      | _ => []
  | .duplicator .middle clauseIndex =>
      match clauseIndex.val with
      | 0 => p75
      | 1 => p83
      | _ => []
  | .duplicator .right clauseIndex =>
      match clauseIndex.val with
      | 0 => p68
      | 1 => p52
      | _ => []
  | .routedClause => p1104

/-- An atlas entry has the advertised origin, two-block endpoint, and
orthogonality. -/
def RetainedDirectSourcePrefixChoice.Valid
    (choice : RetainedDirectSourcePrefixChoice) : Prop :=
  choice.route.head? = some (0, 0) ∧
    choice.route.getLast? =
      some
        (retainedTerminalFanOuterCoordinatedPrefixVector
          choice.direction) ∧
    OrthogonalPolyline choice.route

instance (choice : RetainedDirectSourcePrefixChoice) :
    Decidable choice.Valid := by
  unfold RetainedDirectSourcePrefixChoice.Valid
  infer_instance

/-- Every finite atlas entry is a valid relative coordinated prefix. -/
theorem retainedDirectSourcePrefixChoices_valid :
    ∀ kind : RetainedDirectClauseKind,
      ∀ choice ∈ retainedDirectSourcePrefixChoices kind,
        choice.Valid := by
  native_decide

/-- Turn a checked atlas entry into the generic coordinated-prefix
certificate. -/
def RetainedDirectSourcePrefixChoice.certificate
    (choice : RetainedDirectSourcePrefixChoice)
    (valid : choice.Valid) :
    RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
      choice.direction where
  route := choice.route
  head_eq := valid.1
  last_eq := valid.2.1
  orthogonal := valid.2.2

/-- The relative 64-block escape obtained from one atlas choice. -/
def RetainedDirectSourcePrefixChoice.sourceEscapeRoute
    (choice : RetainedDirectSourcePrefixChoice) : List Cell :=
  joinAtEndpoint choice.route
    ((retainedTerminalFanOuterPostCoordinatedPrefixRay
      choice.direction).rasterize
        (retainedTerminalFanOuterCoordinatedPrefixVector
          choice.direction))

/-- Within every direct clause, the selected 64-block escapes are
continuously separated and can meet only at their common head. -/
def RetainedDirectClauseKind.SourceEscapesSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (firstIndex secondIndex :
    Fin (retainedDirectSourcePrefixChoices kind).length),
    firstIndex ≠ secondIndex →
      RoutesAvoidEachOther
        ((retainedDirectSourcePrefixChoices kind).get
          firstIndex).sourceEscapeRoute
        ((retainedDirectSourcePrefixChoices kind).get
          secondIndex).sourceEscapeRoute ∧
      RoutesMeetOnlyAtHeads
        ((retainedDirectSourcePrefixChoices kind).get
          firstIndex).sourceEscapeRoute
        ((retainedDirectSourcePrefixChoices kind).get
          secondIndex).sourceEscapeRoute

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceEscapesSeparated := by
  unfold RetainedDirectClauseKind.SourceEscapesSeparated
  let firstDecidable :
      ∀ firstIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            firstIndex ≠ secondIndex →
              RoutesAvoidEachOther
                ((retainedDirectSourcePrefixChoices kind).get
                  firstIndex).sourceEscapeRoute
                ((retainedDirectSourcePrefixChoices kind).get
                  secondIndex).sourceEscapeRoute ∧
              RoutesMeetOnlyAtHeads
                ((retainedDirectSourcePrefixChoices kind).get
                  firstIndex).sourceEscapeRoute
                ((retainedDirectSourcePrefixChoices kind).get
                  secondIndex).sourceEscapeRoute) :=
    fun firstIndex => by
      letI :
          ∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            Decidable
              (firstIndex ≠ secondIndex →
                RoutesAvoidEachOther
                  ((retainedDirectSourcePrefixChoices kind).get
                    firstIndex).sourceEscapeRoute
                  ((retainedDirectSourcePrefixChoices kind).get
                    secondIndex).sourceEscapeRoute ∧
              RoutesMeetOnlyAtHeads
                ((retainedDirectSourcePrefixChoices kind).get
                  firstIndex).sourceEscapeRoute
                ((retainedDirectSourcePrefixChoices kind).get
                  secondIndex).sourceEscapeRoute) :=
        fun secondIndex => by
          let firstRoute :=
            ((retainedDirectSourcePrefixChoices kind).get
              firstIndex).sourceEscapeRoute
          let secondRoute :=
            ((retainedDirectSourcePrefixChoices kind).get
              secondIndex).sourceEscapeRoute
          change
            Decidable
              (firstIndex ≠ secondIndex →
                RoutesAvoidEachOther firstRoute secondRoute ∧
                  RoutesMeetOnlyAtHeads firstRoute secondRoute)
          letI : Decidable
              (RoutesAvoidEachOther firstRoute secondRoute) :=
            inferInstance
          letI : Decidable
              (RoutesMeetOnlyAtHeads firstRoute secondRoute) :=
            inferInstance
          infer_instance
      exact Fintype.decidableForallFintype
  letI := firstDecidable
  exact Fintype.decidableForallFintype

theorem retainedDirectSourcePrefixChoices_sourceEscapes_separated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceEscapesSeparated := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
