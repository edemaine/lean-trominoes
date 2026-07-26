import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-!
# Certified degree-eight occurrence-splitting ring

Figure 7 replaces an unsplit variable whose incident rays occupy the eight
multiples of 45 degrees by a clockwise ring of occurrence copies.  Each copy
keeps one old incidence and receives the two neighboring implication
incidences, so its degree is three.

This file records the worst-case local geometry explicitly.  Diagonal old
rays enter the corner copies through an L-shaped orthogonal route outside
the implication ring.  The resulting 24 incidence routes form a finite
continuously planar orthogonal drawing, certified by computation.  Smaller
variable neighborhoods will be obtained by deleting unused spoke/copy
positions and contracting the corresponding ring gaps.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT

/-- The eight possible terminal-ray directions in clockwise order. -/
inductive Port
  | northwest
  | north
  | northeast
  | east
  | southeast
  | south
  | southwest
  | west
  deriving DecidableEq, Repr

/-- Clockwise presentation order used both by the geometric rotation system
and by the implication cycle. -/
def ports : List Port :=
  [.northwest, .north, .northeast, .east,
    .southeast, .south, .southwest, .west]

/-- Clockwise successor, closing the ring at the northwest copy. -/
def Port.next : Port → Port
  | .northwest => .north
  | .north => .northeast
  | .northeast => .east
  | .east => .southeast
  | .southeast => .south
  | .south => .southwest
  | .southwest => .west
  | .west => .northwest

/-- Occurrence-copy positions on the boundary of the inner square. -/
def variablePosition : Port → Cell
  | .northwest => (3, 3)
  | .north => (6, 3)
  | .northeast => (9, 3)
  | .east => (9, 6)
  | .southeast => (9, 9)
  | .south => (6, 9)
  | .southwest => (3, 9)
  | .west => (3, 6)

/-- Clause-side ports of the eight old incidences. -/
def spokeClausePosition : Port → Cell
  | .northwest => (0, 0)
  | .north => (6, 0)
  | .northeast => (12, 0)
  | .east => (12, 6)
  | .southeast => (12, 12)
  | .south => (6, 12)
  | .southwest => (0, 12)
  | .west => (0, 6)

/-- Implication-clause positions in the eight gaps of the inner ring. -/
def cycleClausePosition : Port → Cell
  | .northwest => (4, 3)
  | .north => (8, 3)
  | .northeast => (9, 4)
  | .east => (9, 8)
  | .southeast => (8, 9)
  | .south => (4, 9)
  | .southwest => (3, 8)
  | .west => (3, 4)

/-- One retained old incidence, represented locally as a unary port clause. -/
def spokeClause (port : Port) : EmbeddedClause Port where
  position := spokeClausePosition port
  literals := [(port, true)]

/-- The implication from one clockwise occurrence copy to the next. -/
def cycleClause (port : Port) : EmbeddedClause Port where
  position := cycleClausePosition port
  literals := [(port, false), (port.next, true)]

/-- Eight old incidences followed by the eight implication clauses. -/
def formula : List (EmbeddedClause Port) :=
  ports.map spokeClause ++ ports.map cycleClause

/-- Orthogonalized old rays.  Corner rays bend outside the implication
square, so they cannot enter its interior. -/
def spokeRoute : Port → List Cell
  | .northwest => [(0, 0), (0, 3), (3, 3)]
  | .north => [(6, 0), (6, 3)]
  | .northeast => [(12, 0), (12, 3), (9, 3)]
  | .east => [(12, 6), (9, 6)]
  | .southeast => [(12, 12), (12, 9), (9, 9)]
  | .south => [(6, 12), (6, 9)]
  | .southwest => [(0, 12), (0, 9), (3, 9)]
  | .west => [(0, 6), (3, 6)]

/-- The two direct sides of one local implication clause. -/
def cycleRoute (port : Port) (literalIndex : Nat) : List Cell :=
  match literalIndex with
  | 0 => [cycleClausePosition port, variablePosition port]
  | 1 => [cycleClausePosition port, variablePosition port.next]
  | _ => []

/-- Total presentation-indexed route family for the local formula. -/
def routes (clauseIndex literalIndex : Nat) : List Cell :=
  if clauseIndex < ports.length then
    if literalIndex = 0 then
      spokeRoute (ports.getD clauseIndex .northwest)
    else
      []
  else if clauseIndex < 2 * ports.length then
    cycleRoute
      (ports.getD (clauseIndex - ports.length) .northwest)
      literalIndex
  else
    []

/-- Complete finite occurrence-splitting neighborhood. -/
def drawing : EmbeddedCNFIncidenceDrawing Port where
  formula := formula
  variablePosition := variablePosition
  routes := routes

/-- The degree-eight ring has exact endpoints, orthogonal routes, and exact
continuous planarity. -/
theorem drawing_isValid : drawing.IsValid := by
  native_decide

/-- Endpoint compatibility of the certified local replacement. -/
theorem drawing_routesMatch : drawing.RoutesMatch :=
  drawing_isValid.1

/-- Every local spoke and implication incidence is orthogonal. -/
theorem drawing_isOrthogonal : drawing.IsOrthogonal :=
  drawing_isValid.2.1

/-- The complete local replacement is continuously planar. -/
theorem drawing_isPlanar : drawing.IsPlanar :=
  drawing_isValid.2.2

end OccurrenceSplitRing
end LeanTrominoes
