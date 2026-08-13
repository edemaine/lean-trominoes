/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-!
# Certified eight-port occurrence-splitting ring

Figure 7 replaces an unsplit variable whose incident rays occupy the eight
multiples of 45 degrees by a clockwise ring of occurrence copies.  Each copy
keeps one old incidence and receives the two neighboring implication
incidences, so its degree is three.

The semantic occurrence order consumed later by the 3DM construction is
linear, whereas the implication ring is cyclic.  We therefore insert one
degree-two separator copy between the northeast and east source ports.  It
is the unique cut in the implication-clause presentation: at every real
port, the copied source incidence is followed by the incoming and then
outgoing ring incidences.  In the drawing's axis convention these three
terminal directions are clockwise.  This remains a constant-size version
of Figure 7 and works even when all eight source ports are occupied.

This file records the resulting worst-case local geometry explicitly.
Diagonal old rays enter the corner copies through an L-shaped orthogonal
route outside the implication ring.  The 26 incidence routes form a finite
continuously planar orthogonal drawing, certified by computation.
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

/-- Vertices of the implication cycle: eight source ports and one
degree-two separator. -/
inductive RingVertex
  | separator
  | port (value : Port)
  deriving DecidableEq, Repr

/-- Clockwise implication-cycle order, cut at the separator. -/
def cycleVertices : List RingVertex :=
  [.separator, .port .east, .port .southeast, .port .south,
    .port .southwest, .port .west, .port .northwest,
    .port .north, .port .northeast]

/-- Clockwise successor in the nine-copy implication cycle. -/
def RingVertex.next : RingVertex → RingVertex
  | .separator => .port .east
  | .port .east => .port .southeast
  | .port .southeast => .port .south
  | .port .south => .port .southwest
  | .port .southwest => .port .west
  | .port .west => .port .northwest
  | .port .northwest => .port .north
  | .port .north => .port .northeast
  | .port .northeast => .separator

/-- Clause presentation follows the directed cycle from its separator cut.
Thus the incoming implication is encountered before the outgoing one at
every real port; only the degree-two separator straddles the list boundary. -/
def presentedCycleVertices : List RingVertex :=
  cycleVertices

/-- Occurrence-copy positions on the boundary of the inner square, after a
factor-two refinement that makes room for the separator. -/
def variablePosition : Port → Cell
  | .northwest => (6, 6)
  | .north => (12, 6)
  | .northeast => (18, 6)
  | .east => (18, 12)
  | .southeast => (18, 18)
  | .south => (12, 18)
  | .southwest => (6, 18)
  | .west => (6, 12)

/-- The separator lies halfway along the northeast-to-east side. -/
def separatorPosition : Cell := (18, 9)

/-- Position of every implication-cycle copy. -/
def ringVariablePosition : RingVertex → Cell
  | .separator => separatorPosition
  | .port port => variablePosition port

/-- Clause-side ports of the eight old incidences. -/
def spokeClausePosition : Port → Cell
  | .northwest => (0, 0)
  | .north => (12, 0)
  | .northeast => (24, 0)
  | .east => (24, 12)
  | .southeast => (24, 24)
  | .south => (12, 24)
  | .southwest => (0, 24)
  | .west => (0, 12)

/-- Implication-clause positions in the nine gaps of the inner ring. -/
def cycleClausePosition : RingVertex → Cell
  | .separator => (18, 10)
  | .port .east => (18, 16)
  | .port .southeast => (16, 18)
  | .port .south => (8, 18)
  | .port .southwest => (6, 16)
  | .port .west => (6, 8)
  | .port .northwest => (8, 6)
  | .port .north => (16, 6)
  | .port .northeast => (18, 8)

/-- No implication-clause vertex of the local ring occupies a ring-variable
vertex, including the separator copy. -/
theorem cycleClausePosition_ne_ringVariablePosition :
    ∀ clauseVertex variableVertex : RingVertex,
      cycleClausePosition clauseVertex ≠
        ringVariablePosition variableVertex := by
  intro clauseVertex variableVertex
  cases clauseVertex <;> cases variableVertex
  · native_decide
  · rename_i variablePort
    cases variablePort <;> native_decide
  · rename_i clausePort
    cases clausePort <;> native_decide
  · rename_i clausePort variablePort
    cases clausePort <;> cases variablePort <;> native_decide

/-- One retained old incidence, represented locally as a unary port clause. -/
def spokeClause (port : Port) : EmbeddedClause RingVertex where
  position := spokeClausePosition port
  literals := [(.port port, true)]

/-- The implication from one clockwise occurrence copy to the next. -/
def cycleClause (vertex : RingVertex) : EmbeddedClause RingVertex where
  position := cycleClausePosition vertex
  literals := [(vertex, false), (vertex.next, true)]

/-- Separator-cut presentation of the nine implication clauses. -/
def cycleFormula : List (EmbeddedClause RingVertex) :=
  presentedCycleVertices.map cycleClause

/-- Eight old incidences followed by the nine implication clauses. -/
def formula : List (EmbeddedClause RingVertex) :=
  ports.map spokeClause ++ cycleFormula

/-- Orthogonalized old rays.  Corner rays bend outside the implication
square, so they cannot enter its interior. -/
def spokeRoute : Port → List Cell
  | .northwest => [(0, 0), (0, 6), (6, 6)]
  | .north => [(12, 0), (12, 6)]
  | .northeast => [(24, 0), (24, 6), (18, 6)]
  | .east => [(24, 12), (18, 12)]
  | .southeast => [(24, 24), (24, 18), (18, 18)]
  | .south => [(12, 24), (12, 18)]
  | .southwest => [(0, 24), (0, 18), (6, 18)]
  | .west => [(0, 12), (6, 12)]

/-- The two direct sides of one local implication clause. -/
def cycleRoute
    (vertex : RingVertex) (literalIndex : Nat) : List Cell :=
  match literalIndex with
  | 0 => [cycleClausePosition vertex, ringVariablePosition vertex]
  | 1 => [cycleClausePosition vertex, ringVariablePosition vertex.next]
  | _ => []

/-- Presentation-indexed routes for the standalone implication cycle. -/
def cycleRoutes (clauseIndex literalIndex : Nat) : List Cell :=
  if clauseIndex < presentedCycleVertices.length then
    cycleRoute
      (presentedCycleVertices.getD clauseIndex .separator)
      literalIndex
  else
    []

/-- Total presentation-indexed route family for the local formula. -/
def routes (clauseIndex literalIndex : Nat) : List Cell :=
  if clauseIndex < ports.length then
    if literalIndex = 0 then
      spokeRoute (ports.getD clauseIndex .northwest)
    else
      []
  else if clauseIndex < ports.length + cycleFormula.length then
    cycleRoutes (clauseIndex - ports.length) literalIndex
  else
    []

/-- Complete finite occurrence-splitting neighborhood. -/
def drawing : EmbeddedCNFIncidenceDrawing RingVertex where
  formula := formula
  variablePosition := ringVariablePosition
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
