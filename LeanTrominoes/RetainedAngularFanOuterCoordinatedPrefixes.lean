import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Clause-coordinated prefixes for retained outer fan escapes

Direct incidences at one clause share their source gate.  Their first few
grid steps therefore have to be selected as a family, before the routes can
return to the direction-canonical retained-ray raster.

This layer isolates exactly that finite choice.  A relative certificate
supplies an orthogonal route through the first two primitive blocks.  The
generic construction translates it to the source gate, appends the remaining
62 canonical blocks of the fixed source escape, and packages the result as
the 64-block escape certificate consumed by the complete outer-fan route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Number of primitive blocks whose rasterization is selected jointly at a
direct clause.  Exhaustive search over the direct clause profiles shows that
two blocks suffice; the finite tables live in the next layer. -/
def retainedTerminalFanOuterCoordinatedPrefixLength : Nat := 2

/-- The direction-canonical remainder of the 64-block source escape after
the clause-coordinated prefix. -/
def retainedTerminalFanOuterPostCoordinatedPrefixRay
    (direction : RetainedTerminalDirection) : RetainedRay :=
  retainedTerminalFanOuterInwardRayOfLength direction
    (retainedTerminalFanOuterSourceEscapeLength -
      retainedTerminalFanOuterCoordinatedPrefixLength)

/-- Displacement of the two-block checkpoint selected by a coordinated
prefix. -/
def retainedTerminalFanOuterCoordinatedPrefixVector
    (direction : RetainedTerminalDirection) : Cell :=
  (retainedTerminalFanOuterInwardRayOfLength direction
    retainedTerminalFanOuterCoordinatedPrefixLength).vector

/-- The two-block prefix and the remaining canonical raster have exactly the
same total displacement as the original 64-block source escape. -/
theorem retainedTerminalFanOuterCoordinatedPrefix_vectors_add
    (direction : RetainedTerminalDirection) :
    Cell.add
        (retainedTerminalFanOuterCoordinatedPrefixVector direction)
        (retainedTerminalFanOuterPostCoordinatedPrefixRay direction).vector =
      (retainedTerminalFanOuterInwardRayOfLength direction
        retainedTerminalFanOuterSourceEscapeLength).vector := by
  cases direction with
  | compass port =>
      cases port <;>
        native_decide
  | routedClause arm =>
      cases arm <;>
        native_decide

/-- A finite route at the origin through the first two primitive blocks of
one terminal direction.  Different incidences at a clause choose these
certificates jointly. -/
structure RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
    (direction : RetainedTerminalDirection) where
  route : List Cell
  head_eq : route.head? = some (0, 0)
  last_eq :
    route.getLast? =
      some
        (retainedTerminalFanOuterCoordinatedPrefixVector direction)
  orthogonal : OrthogonalPolyline route

/-- The positioned two-block checkpoint, measured from the exact source
gate of an incidence. -/
def retainedTerminalFanOuterCoordinatedPrefixPoint
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : Cell :=
  Cell.add
    (retainedAngularFanOuterDemand center terminal slot).gate
    (retainedTerminalFanOuterCoordinatedPrefixVector terminal.1)

/-- Translate a relative clause-coordinated prefix to its incidence's exact
source gate. -/
def retainedTerminalFanOuterPositionedCoordinatedPrefixRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) : List Cell :=
  translatePolyline
    (retainedAngularFanOuterDemand center terminal slot).gate
    coordinated.route

@[simp]
theorem retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute
      center terminal slot coordinated).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  simp [retainedTerminalFanOuterPositionedCoordinatedPrefixRoute,
    translatePolyline, coordinated.head_eq, Cell.add]

@[simp]
theorem retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute
      center terminal slot coordinated).getLast? =
        some
          (retainedTerminalFanOuterCoordinatedPrefixPoint
            center terminal slot) := by
  simp [retainedTerminalFanOuterPositionedCoordinatedPrefixRoute,
    retainedTerminalFanOuterCoordinatedPrefixPoint,
    translatePolyline, coordinated.last_eq]

/-- Translation preserves the certified orthogonality of a coordinated
prefix. -/
theorem retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    OrthogonalPolyline
      (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute
        center terminal slot coordinated) := by
  exact coordinated.orthogonal.translate
    (retainedAngularFanOuterDemand center terminal slot).gate

/-- Complete 64-block source escape obtained by appending 62 canonical
blocks to a clause-coordinated two-block prefix. -/
def retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute
      center terminal slot coordinated)
    ((retainedTerminalFanOuterPostCoordinatedPrefixRay
      terminal.1).rasterize
        (retainedTerminalFanOuterCoordinatedPrefixPoint
          center terminal slot))

/-- Appending the canonical suffix reaches the original 64-block source
escape point exactly. -/
@[simp]
theorem
    retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    (retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix
      center terminal slot coordinated).getLast? =
        some
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot) := by
  apply joinAtEndpoint_getLast?
    (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_getLast?
      center terminal slot coordinated)
    (RetainedRay.rasterize_head? _ _)
  rw [RetainedRay.rasterize_getLast?]
  apply congrArg some
  have vectors :=
    retainedTerminalFanOuterCoordinatedPrefix_vectors_add
      terminal.1
  have horizontal := congrArg Prod.fst vectors
  have vertical := congrArg Prod.snd vectors
  unfold retainedTerminalFanOuterCoordinatedPrefixPoint
    retainedTerminalFanOuterSourceEscapePoint
    retainedTerminalFanOuterSourceEscapeRay
  simp only [Cell.add] at horizontal vertical ⊢
  apply Prod.ext <;> omega

/-- The completed 64-block source escape remains orthogonal. -/
theorem
    retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    OrthogonalPolyline
      (retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix
        center terminal slot coordinated) := by
  exact
    (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_orthogonal
      center terminal slot coordinated).joinAtEndpoint
      (RetainedRay.rasterize_orthogonal _ _)
      (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_getLast?
        center terminal slot coordinated)
      (RetainedRay.rasterize_head? _ _)

/-- Package a coordinated two-block prefix as the clause-level 64-block
escape certificate accepted by the complete escaped outer-fan route. -/
def retainedTerminalFanOuterSourceEscapeCertificateOfCoordinatedPrefix
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (coordinated :
      RetainedTerminalFanOuterRelativeCoordinatedPrefixCertificate
        terminal.1) :
    RetainedTerminalFanOuterSourceEscapeCertificate
      center terminal slot where
  route :=
    retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix
      center terminal slot coordinated
  head_eq := by
    unfold retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix
    exact joinAtEndpoint_head?
      (retainedTerminalFanOuterPositionedCoordinatedPrefixRoute_head?
        center terminal slot coordinated)
  last_eq :=
    retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix_getLast?
      center terminal slot coordinated
  orthogonal :=
    retainedTerminalFanOuterSourceEscapeRouteOfCoordinatedPrefix_orthogonal
      center terminal slot coordinated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
