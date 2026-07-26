import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPorts
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularPorts
import LeanTrominoes.PositionedPeriodicCNFScaling

/-!
# Geometry of the eight terminal-ray ports

The routed planar-SAT formulas use only the two axes and the two 45-degree
diagonals.  This file replaces the executable nested classifier by a compact
geometric characterization and records its behavior under positive integral
scaling.

It also numbers the ports in the east-first order used by
`terminalVectorAngleLE` and the positioned fixed-eight split:

`east, southeast, south, southwest, west, northwest, north, northeast`.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

/-- East-first cyclic rank of a compass port. -/
def Port.angularRank : Port → Nat
  | .east => 0
  | .southeast => 1
  | .south => 2
  | .southwest => 3
  | .west => 4
  | .northwest => 5
  | .north => 6
  | .northeast => 7

@[simp]
theorem Port.angularRank_lt_eight (port : Port) :
    port.angularRank < 8 := by
  cases port <;> decide

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Looking up the east-first slot at a port's cyclic rank recovers the
port. -/
@[simp]
theorem angularPortOfIndex_angularRank (port : Port) :
    angularPortOfIndex port.angularRank = port := by
  cases port <;> rfl

/-- Every in-range east-first slot has its own index as cyclic rank. -/
theorem angularRank_angularPortOfIndex
    {index : Nat} (belowEight : index < 8) :
    (angularPortOfIndex index).angularRank = index := by
  interval_cases index <;> rfl

/-- A vector lies on one of the eight permitted nonzero rays exactly when
it is nonzero and lies on an axis or a 45-degree diagonal. -/
theorem terminalPort_isSome_iff (vector : Cell) :
    (terminalPort vector).isSome ↔
      vector ≠ (0, 0) ∧
        (vector.1 = 0 ∨ vector.2 = 0 ∨
          vector.1 = vector.2 ∨ vector.1 = -vector.2) := by
  rcases vector with ⟨horizontal, vertical⟩
  unfold terminalPort
  split_ifs <;> simp_all <;> omega

/-- A positive integral scaling changes the length but not the compass ray
of a terminal vector. -/
theorem terminalPort_scale
    {factor : Int} (positive : 0 < factor)
    (vector : Cell) :
    terminalPort (Cell.scale factor vector) =
      terminalPort vector := by
  rcases vector with ⟨horizontal, vertical⟩
  have mulNegative (value : Int) :
      factor * value < 0 ↔ value < 0 := by
    have comparison :
        factor * value < factor * 0 ↔ value < 0 :=
      Int.mul_lt_mul_left positive
    simpa only [mul_zero] using comparison
  have mulPositive (value : Int) :
      0 < factor * value ↔ 0 < value := by
    have comparison :
        factor * 0 < factor * value ↔ 0 < value :=
      Int.mul_lt_mul_left positive
    simpa only [mul_zero] using comparison
  have mulEqNegative (first second : Int) :
      factor * first = -(factor * second) ↔
        first = -second := by
    constructor
    · intro equality
      apply mul_left_cancel₀ positive.ne'
      simpa only [mul_neg] using equality
    · intro equality
      rw [equality, mul_neg]
  simp [terminalPort, Cell.scale, mulNegative,
    mulPositive, mulEqNegative, positive.ne']

/-- Scaling every point of a route scales its final backwards tangent
vector by the same factor. -/
theorem routeTerminalVector_scalePolyline
    (factor : Int) (route : List Cell) :
    routeTerminalVector (scalePolyline factor route) =
      Cell.scale factor (routeTerminalVector route) := by
  unfold routeTerminalVector
  rw [gridPolylineSegments_scalePolyline,
    List.getLast?_map]
  cases (gridPolylineSegments route).getLast? with
  | none =>
      simp [Cell.scale]
  | some segment =>
      simp [GridSegment.scale, Cell.scale, Cell.sub]
      exact ⟨by ring, by ring⟩

/-- Positive route scaling preserves its total compass-port lookup. -/
theorem routeTerminalPort_scaleIncidenceRoutes
    {factor : Nat} (positive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) :
    routeTerminalPort
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
        clauseIndex literalIndex =
    routeTerminalPort routes clauseIndex literalIndex := by
  have positiveInt : (0 : Int) < factor := by
    exact_mod_cast positive
  simp only [routeTerminalPort,
    PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
    routeTerminalVector_scalePolyline]
  rw [terminalPort_scale positiveInt]

/-- Positive route scaling preserves validity of every genuine terminal
ray. -/
theorem TerminalPortCertificate.scaleIncidenceRoutes
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    {factor : Nat} (positive : 0 < factor)
    {routes : PositionedPeriodicCNF.IncidenceRoutes}
    (certificate : TerminalPortCertificate source routes) :
    TerminalPortCertificate source
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) where
  valid := by
    have positiveInt : (0 : Int) < factor := by
      exact_mod_cast positive
    intro tagged taggedMember
    simp only [
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      routeTerminalVector_scalePolyline]
    rw [terminalPort_scale positiveInt]
    exact certificate.valid tagged taggedMember
  separate := by
    intro first firstMember second secondMember atomsEqual portsEqual
    apply certificate.separate
      first firstMember second secondMember atomsEqual
    simpa only [
      routeTerminalPort_scaleIncidenceRoutes positive] using
      portsEqual

end PeriodicEightOccurrenceSplit
end LeanTrominoes
