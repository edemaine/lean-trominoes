import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry

/-!
# Rectilinear staircases for octilinear rays

The retained planar-SAT drawing uses the eight compass directions: the two
axes and the two 45-degree diagonals.  Positive refinement leaves enough
integer-grid room to replace a diagonal ray by alternating horizontal and
vertical unit steps.  This file packages that local rasterization independently
of any particular incidence drawing.

An axis ray remains one segment.  A diagonal ray of integer length `n`
becomes a staircase of `2n` unit segments.  Every rasterized ray has its exact
advertised endpoints and is an orthogonal polyline.
-/

namespace LeanTrominoes

namespace OccurrenceSplitRing

/-- Primitive outward vector of one compass port. -/
def Port.unitVector : Port → Cell
  | .northwest => (-1, -1)
  | .north => (0, -1)
  | .northeast => (1, -1)
  | .east => (1, 0)
  | .southeast => (1, 1)
  | .south => (0, 1)
  | .southwest => (-1, 1)
  | .west => (-1, 0)

@[simp]
theorem Port.unitVector_ne_zero (port : Port) :
    port.unitVector ≠ (0, 0) := by
  cases port <;> decide

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Alternating horizontal-then-vertical unit steps along a diagonal ray. -/
def diagonalStaircase
    (horizontal vertical : Int) : Nat → Cell → List Cell
  | 0, start => [start]
  | length + 1, start =>
      start ::
        Cell.add start (horizontal, 0) ::
          diagonalStaircase horizontal vertical length
            (Cell.add start (horizontal, vertical))

@[simp]
theorem diagonalStaircase_head?
    (horizontal vertical : Int) (length : Nat) (start : Cell) :
    (diagonalStaircase horizontal vertical length start).head? =
      some start := by
  cases length <;> rfl

@[simp]
theorem diagonalStaircase_getLast?
    (horizontal vertical : Int) (length : Nat) (start : Cell) :
    (diagonalStaircase horizontal vertical length start).getLast? =
      some
        (Cell.add start
          (Cell.scale length (horizontal, vertical))) := by
  induction length generalizing start with
  | zero =>
      simp [diagonalStaircase, Cell.add, Cell.scale]
  | succ length induction =>
      rw [diagonalStaircase, List.getLast?_cons_cons,
        List.getLast?_cons, induction]
      simp [Cell.add, Cell.scale]
      constructor <;> ring

/-- Every diagonal staircase is rectilinear, independently of the signs of
its two unit steps. -/
theorem diagonalStaircase_orthogonal
    {horizontal vertical : Int}
    (horizontalNonzero : horizontal ≠ 0)
    (verticalNonzero : vertical ≠ 0)
    (length : Nat) (start : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (diagonalStaircase horizontal vertical length start) := by
  induction length generalizing start with
  | zero =>
      simp [diagonalStaircase,
        PeriodicOrthocrossing.OrthogonalPolyline]
  | succ length induction =>
      simp only [diagonalStaircase,
        PeriodicOrthocrossing.OrthogonalPolyline,
        List.isChain_cons_cons]
      constructor
      · left
        simp [GridSegment.IsHorizontal, Cell.add,
          horizontalNonzero]
      · apply (List.isChain_cons).2
        constructor
        · intro next nextMember
          simp only [diagonalStaircase_head?,
            Option.mem_def, Option.some.injEq] at nextMember
          subst next
          right
          simp [GridSegment.IsVertical, Cell.add,
            verticalNonzero]
        · exact induction _

/-- Rasterize an integer ray in one of the eight compass directions.
Horizontal and vertical rays stay direct; diagonal rays become unit
staircases. -/
def compassRay
    (port : Port) : Nat → Cell → List Cell
  | 0, start => [start]
  | length + 1, start =>
      match port with
      | .northwest =>
          diagonalStaircase (-1) (-1) (length + 1) start
      | .north =>
          [start,
            Cell.add start
              (Cell.scale (length + 1) port.unitVector)]
      | .northeast =>
          diagonalStaircase 1 (-1) (length + 1) start
      | .east =>
          [start,
            Cell.add start
              (Cell.scale (length + 1) port.unitVector)]
      | .southeast =>
          diagonalStaircase 1 1 (length + 1) start
      | .south =>
          [start,
            Cell.add start
              (Cell.scale (length + 1) port.unitVector)]
      | .southwest =>
          diagonalStaircase (-1) 1 (length + 1) start
      | .west =>
          [start,
            Cell.add start
              (Cell.scale (length + 1) port.unitVector)]

@[simp]
theorem compassRay_head?
    (port : Port) (length : Nat) (start : Cell) :
    (compassRay port length start).head? = some start := by
  cases length <;> cases port <;> simp [compassRay]

@[simp]
theorem compassRay_getLast?
    (port : Port) (length : Nat) (start : Cell) :
    (compassRay port length start).getLast? =
      some
        (Cell.add start
          (Cell.scale length port.unitVector)) := by
  cases length <;> cases port <;>
    simp [compassRay, OccurrenceSplitRing.Port.unitVector,
      Cell.add, Cell.scale]

/-- Every compass-ray rasterization is an orthogonal polyline. -/
theorem compassRay_orthogonal
    (port : Port) (length : Nat) (start : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (compassRay port length start) := by
  cases length with
  | zero =>
      simp [compassRay,
        PeriodicOrthocrossing.OrthogonalPolyline]
  | succ length =>
      cases port
      · exact diagonalStaircase_orthogonal
          (by decide) (by decide) (length + 1) start
      · simp only [compassRay,
          PeriodicOrthocrossing.OrthogonalPolyline,
          List.isChain_cons_cons, List.isChain_singleton]
        constructor
        · right
          simp [GridSegment.IsVertical,
            OccurrenceSplitRing.Port.unitVector,
            Cell.add, Cell.scale]
          omega
        · trivial
      · exact diagonalStaircase_orthogonal
          (by decide) (by decide) (length + 1) start
      · simp only [compassRay,
          PeriodicOrthocrossing.OrthogonalPolyline,
          List.isChain_cons_cons, List.isChain_singleton]
        constructor
        · left
          simp [GridSegment.IsHorizontal,
            OccurrenceSplitRing.Port.unitVector,
            Cell.add, Cell.scale]
          omega
        · trivial
      · exact diagonalStaircase_orthogonal
          (by decide) (by decide) (length + 1) start
      · simp only [compassRay,
          PeriodicOrthocrossing.OrthogonalPolyline,
          List.isChain_cons_cons, List.isChain_singleton]
        constructor
        · right
          simp [GridSegment.IsVertical,
            OccurrenceSplitRing.Port.unitVector,
            Cell.add, Cell.scale]
          omega
        · trivial
      · exact diagonalStaircase_orthogonal
          (by decide) (by decide) (length + 1) start
      · simp only [compassRay,
          PeriodicOrthocrossing.OrthogonalPolyline,
          List.isChain_cons_cons, List.isChain_singleton]
        constructor
        · left
          simp [GridSegment.IsHorizontal,
            OccurrenceSplitRing.Port.unitVector,
            Cell.add, Cell.scale]
          omega
        · trivial

/-- The primitive vector of a port is classified as that same port. -/
@[simp]
theorem terminalPort_unitVector (port : Port) :
    terminalPort port.unitVector = some port := by
  cases port <;>
    rfl

/-- Positive integer multiples retain their compass classification. -/
theorem terminalPort_scale_unitVector
    (port : Port) {length : Int} (positive : 0 < length) :
    terminalPort (Cell.scale length port.unitVector) =
      some port := by
  rw [terminalPort_scale positive, terminalPort_unitVector]

/-- Integer distance along the nonzero coordinate used by one compass ray. -/
def compassLength (port : Port) (vector : Cell) : Nat :=
  match port with
  | .northwest => (-vector.1).toNat
  | .north => (-vector.2).toNat
  | .northeast | .east | .southeast => vector.1.toNat
  | .south => vector.2.toNat
  | .southwest | .west => (-vector.1).toNat

/-- Successful compass classification decomposes the vector into a positive
integer multiple of that port's primitive vector. -/
theorem compassLength_pos_and_scale
    {vector : Cell} {port : Port}
    (classified : terminalPort vector = some port) :
    0 < compassLength port vector ∧
      vector =
        Cell.scale (compassLength port vector) port.unitVector := by
  rcases vector with ⟨horizontal, vertical⟩
  cases port <;>
    unfold terminalPort at classified <;>
    split_ifs at classified <;>
    simp_all [compassLength,
      OccurrenceSplitRing.Port.unitVector, Cell.scale] <;>
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
