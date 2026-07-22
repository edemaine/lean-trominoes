import LeanTrominoes.Computability
import LeanTrominoes.FiniteSearch
import LeanWang.Basic

/-!
# Computable finite tromino search

List presentations of the finite boxes, candidate placements, and assignment
states used by the finite-obstruction characterization. These presentations
are designed both for execution and for primitive-recursion proofs.
-/

namespace LeanTrominoes
namespace TrominoAssignment

/-- The integers from `-radius` through `radius`, in increasing order. -/
def centeredIntegerList (radius : Nat) : List Int :=
  (List.range (2 * radius + 1)).map fun (index : Nat) =>
    (index : Int) - (radius : Int)

theorem mem_centeredIntegerList_iff (radius : Nat) (coordinate : Int) :
    coordinate ∈ centeredIntegerList radius ↔
      -(radius : Int) ≤ coordinate ∧ coordinate ≤ (radius : Int) := by
  simp only [centeredIntegerList, List.mem_map]
  constructor
  · rintro ⟨index, index_lt, rfl⟩
    norm_num [Nat.cast_add, Nat.cast_mul] at *
    omega
  · rintro ⟨lower, upper⟩
    refine ⟨Int.toNat (coordinate + radius), ?_, ?_⟩
    · have nonnegative : 0 ≤ coordinate + (radius : Int) := by omega
      have toNat_eq :
          (Int.toNat (coordinate + radius) : Int) = coordinate + radius :=
        Int.toNat_of_nonneg nonnegative
      have integerBound :
          (Int.toNat (coordinate + radius) : Int) <
            (2 * radius + 1 : Nat) := by
        rw [toNat_eq]
        norm_num [Nat.cast_add, Nat.cast_mul]
        omega
      exact List.mem_range.mpr (by exact_mod_cast integerBound)
    · have nonnegative : 0 ≤ coordinate + (radius : Int) := by omega
      have toNat_eq :
          (Int.toNat (coordinate + radius) : Int) = coordinate + radius :=
        Int.toNat_of_nonneg nonnegative
      calc
        (Int.toNat (coordinate + radius) : Int) - radius =
            (coordinate + radius) - radius := by rw [toNat_eq]
        _ = coordinate := by ring

/-- List presentation of the centered integer box. -/
def boxCellList (radius : Nat) : List Cell :=
  (centeredIntegerList radius).flatMap fun x =>
    (centeredIntegerList radius).map fun y => (x, y)

theorem mem_boxCellList_iff (radius : Nat) (cell : Cell) :
    cell ∈ boxCellList radius ↔ LeanWang.InBox radius cell := by
  rcases cell with ⟨x, y⟩
  simp only [boxCellList, List.mem_flatMap, List.mem_map,
    mem_centeredIntegerList_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨x', ⟨xLower, xUpper⟩, y', ⟨yLower, yUpper⟩,
      ⟨rfl, rfl⟩⟩
    exact ⟨xLower, xUpper, yLower, yUpper⟩
  · rintro ⟨xLower, xUpper, yLower, yUpper⟩
    exact ⟨x, ⟨xLower, xUpper⟩, y, ⟨yLower, yUpper⟩,
      ⟨rfl, rfl⟩⟩

theorem boxCellList_nodup (radius : Nat) :
    (boxCellList radius).Nodup := by
  have integerNodup : (centeredIntegerList radius).Nodup := by
    unfold centeredIntegerList
    have injective : Function.Injective fun index : Nat =>
        (index : Int) - (radius : Int) := by
      intro first second equality
      exact Int.ofNat_injective ((Int.sub_left_inj _).mp equality)
    change (List.map (fun index : Nat =>
      (index : Int) - (radius : Int)) (List.range (2 * radius + 1))).Nodup
    exact List.Nodup.map injective List.nodup_range
  unfold boxCellList
  exact integerNodup.product integerNodup

/-- Explicit enumeration of all square-grid symmetries. -/
def squareSymmetryList : List SquareSymmetry :=
  [.identity, .rotate90, .rotate180, .rotate270,
    .reflectX, .reflectDiagonal, .reflectY, .reflectAntidiagonal]

@[simp]
theorem mem_squareSymmetryList (symmetry : SquareSymmetry) :
    symmetry ∈ squareSymmetryList := by
  cases symmetry <;> simp [squareSymmetryList]

theorem squareSymmetryList_nodup : squareSymmetryList.Nodup := by
  decide

/-- Explicit canonical cell list for each tromino. -/
def trominoCellList : Tromino → List Cell
  | .I => [(0, 0), (1, 0), (2, 0)]
  | .L => [(0, 0), (1, 0), (0, 1)]

theorem mem_trominoCellList_iff (tromino : Tromino) (cell : Cell) :
    cell ∈ trominoCellList tromino ↔ cell ∈ tromino.cells := by
  cases tromino <;> simp [trominoCellList, Tromino.cells]

theorem trominoCellList_nodup (tromino : Tromino) :
    (trominoCellList tromino).Nodup := by
  cases tromino <;> decide

/-- List of all placements that can cover a fixed target cell. -/
def coveringPlacementList (tromino : Tromino) (cell : Cell) :
    List (Placement Unit) :=
  (squareSymmetryList.product (trominoCellList tromino)).map fun candidate =>
    { kind := ()
      symmetry := candidate.1
      offset := Cell.sub cell (candidate.1.act candidate.2) }

theorem mem_coveringPlacementList_iff (tromino : Tromino) (cell : Cell)
    (placement : Placement Unit) :
    placement ∈ coveringPlacementList tromino cell ↔
      placement ∈ coveringPlacements tromino cell := by
  rw [mem_coveringPlacements_iff]
  constructor
  · simp only [coveringPlacementList, List.mem_map]
    rintro ⟨candidate, candidate_mem, rfl⟩
    rcases candidate with ⟨symmetry, source⟩
    have source_mem : source ∈ trominoCellList tromino := by
      simpa using candidate_mem
    rw [Placement.mem_cells_iff]
    refine ⟨source, (mem_trominoCellList_iff tromino source).mp source_mem, ?_⟩
    simp [Cell.add, Cell.sub]
  · intro covers
    rw [Placement.mem_cells_iff] at covers
    obtain ⟨source, source_mem, equality⟩ := covers
    simp only [coveringPlacementList, List.mem_map]
    refine ⟨⟨placement.symmetry, source⟩,
      ?_, ?_⟩
    · simp [(mem_trominoCellList_iff tromino source).mpr source_mem]
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · rfl
    · apply Prod.ext
      · have xEquality := congrArg Prod.fst equality
        simp only [Cell.add] at xEquality
        simp only [Cell.sub]
        rw [← xEquality]
        ring
      · have yEquality := congrArg Prod.snd equality
        simp only [Cell.add] at yEquality
        simp only [Cell.sub]
        rw [← yEquality]
        ring

theorem coveringPlacementList_nodup (tromino : Tromino) (cell : Cell) :
    (coveringPlacementList tromino cell).Nodup := by
  unfold coveringPlacementList
  apply List.Nodup.map
  · rintro ⟨firstSymmetry, firstSource⟩ ⟨secondSymmetry, secondSource⟩
      equality
    have symmetryEquality : firstSymmetry = secondSymmetry :=
      congrArg Placement.symmetry equality
    subst secondSymmetry
    have offsetEquality := congrArg Placement.offset equality
    have actionEquality :
        firstSymmetry.act firstSource = firstSymmetry.act secondSource := by
      apply Prod.ext
      · exact (Int.sub_right_inj cell.1).mp
          (congrArg Prod.fst offsetEquality)
      · exact (Int.sub_right_inj cell.2).mp
          (congrArg Prod.snd offsetEquality)
    exact Prod.ext rfl (firstSymmetry.act_injective actionEquality)
  · exact squareSymmetryList_nodup.product (trominoCellList_nodup tromino)

/-- List of every offset inspected by the radius-`radius` box constraints.
Duplicates are harmless: all occurrences of an offset read the same state. -/
def inspectedOffsetList (tromino : Tromino) (radius : Nat) : List Cell :=
  boxCellList radius ++ (boxCellList radius).flatMap fun cell =>
    (coveringPlacementList tromino cell).map Placement.offset

theorem mem_inspectedOffsetList_iff (tromino : Tromino) (radius : Nat)
    (offset : Cell) :
    offset ∈ inspectedOffsetList tromino radius ↔
      offset ∈ inspectedOffsets tromino radius := by
  simp only [inspectedOffsetList, List.mem_append, List.mem_flatMap,
    List.mem_map, inspectedOffsets, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, mem_boxCells_iff]
  constructor
  · rintro (inBox | ⟨cell, cellInBox, placement, placementInList, rfl⟩)
    · exact Or.inl ((mem_boxCellList_iff radius offset).mp inBox)
    · exact Or.inr ⟨cell, (mem_boxCellList_iff radius cell).mp cellInBox,
        placement,
        (mem_coveringPlacementList_iff tromino cell placement).mp
          placementInList, rfl⟩
  · rintro (inBox | ⟨cell, cellInBox, placement, placementCandidate, rfl⟩)
    · exact Or.inl ((mem_boxCellList_iff radius offset).mpr inBox)
    · exact Or.inr ⟨cell, (mem_boxCellList_iff radius cell).mpr cellInBox,
        placement,
        (mem_coveringPlacementList_iff tromino cell placement).mpr
          placementCandidate, rfl⟩

/-- The nine possible states at an assignment offset. -/
def assignmentStateList : List (Option SquareSymmetry) :=
  none :: squareSymmetryList.map some

@[simp]
theorem mem_assignmentStateList (state : Option SquareSymmetry) :
    state ∈ assignmentStateList := by
  cases state <;> simp [assignmentStateList]

/-- Associate every listed offset with the state stored at its first
occurrence. -/
def assignmentGraph (offsets : List Cell)
    (states : List (Option SquareSymmetry)) :
    List (Cell × Option SquareSymmetry) :=
  offsets.map fun offset =>
    (offset, states.getD (offsets.idxOf offset) none)

/-- Global assignment represented by a finite state word. Unlisted offsets
have state `none`. -/
def listAssignment (offsets : List Cell)
    (states : List (Option SquareSymmetry)) : TrominoAssignment :=
  fun offset => ((assignmentGraph offsets states).lookup offset).getD none

theorem listAssignment_eq_getD_of_mem {offsets : List Cell}
    {states : List (Option SquareSymmetry)} {offset : Cell}
    (member : offset ∈ offsets) :
    listAssignment offsets states offset =
      states.getD (offsets.idxOf offset) none := by
  simp [listAssignment, assignmentGraph, List.lookup_graph _ member]

theorem listAssignment_eq_none_of_not_mem {offsets : List Cell}
    {states : List (Option SquareSymmetry)} {offset : Cell}
    (notMember : offset ∉ offsets) :
    listAssignment offsets states offset = none := by
  have lookupNone : (assignmentGraph offsets states).lookup offset = none := by
    rw [List.lookup_eq_none_iff]
    intro pair pairMember
    have pairKeyMember : pair.1 ∈ offsets := by
      rw [assignmentGraph] at pairMember
      rcases List.mem_map.mp pairMember with
        ⟨listed, listedMember, pairEquality⟩
      subst pair
      exact listedMember
    have keyNotEqual : offset ≠ pair.1 := by
      intro equality
      apply notMember
      simpa [equality] using pairKeyMember
    simp [keyNotEqual]
  rw [listAssignment, lookupNone]
  rfl

end TrominoAssignment
end LeanTrominoes
