/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.FiniteSearch
import LeanWang.Basic
import LeanWang.CoRE

/-!
# Computable finite tromino search

List presentations of the finite boxes, candidate placements, and assignment
states used by the finite-obstruction characterization. These presentations
are designed both for execution and for primitive-recursion proofs.
-/

namespace LeanTrominoes
namespace TrominoAssignment

open LeanTrominoes.Computability

/-- Product representation used to encode unit-kind placements. -/
def placementUnitEquiv : Placement Unit ≃ Unit × SquareSymmetry × Cell where
  toFun placement := (placement.kind, placement.symmetry, placement.offset)
  invFun data :=
    { kind := data.1
      symmetry := data.2.1
      offset := data.2.2 }
  left_inv placement := by cases placement; rfl
  right_inv data := by rcases data with ⟨kind, symmetry, offset⟩; rfl

noncomputable instance : Primcodable (Placement Unit) :=
  Primcodable.ofEquiv (Unit × SquareSymmetry × Cell) placementUnitEquiv

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
def firstIndex (offsets : List Cell) (offset : Cell) : Nat :=
  offsets.findIdx fun candidate => decide (candidate = offset)

theorem firstIndex_eq_idxOf (offsets : List Cell) (offset : Cell) :
    firstIndex offsets offset = offsets.idxOf offset := by
  induction offsets with
  | nil => rfl
  | cons head tail induction =>
      rw [firstIndex]
      simp only [List.findIdx_cons, List.idxOf_cons]
      by_cases equality : head = offset
      · subst head
        simp
      · have decisionFalse : decide (head = offset) = false := by
          simp [equality]
        have beqFalse : (head == offset) = false := by
          simp [equality]
        rw [decisionFalse, beqFalse]
        exact congrArg Nat.succ induction

def assignmentGraph (offsets : List Cell)
    (states : List (Option SquareSymmetry)) :
    List (Cell × Option SquareSymmetry) :=
  offsets.map fun offset =>
    (offset, states.getD (firstIndex offsets offset) none)

/-- Global assignment represented by a finite state word. Unlisted offsets
have state `none`. -/
def listAssignment (offsets : List Cell)
    (states : List (Option SquareSymmetry)) : TrominoAssignment :=
  fun offset =>
    (@List.lookup Cell (Option SquareSymmetry) instBEqOfDecidableEq
      offset (assignmentGraph offsets states)).getD none

theorem listAssignment_eq_getD_of_mem {offsets : List Cell}
    {states : List (Option SquareSymmetry)} {offset : Cell}
    (member : offset ∈ offsets) :
    listAssignment offsets states offset =
      states.getD (firstIndex offsets offset) none := by
  have lookupGraph :=
    @List.lookup_graph Cell (Option SquareSymmetry)
      instBEqOfDecidableEq (by infer_instance)
      (fun listed => states.getD (firstIndex offsets listed) none)
      offset offsets member
  simpa [listAssignment, assignmentGraph] using
    congrArg (Option.getD · none) lookupGraph

theorem listAssignment_eq_none_of_not_mem {offsets : List Cell}
    {states : List (Option SquareSymmetry)} {offset : Cell}
    (notMember : offset ∉ offsets) :
    listAssignment offsets states offset = none := by
  have lookupNone :
      @List.lookup Cell (Option SquareSymmetry) instBEqOfDecidableEq
        offset (assignmentGraph offsets states) = none := by
    rw [@List.lookup_eq_none_iff Cell instBEqOfDecidableEq]
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

theorem listAssignment_map_eq_of_mem {offsets : List Cell}
    (assignment : TrominoAssignment) {offset : Cell}
    (member : offset ∈ offsets) :
    listAssignment offsets (offsets.map assignment) offset = assignment offset := by
  rw [listAssignment_eq_getD_of_mem member,
    firstIndex_eq_idxOf,
    List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf member]
  rfl

/-- Encoding the extension of a finite box assignment as a state word and
decoding it again recovers the extension everywhere. -/
theorem listAssignment_map_extend {tromino : Tromino} {radius : Nat}
    (assignment : FiniteBoxAssignment tromino radius) :
    listAssignment (inspectedOffsetList tromino radius)
        ((inspectedOffsetList tromino radius).map assignment.extend) =
      assignment.extend := by
  funext offset
  by_cases member : offset ∈ inspectedOffsetList tromino radius
  · exact listAssignment_map_eq_of_mem assignment.extend member
  · rw [listAssignment_eq_none_of_not_mem member]
    unfold FiniteBoxAssignment.extend
    rw [dif_neg]
    exact fun finsetMember => member
      ((mem_inspectedOffsetList_iff tromino radius offset).mpr finsetMember)

/-- Membership characterization for the generic exhaustive word generator. -/
theorem mem_words_iff {alphabet : List α} {length : Nat} {word : List α} :
    word ∈ LeanWang.words alphabet length ↔
      word.length = length ∧ ∀ state ∈ word, state ∈ alphabet := by
  induction length generalizing word with
  | zero => cases word <;> simp [LeanWang.words]
  | succ length induction =>
      cases word <;>
        simp [LeanWang.words, induction, and_left_comm, and_assoc, and_comm]

/-- All state words long enough to assign every inspected offset. -/
def assignmentWords (tromino : Tromino) (radius : Nat) :
    List (List (Option SquareSymmetry)) :=
  LeanWang.words assignmentStateList
    (inspectedOffsetList tromino radius).length

/-- A state word satisfies the semantic constraints in the centered box. -/
def IsListValid (tromino : Tromino) (region : Set Cell) (radius : Nat)
    (states : List (Option SquareSymmetry)) : Prop :=
  (listAssignment (inspectedOffsetList tromino radius) states).IsValidInBox
    tromino region radius

/-- Finite box satisfiability expressed as an exhaustive list search. -/
def IsListBoxSatisfiable (tromino : Tromino) (region : Set Cell)
    (radius : Nat) : Prop :=
  ∃ states ∈ assignmentWords tromino radius,
    IsListValid tromino region radius states

theorem isListBoxSatisfiable_iff_isBoxSatisfiable (tromino : Tromino)
    (region : Set Cell) (radius : Nat) :
    IsListBoxSatisfiable tromino region radius ↔
      IsBoxSatisfiable tromino region radius := by
  constructor
  · rintro ⟨states, _, valid⟩
    apply (isBoxSatisfiable_iff_exists_isValidInBox
      tromino region radius).mpr
    exact ⟨listAssignment (inspectedOffsetList tromino radius) states, valid⟩
  · rintro ⟨assignment, valid⟩
    let offsets := inspectedOffsetList tromino radius
    let states := offsets.map assignment.extend
    refine ⟨states, ?_, ?_⟩
    · unfold assignmentWords
      rw [mem_words_iff]
      exact ⟨by simp [states, offsets], fun state state_mem =>
        mem_assignmentStateList state⟩
    · unfold IsListValid
      rw [show listAssignment offsets states = assignment.extend by
        simpa only [offsets, states] using listAssignment_map_extend assignment]
      exact (isFiniteValid_iff_extend_isValidInBox
        tromino region radius assignment).mp valid

/-! ## Primitive-recursive list generators -/

theorem centeredIntegerList_primrec : Primrec centeredIntegerList := by
  unfold centeredIntegerList
  exact Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
        (Primrec.const 1)))
    (int_subtract_primrec.comp₂
      (int_ofNat_primrec.comp₂ Primrec₂.right)
      (int_ofNat_primrec.comp₂ Primrec₂.left))

theorem boxCellList_primrec : Primrec boxCellList := by
  have rows : Primrec₂ fun (radius : Nat) (x : Int) =>
      (centeredIntegerList radius).map fun y => (x, y) := by
    exact Primrec.list_map
      (centeredIntegerList_primrec.comp Primrec.fst)
      (Primrec₂.pair.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
  exact Primrec.list_flatMap centeredIntegerList_primrec rows

theorem placementUnitEquiv_primrec : Primrec placementUnitEquiv := by
  exact Primrec.of_equiv

theorem placement_symmetry_primrec :
    Primrec (Placement.symmetry : Placement Unit → SquareSymmetry) := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp placementUnitEquiv_primrec)).of_eq (fun _ => rfl)

theorem placement_offset_primrec :
    Primrec (Placement.offset : Placement Unit → Cell) := by
  exact (Primrec.snd.comp
    (Primrec.snd.comp placementUnitEquiv_primrec)).of_eq (fun _ => rfl)

theorem placementOfCandidate_primrec : Primrec₂ fun (cell : Cell)
    (candidate : SquareSymmetry × Cell) =>
    (Placement.mk () candidate.1
      (Cell.sub cell (candidate.1.act candidate.2)) : Placement Unit) := by
  have inversePrimrec : Primrec placementUnitEquiv.symm :=
    Primrec.of_equiv_symm
  have tuplePrimrec : Primrec₂ fun (cell : Cell)
      (candidate : SquareSymmetry × Cell) =>
      ((), candidate.1,
        Cell.sub cell (candidate.1.act candidate.2)) :=
    Primrec₂.pair.comp₂ (Primrec₂.const ())
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (cell_sub_primrec.comp₂ Primrec₂.left
          (squareSymmetry_act_primrec.comp₂
            (Primrec.fst.comp₂ Primrec₂.right)
            (Primrec.snd.comp₂ Primrec₂.right))))
  exact (inversePrimrec.comp₂ tuplePrimrec).of_eq fun _ _ => rfl

theorem coveringPlacementList_primrec (tromino : Tromino) :
    Primrec (coveringPlacementList tromino) := by
  unfold coveringPlacementList
  exact Primrec.list_map
    (Primrec.const
      (squareSymmetryList.product (trominoCellList tromino)))
    placementOfCandidate_primrec

theorem inspectedOffsetList_primrec (tromino : Tromino) :
    Primrec (inspectedOffsetList tromino) := by
  have candidateOffsets : Primrec₂ fun (_radius : Nat) (cell : Cell) =>
      (coveringPlacementList tromino cell).map Placement.offset := by
    exact Primrec.list_map
      (coveringPlacementList_primrec tromino |>.comp Primrec.snd)
      (placement_offset_primrec.comp₂ Primrec₂.right)
  unfold inspectedOffsetList
  exact Primrec.list_append.comp boxCellList_primrec
    (Primrec.list_flatMap boxCellList_primrec candidateOffsets)

theorem assignmentGraph_primrec : Primrec₂ assignmentGraph := by
  change Primrec fun input : List Cell × List (Option SquareSymmetry) =>
    assignmentGraph input.1 input.2
  unfold assignmentGraph
  have firstIndexPrimrec : Primrec₂ firstIndex := by
    change Primrec fun input : List Cell × Cell =>
      firstIndex input.1 input.2
    unfold firstIndex
    exact Primrec.list_findIdx Primrec.fst
      (Primrec.eq.decide.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
  have indexPrimrec : Primrec₂ fun
      (input : List Cell × List (Option SquareSymmetry)) (offset : Cell) =>
      firstIndex input.1 offset :=
    firstIndexPrimrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact Primrec.list_map Primrec.fst
    (Primrec₂.pair.comp₂ Primrec₂.right
      (Primrec.list_getD (none : Option SquareSymmetry) |>.comp₂
        (Primrec.snd.comp₂ Primrec₂.left)
        indexPrimrec))

theorem listAssignment_primrec : Primrec₂ fun
    (input : List Cell × List (Option SquareSymmetry)) (cell : Cell) =>
    listAssignment input.1 input.2 cell := by
  have graphPrimrec : Primrec₂ fun
      (input : List Cell × List (Option SquareSymmetry)) (_cell : Cell) =>
      assignmentGraph input.1 input.2 :=
    assignmentGraph_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.left)
  exact (Primrec.option_getD.comp₂
    (Primrec.listLookup.comp₂ Primrec₂.right graphPrimrec)
    (Primrec₂.const none)).of_eq fun _ _ => rfl

theorem assignmentWordsCore_primrec :
    Primrec₂ (LeanWang.words : List (Option SquareSymmetry) → Nat →
      List (List (Option SquareSymmetry))) := by
  let step : List (Option SquareSymmetry) →
      Nat × List (List (Option SquareSymmetry)) →
        List (List (Option SquareSymmetry)) :=
    fun alphabet state => state.2.flatMap fun tail =>
      alphabet.map fun head => head :: tail
  have mapHeads : Primrec₂ fun
      (input : List (Option SquareSymmetry) ×
        (Nat × List (List (Option SquareSymmetry))))
      (tail : List (Option SquareSymmetry)) =>
      input.1.map fun head => head :: tail := by
    exact Primrec.list_map (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst))
  have stepPrimrec : Primrec₂ step := by
    exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) mapHeads
  exact (Primrec.nat_rec
    (Primrec.const ([[]] : List (List (Option SquareSymmetry))))
    stepPrimrec).of_eq (by
      intro alphabet length
      induction length <;> simp [LeanWang.words, step, *])

theorem assignmentWords_primrec (tromino : Tromino) :
    Primrec (assignmentWords tromino) := by
  unfold assignmentWords
  exact assignmentWordsCore_primrec.comp
    (Primrec.const assignmentStateList)
    (Primrec.list_length.comp (inspectedOffsetList_primrec tromino))

/-! ## Periodic-region verifier -/

/-- Candidate placements selected by a finite assignment word at one cell. -/
def activePlacementList (tromino : Tromino) (radius : Nat)
    (states : List (Option SquareSymmetry)) (cell : Cell) :
    List (Placement Unit) :=
  (coveringPlacementList tromino cell).filter fun placement =>
    listAssignment (inspectedOffsetList tromino radius) states
      placement.offset = some placement.symmetry

/-- Fully explicit local verifier using only finite lists and the executable
periodic-region membership checker. -/
def IsPeriodicListValid (tromino : Tromino) (periodicRegion : PeriodicRegion)
    (radius : Nat) (states : List (Option SquareSymmetry)) : Prop :=
  (∀ offset ∈ boxCellList radius, ∀ symmetry ∈ squareSymmetryList,
      listAssignment (inspectedOffsetList tromino radius) states offset =
          some symmetry →
        ∀ source ∈ trominoCellList tromino,
          periodicRegion.validContains
            (Cell.add offset (symmetry.act source)) = true) ∧
    ∀ cell ∈ boxCellList radius,
      periodicRegion.validContains cell = true →
        (activePlacementList tromino radius states cell).length = 1

theorem activeCandidateLength_eq_card (tromino : Tromino) (cell : Cell)
    (assignment : TrominoAssignment) :
    ((coveringPlacementList tromino cell).filter fun placement =>
      assignment placement.offset = some placement.symmetry).length =
    ((coveringPlacements tromino cell).filter fun placement =>
      assignment placement.offset = some placement.symmetry).card := by
  rw [← List.toFinset_card_of_nodup
    ((coveringPlacementList_nodup tromino cell).filter _)]
  apply congrArg Finset.card
  ext placement
  simp [mem_coveringPlacementList_iff]

theorem isPeriodicListValid_iff_isListValid (tromino : Tromino)
    (periodicRegion : PeriodicRegion) (fullRank : periodicRegion.IsFullRank)
    (radius : Nat) (states : List (Option SquareSymmetry)) :
    IsPeriodicListValid tromino periodicRegion radius states ↔
      IsListValid tromino periodicRegion.carrier radius states := by
  let assignment :=
    listAssignment (inspectedOffsetList tromino radius) states
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro offset offsetInBox symmetry cell cellInPlacement selected
      obtain ⟨source, sourceMem, sourceEquality⟩ :=
        (Placement.mem_cells_iff
          (fun _ : Unit => tromino.cells)
          (Placement.mk () symmetry offset) cell).mp cellInPlacement
      have validContains := inside offset
        ((mem_boxCellList_iff radius offset).mpr offsetInBox)
        symmetry (mem_squareSymmetryList symmetry) selected source
        ((mem_trominoCellList_iff tromino source).mpr sourceMem)
      have validContainsCell : periodicRegion.validContains cell = true := by
        simpa only [sourceEquality] using validContains
      exact (periodicRegion.validContains_eq_true_iff cell).mp
        validContainsCell |>.2
    · intro cell cellInBox cellMember
      rw [← activeCandidateLength_eq_card tromino cell assignment]
      apply covered cell ((mem_boxCellList_iff radius cell).mpr cellInBox)
      exact (periodicRegion.validContains_eq_true_iff cell).mpr
        ⟨fullRank, cellMember⟩
  · rintro ⟨inside, covered⟩
    constructor
    · intro offset offsetInList symmetry _ selected source sourceInList
      apply (periodicRegion.validContains_eq_true_iff _).mpr
      refine ⟨fullRank, inside offset
        ((mem_boxCellList_iff radius offset).mp offsetInList)
        symmetry (Cell.add offset (symmetry.act source)) ?_ selected⟩
      rw [Placement.mem_cells_iff]
      exact ⟨source,
        (mem_trominoCellList_iff tromino source).mp sourceInList, rfl⟩
    · intro cell cellInList validContains
      unfold activePlacementList
      rw [activeCandidateLength_eq_card tromino cell assignment]
      apply covered cell ((mem_boxCellList_iff radius cell).mp cellInList)
      exact (periodicRegion.validContains_eq_true_iff cell).mp validContains |>.2

/-- Exhaustive finite periodic-region search. -/
def IsPeriodicListBoxSatisfiable (tromino : Tromino)
    (periodicRegion : PeriodicRegion) (radius : Nat) : Prop :=
  ∃ states ∈ assignmentWords tromino radius,
    IsPeriodicListValid tromino periodicRegion radius states

theorem isPeriodicListBoxSatisfiable_iff (tromino : Tromino)
    (periodicRegion : PeriodicRegion) (fullRank : periodicRegion.IsFullRank)
    (radius : Nat) :
    IsPeriodicListBoxSatisfiable tromino periodicRegion radius ↔
      IsBoxSatisfiable tromino periodicRegion.carrier radius := by
  rw [← isListBoxSatisfiable_iff_isBoxSatisfiable
    tromino periodicRegion.carrier radius]
  unfold IsPeriodicListBoxSatisfiable IsListBoxSatisfiable
  apply exists_congr
  intro states
  apply and_congr_right
  intro _
  exact isPeriodicListValid_iff_isListValid
    tromino periodicRegion fullRank radius states

private abbrev PeriodicSearchInput :=
  (PeriodicRegion × Nat) × List (Option SquareSymmetry)

private def searchRegion (input : PeriodicSearchInput) : PeriodicRegion :=
  input.1.1

private def searchRadius (input : PeriodicSearchInput) : Nat :=
  input.1.2

private def searchStates (input : PeriodicSearchInput) :
    List (Option SquareSymmetry) :=
  input.2

private def searchOffsets (tromino : Tromino)
    (input : PeriodicSearchInput) : List Cell :=
  inspectedOffsetList tromino (searchRadius input)

private def searchStateAt (tromino : Tromino)
    (input : PeriodicSearchInput) (cell : Cell) : Option SquareSymmetry :=
  listAssignment (searchOffsets tromino input) (searchStates input) cell

private theorem searchRegion_primrec : Primrec searchRegion :=
  Primrec.fst.comp Primrec.fst

private theorem searchRadius_primrec : Primrec searchRadius :=
  Primrec.snd.comp Primrec.fst

private theorem searchStates_primrec : Primrec searchStates :=
  Primrec.snd

private theorem searchOffsets_primrec (tromino : Tromino) :
    Primrec (searchOffsets tromino) :=
  (inspectedOffsetList_primrec tromino).comp searchRadius_primrec

private theorem searchStateAt_primrec (tromino : Tromino) :
    Primrec₂ (searchStateAt tromino) := by
  unfold searchStateAt
  exact listAssignment_primrec.comp₂
    (Primrec₂.pair.comp₂
      ((searchOffsets_primrec tromino).comp₂ Primrec₂.left)
      (searchStates_primrec.comp₂ Primrec₂.left))
    Primrec₂.right

private abbrev InsideBase := PeriodicSearchInput × Cell
private abbrev InsideContext :=
  PeriodicSearchInput × (Cell × SquareSymmetry)

private theorem insideSource_primrec (tromino : Tromino) :
    PrimrecRel fun (context : InsideContext) (source : Cell) =>
      searchStateAt tromino context.1 context.2.1 ≠ some context.2.2 ∨
        (searchRegion context.1).validContains
          (Cell.add context.2.1 (context.2.2.act source)) = true := by
  have selected : PrimrecRel fun (context : InsideContext) (_source : Cell) =>
      searchStateAt tromino context.1 context.2.1 = some context.2.2 :=
    Primrec.eq.comp₂
      (searchStateAt_primrec tromino |>.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left))
      (Primrec.option_some.comp₂
        ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left))
  have coveredCell : Primrec₂ fun (context : InsideContext) (source : Cell) =>
      Cell.add context.2.1 (context.2.2.act source) :=
    cell_add_primrec.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
      (squareSymmetry_act_primrec.comp₂
        ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left)
        Primrec₂.right)
  have inside : PrimrecRel fun (context : InsideContext) (source : Cell) =>
      (searchRegion context.1).validContains
        (Cell.add context.2.1 (context.2.2.act source)) = true :=
    Primrec.eq.comp₂
      (periodicRegion_validContains_primrec.comp₂
        (searchRegion_primrec.comp₂
          (Primrec.fst.comp₂ Primrec₂.left))
        coveredCell)
      (Primrec₂.const true)
  exact selected.not.or inside

private theorem insideOffsets_primrec (tromino : Tromino) :
    PrimrecPred fun input : PeriodicSearchInput =>
      ∀ offset ∈ boxCellList (searchRadius input),
        ∀ symmetry ∈ squareSymmetryList,
          searchStateAt tromino input offset = some symmetry →
            ∀ source ∈ trominoCellList tromino,
              (searchRegion input).validContains
                (Cell.add offset (symmetry.act source)) = true := by
  have allSources : PrimrecPred fun context : InsideContext =>
      ∀ source ∈ trominoCellList tromino,
        searchStateAt tromino context.1 context.2.1 ≠ some context.2.2 ∨
          (searchRegion context.1).validContains
            (Cell.add context.2.1 (context.2.2.act source)) = true :=
    (insideSource_primrec tromino).swap.forall_mem_list.comp
      (Primrec.const (trominoCellList tromino)) Primrec.id
  have allSourcesRelation : PrimrecRel fun (symmetry : SquareSymmetry)
      (base : InsideBase) =>
      ∀ source ∈ trominoCellList tromino,
        searchStateAt tromino base.1 base.2 ≠ some symmetry ∨
          (searchRegion base.1).validContains
            (Cell.add base.2 (symmetry.act source)) = true :=
    (allSources.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))).primrecRel
  have allSymmetries : PrimrecPred fun base : InsideBase =>
      ∀ symmetry ∈ squareSymmetryList,
        ∀ source ∈ trominoCellList tromino,
          searchStateAt tromino base.1 base.2 ≠ some symmetry ∨
            (searchRegion base.1).validContains
              (Cell.add base.2 (symmetry.act source)) = true :=
    allSourcesRelation.forall_mem_list.comp
      (Primrec.const squareSymmetryList) Primrec.id
  have offsetRelation : PrimrecRel fun (offset : Cell)
      (input : PeriodicSearchInput) =>
      ∀ symmetry ∈ squareSymmetryList,
        searchStateAt tromino input offset = some symmetry →
          ∀ source ∈ trominoCellList tromino,
            (searchRegion input).validContains
              (Cell.add offset (symmetry.act source)) = true :=
    ((allSymmetries.comp (Primrec.pair Primrec.snd Primrec.fst)).primrecRel).of_eq
      fun offset input => by
        constructor
        · intro all symmetry symmetryMem selected source sourceMem
          exact (all symmetry symmetryMem source sourceMem).resolve_left
            (fun notSelected => notSelected selected)
        · intro all symmetry symmetryMem source sourceMem
          by_cases selected : searchStateAt tromino input offset = some symmetry
          · exact Or.inr (all symmetry symmetryMem selected source sourceMem)
          · exact Or.inl selected
  exact offsetRelation.forall_mem_list.comp
    (boxCellList_primrec.comp searchRadius_primrec) Primrec.id

private abbrev CoverageContext := PeriodicSearchInput × Cell

private theorem activePlacement_primrec (tromino : Tromino) :
    PrimrecRel fun (placement : Placement Unit) (context : CoverageContext) =>
      searchStateAt tromino context.1 placement.offset =
        some placement.symmetry := by
  exact Primrec.eq.comp₂
    (searchStateAt_primrec tromino |>.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (placement_offset_primrec.comp₂ Primrec₂.left))
    (Primrec.option_some.comp₂
      (placement_symmetry_primrec.comp₂ Primrec₂.left))

private theorem coverageCells_primrec (tromino : Tromino) :
    PrimrecPred fun input : PeriodicSearchInput =>
      ∀ cell ∈ boxCellList (searchRadius input),
        (searchRegion input).validContains cell = true →
          (activePlacementList tromino (searchRadius input)
            (searchStates input) cell).length = 1 := by
  have activeList : Primrec fun context : CoverageContext =>
      activePlacementList tromino (searchRadius context.1)
        (searchStates context.1) context.2 := by
    unfold activePlacementList
    exact (activePlacement_primrec tromino).listFilter.comp
      ((coveringPlacementList_primrec tromino).comp Primrec.snd) Primrec.id
  have oneActive : PrimrecPred fun context : CoverageContext =>
      (activePlacementList tromino (searchRadius context.1)
        (searchStates context.1) context.2).length = 1 :=
    Primrec.eq.comp (Primrec.list_length.comp activeList) (Primrec.const 1)
  have regionMember : PrimrecPred fun context : CoverageContext =>
      (searchRegion context.1).validContains context.2 = true :=
    Primrec.eq.comp
      (periodicRegion_validContains_primrec.comp
        (searchRegion_primrec.comp Primrec.fst) Primrec.snd)
      (Primrec.const true)
  have cellRelation : PrimrecRel fun (cell : Cell)
      (input : PeriodicSearchInput) =>
      (searchRegion input).validContains cell = true →
        (activePlacementList tromino (searchRadius input)
          (searchStates input) cell).length = 1 :=
    (((regionMember.not.or oneActive).comp
      (Primrec.pair Primrec.snd Primrec.fst)).primrecRel).of_eq
      fun cell input => by
        by_cases member : (searchRegion input).validContains cell = true
        · simp [member]
        · simp [member]
  exact cellRelation.forall_mem_list.comp
    (boxCellList_primrec.comp searchRadius_primrec) Primrec.id

theorem isPeriodicListValid_primrec (tromino : Tromino) :
    PrimrecPred fun input : PeriodicSearchInput =>
      IsPeriodicListValid tromino (searchRegion input)
        (searchRadius input) (searchStates input) := by
  simpa only [IsPeriodicListValid, searchOffsets, searchStateAt] using
    (insideOffsets_primrec tromino).and (coverageCells_primrec tromino)

theorem isPeriodicListBoxSatisfiable_primrec (tromino : Tromino) :
    PrimrecPred fun input : PeriodicRegion × Nat =>
      IsPeriodicListBoxSatisfiable tromino input.1 input.2 := by
  have validRelation : PrimrecRel fun
      (states : List (Option SquareSymmetry))
      (input : PeriodicRegion × Nat) =>
      IsPeriodicListValid tromino input.1 input.2 states :=
    ((isPeriodicListValid_primrec tromino).primrecRel.swap).of_eq
      fun _ _ => Iff.rfl
  have finiteSearch : PrimrecPred fun input : PeriodicRegion × Nat =>
      ∃ states ∈ assignmentWords tromino input.2,
        IsPeriodicListValid tromino input.1 input.2 states :=
    validRelation.exists_mem_list.comp
      ((assignmentWords_primrec tromino).comp Primrec.snd) Primrec.id
  exact finiteSearch.of_eq fun _ => Iff.rfl

/-- A finite certificate that a periodic-region input is a no-instance:
either its period presentation is malformed (`index = 0`), or a finite box
has no satisfying assignment (`index = radius + 1`). -/
def PeriodicTrominoObstruction (tromino : Tromino)
    (input : PeriodicRegion × Nat) : Prop :=
  (input.2 = 0 ∧ ¬ input.1.IsFullRank) ∨
    (input.2 ≠ 0 ∧
      ¬ IsPeriodicListBoxSatisfiable tromino input.1 (input.2 - 1))

theorem periodicTrominoObstruction_primrec (tromino : Tromino) :
    PrimrecPred (PeriodicTrominoObstruction tromino) := by
  have indexZero : PrimrecPred fun input : PeriodicRegion × Nat =>
      input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have malformed : PrimrecPred fun input : PeriodicRegion × Nat =>
      ¬ input.1.IsFullRank :=
    (periodicRegion_isFullRank_primrec.comp Primrec.fst).not
  have indexNonzero : PrimrecPred fun input : PeriodicRegion × Nat =>
      input.2 ≠ 0 :=
    indexZero.not
  have unsatisfiable : PrimrecPred fun input : PeriodicRegion × Nat =>
      ¬ IsPeriodicListBoxSatisfiable tromino input.1 (input.2 - 1) :=
    ((isPeriodicListBoxSatisfiable_primrec tromino).comp
      (Primrec.pair Primrec.fst
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))).not
  exact ((indexZero.and malformed).or
    (indexNonzero.and unsatisfiable)).of_eq fun _ => Iff.rfl

theorem exists_periodicTrominoObstruction_iff (tromino : Tromino)
    (periodicRegion : PeriodicRegion) :
    (∃ index, PeriodicTrominoObstruction tromino (periodicRegion, index)) ↔
      ¬ PeriodicTrominoTiling tromino periodicRegion := by
  classical
  constructor
  · rintro ⟨index, malformed | unsatisfiable⟩
    · rintro ⟨fullRank, _⟩
      exact malformed.2 fullRank
    · rintro ⟨fullRank, tileable⟩
      have boxSatisfiable :=
        (tileable_iff_forall_isBoxSatisfiable
          tromino periodicRegion.carrier).mp tileable (index - 1)
      have listSatisfiable :=
        (isPeriodicListBoxSatisfiable_iff tromino periodicRegion
          fullRank (index - 1)).mpr boxSatisfiable
      exact unsatisfiable.2 listSatisfiable
  · intro notTiling
    by_cases fullRank : periodicRegion.IsFullRank
    · have notTileable : ¬ tromino.Tileable periodicRegion.carrier :=
        fun tileable => notTiling ⟨fullRank, tileable⟩
      have finiteObstruction : ∃ radius,
          ¬ IsBoxSatisfiable tromino periodicRegion.carrier radius := by
        simpa only [not_forall] using
          (not_congr (tileable_iff_forall_isBoxSatisfiable
            tromino periodicRegion.carrier)).mp notTileable
      obtain ⟨radius, unsatisfiable⟩ := finiteObstruction
      refine ⟨radius + 1, Or.inr ⟨by omega, ?_⟩⟩
      simpa only [Nat.add_sub_cancel] using
        (not_congr (isPeriodicListBoxSatisfiable_iff
          tromino periodicRegion fullRank radius)).mpr unsatisfiable
    · exact ⟨0, Or.inl ⟨rfl, fullRank⟩⟩

/-- The 2D periodic tromino tiling problem belongs to co-r.e. for either
tromino, via exhaustive finite-obstruction search. -/
theorem periodicTrominoTiling_coRE (tromino : Tromino) :
    LeanWang.CoREPred (PeriodicTrominoTiling tromino) := by
  unfold LeanWang.CoREPred
  have obstructionComputable : ComputablePred fun
      input : PeriodicRegion × Nat =>
      PeriodicTrominoObstruction tromino input :=
    (periodicTrominoObstruction_primrec tromino).computablePred
  have obstructionRE : REPred fun periodicRegion : PeriodicRegion =>
      ∃ index, PeriodicTrominoObstruction tromino (periodicRegion, index) :=
    LeanWang.REPred.exists_nat obstructionComputable
  exact obstructionRE.of_eq fun periodicRegion =>
    exists_periodicTrominoObstruction_iff tromino periodicRegion

end TrominoAssignment
end LeanTrominoes
