/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComputableSearch

/-! # Finite-box search for computable families of regions -/

namespace LeanTrominoes.TrominoAssignment.ComputableRegionSearch
open LeanTrominoes.Computability
variable {α : Type} (contains : α → Cell → Bool)

/-- Fully explicit local verifier using only finite lists and the executable
region membership checker. -/
def IsComputableListValid (tromino : Tromino) (periodicRegion : α)
    (radius : Nat) (states : List (Option SquareSymmetry)) : Prop :=
  (∀ offset ∈ boxCellList radius, ∀ symmetry ∈ squareSymmetryList,
      listAssignment (inspectedOffsetList tromino radius) states offset =
          some symmetry →
        ∀ source ∈ trominoCellList tromino,
          contains periodicRegion
            (Cell.add offset (symmetry.act source)) = true) ∧
    ∀ cell ∈ boxCellList radius,
      contains periodicRegion cell = true →
        (activePlacementList tromino radius states cell).length = 1

theorem isComputableListValid_iff_isListValid (tromino : Tromino)
    (periodicRegion : α)
    (radius : Nat) (states : List (Option SquareSymmetry)) :
    IsComputableListValid contains tromino periodicRegion radius states ↔
      IsListValid tromino {c | contains periodicRegion c = true} radius states := by
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
      have validContainsCell : contains periodicRegion cell = true := by
        simpa only [sourceEquality] using validContains
      exact validContainsCell
    · intro cell cellInBox cellMember
      rw [← activeCandidateLength_eq_card tromino cell assignment]
      apply covered cell ((mem_boxCellList_iff radius cell).mpr cellInBox)
      exact cellMember
  · rintro ⟨inside, covered⟩
    constructor
    · intro offset offsetInList symmetry _ selected source sourceInList
      refine inside offset
        ((mem_boxCellList_iff radius offset).mp offsetInList)
        symmetry (Cell.add offset (symmetry.act source)) ?_ selected
      rw [Placement.mem_cells_iff]
      exact ⟨source,
        (mem_trominoCellList_iff tromino source).mp sourceInList, rfl⟩
    · intro cell cellInList validContains
      unfold activePlacementList
      rw [activeCandidateLength_eq_card tromino cell assignment]
      apply covered cell ((mem_boxCellList_iff radius cell).mp cellInList)
      exact validContains

/-- Exhaustive finite search for a computable region. -/
def IsComputableListBoxSatisfiable (tromino : Tromino)
    (periodicRegion : α) (radius : Nat) : Prop :=
  ∃ states ∈ assignmentWords tromino radius,
    IsComputableListValid contains tromino periodicRegion radius states

theorem isComputableListBoxSatisfiable_iff (tromino : Tromino)
    (periodicRegion : α)
    (radius : Nat) :
    IsComputableListBoxSatisfiable contains tromino periodicRegion radius ↔
      IsBoxSatisfiable tromino {c | contains periodicRegion c = true} radius := by
  rw [← isListBoxSatisfiable_iff_isBoxSatisfiable
    tromino {c | contains periodicRegion c = true} radius]
  unfold IsComputableListBoxSatisfiable IsListBoxSatisfiable
  apply exists_congr
  intro states
  apply and_congr_right
  intro _
  exact isComputableListValid_iff_isListValid
    contains tromino periodicRegion radius states

variable [Primcodable α]

private abbrev SearchInput (α : Type) :=
  (α × Nat) × List (Option SquareSymmetry)

private def searchRegion (input : SearchInput α) : α :=
  input.1.1

private def searchRadius (input : SearchInput α) : Nat :=
  input.1.2

private def searchStates (input : SearchInput α) :
    List (Option SquareSymmetry) :=
  input.2

private def searchOffsets (tromino : Tromino)
    (input : SearchInput α) : List Cell :=
  inspectedOffsetList tromino (searchRadius input)

private def searchStateAt (tromino : Tromino)
    (input : SearchInput α) (cell : Cell) : Option SquareSymmetry :=
  listAssignment (searchOffsets tromino input) (searchStates input) cell

private theorem searchRegion_primrec : Primrec (searchRegion (α := α)) :=
  Primrec.fst.comp Primrec.fst

private theorem searchRadius_primrec : Primrec (searchRadius (α := α)) :=
  Primrec.snd.comp Primrec.fst

private theorem searchStates_primrec : Primrec (searchStates (α := α)) :=
  Primrec.snd

private theorem searchOffsets_primrec (tromino : Tromino) :
    Primrec (searchOffsets (α := α) tromino) :=
  (inspectedOffsetList_primrec tromino).comp searchRadius_primrec

private theorem searchStateAt_primrec (tromino : Tromino) :
    Primrec₂ (searchStateAt (α := α) tromino) := by
  unfold searchStateAt
  exact listAssignment_primrec.comp₂
    (Primrec₂.pair.comp₂
      ((searchOffsets_primrec tromino).comp₂ Primrec₂.left)
      (searchStates_primrec.comp₂ Primrec₂.left))
    Primrec₂.right

private abbrev InsideBase (α : Type) := SearchInput α × Cell
private abbrev InsideContext (α : Type) :=
  SearchInput α × (Cell × SquareSymmetry)

variable {contains} (contains_primrec : Primrec₂ contains)

include contains_primrec in
private theorem insideSource_primrec (tromino : Tromino) :
    PrimrecRel fun (context : InsideContext α) (source : Cell) =>
      searchStateAt tromino context.1 context.2.1 ≠ some context.2.2 ∨
        contains (searchRegion context.1)
          (Cell.add context.2.1 (context.2.2.act source)) = true := by
  have selected : PrimrecRel fun (context : InsideContext α) (_source : Cell) =>
      searchStateAt tromino context.1 context.2.1 = some context.2.2 :=
    Primrec.eq.comp₂
      (searchStateAt_primrec tromino |>.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left))
      (Primrec.option_some.comp₂
        ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left))
  have coveredCell : Primrec₂ fun (context : InsideContext α) (source : Cell) =>
      Cell.add context.2.1 (context.2.2.act source) :=
    cell_add_primrec.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
      (squareSymmetry_act_primrec.comp₂
        ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left)
        Primrec₂.right)
  have inside : PrimrecRel fun (context : InsideContext α) (source : Cell) =>
      contains (searchRegion context.1)
        (Cell.add context.2.1 (context.2.2.act source)) = true :=
    Primrec.eq.comp₂
      (contains_primrec.comp₂
        (searchRegion_primrec.comp₂
          (Primrec.fst.comp₂ Primrec₂.left))
        coveredCell)
      (Primrec₂.const true)
  exact selected.not.or inside

include contains_primrec in
private theorem insideOffsets_primrec (tromino : Tromino) :
    PrimrecPred fun input : SearchInput α =>
      ∀ offset ∈ boxCellList (searchRadius input),
        ∀ symmetry ∈ squareSymmetryList,
          searchStateAt tromino input offset = some symmetry →
            ∀ source ∈ trominoCellList tromino,
              contains (searchRegion input)
                (Cell.add offset (symmetry.act source)) = true := by
  have allSources : PrimrecPred fun context : InsideContext α =>
      ∀ source ∈ trominoCellList tromino,
        searchStateAt tromino context.1 context.2.1 ≠ some context.2.2 ∨
          contains (searchRegion context.1)
            (Cell.add context.2.1 (context.2.2.act source)) = true :=
    (insideSource_primrec contains_primrec tromino).swap.forall_mem_list.comp
      (Primrec.const (trominoCellList tromino)) Primrec.id
  have allSourcesRelation : PrimrecRel fun (symmetry : SquareSymmetry)
      (base : InsideBase α) =>
      ∀ source ∈ trominoCellList tromino,
        searchStateAt tromino base.1 base.2 ≠ some symmetry ∨
          contains (searchRegion base.1)
            (Cell.add base.2 (symmetry.act source)) = true :=
    (allSources.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))).primrecRel
  have allSymmetries : PrimrecPred fun base : InsideBase α =>
      ∀ symmetry ∈ squareSymmetryList,
        ∀ source ∈ trominoCellList tromino,
          searchStateAt tromino base.1 base.2 ≠ some symmetry ∨
            contains (searchRegion base.1)
              (Cell.add base.2 (symmetry.act source)) = true :=
    allSourcesRelation.forall_mem_list.comp
      (Primrec.const squareSymmetryList) Primrec.id
  have offsetRelation : PrimrecRel fun (offset : Cell)
      (input : SearchInput α) =>
      ∀ symmetry ∈ squareSymmetryList,
        searchStateAt tromino input offset = some symmetry →
          ∀ source ∈ trominoCellList tromino,
            contains (searchRegion input)
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

private abbrev CoverageContext (α : Type) := SearchInput α × Cell

private theorem activePlacement_primrec (tromino : Tromino) :
    PrimrecRel fun (placement : Placement Unit) (context : CoverageContext α) =>
      searchStateAt tromino context.1 placement.offset =
        some placement.symmetry := by
  exact Primrec.eq.comp₂
    (searchStateAt_primrec tromino |>.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (placement_offset_primrec.comp₂ Primrec₂.left))
    (Primrec.option_some.comp₂
      (placement_symmetry_primrec.comp₂ Primrec₂.left))

include contains_primrec in
private theorem coverageCells_primrec (tromino : Tromino) :
    PrimrecPred fun input : SearchInput α =>
      ∀ cell ∈ boxCellList (searchRadius input),
        contains (searchRegion input) cell = true →
          (activePlacementList tromino (searchRadius input)
            (searchStates input) cell).length = 1 := by
  have activeList : Primrec fun context : CoverageContext α =>
      activePlacementList tromino (searchRadius context.1)
        (searchStates context.1) context.2 := by
    unfold activePlacementList
    exact (activePlacement_primrec tromino).listFilter.comp
      ((coveringPlacementList_primrec tromino).comp Primrec.snd) Primrec.id
  have oneActive : PrimrecPred fun context : CoverageContext α =>
      (activePlacementList tromino (searchRadius context.1)
        (searchStates context.1) context.2).length = 1 :=
    Primrec.eq.comp (Primrec.list_length.comp activeList) (Primrec.const 1)
  have regionMember : PrimrecPred fun context : CoverageContext α =>
      contains (searchRegion context.1) context.2 = true :=
    Primrec.eq.comp
      (contains_primrec.comp
        (searchRegion_primrec.comp Primrec.fst) Primrec.snd)
      (Primrec.const true)
  have cellRelation : PrimrecRel fun (cell : Cell)
      (input : SearchInput α) =>
      contains (searchRegion input) cell = true →
        (activePlacementList tromino (searchRadius input)
          (searchStates input) cell).length = 1 :=
    (((regionMember.not.or oneActive).comp
      (Primrec.pair Primrec.snd Primrec.fst)).primrecRel).of_eq
      fun cell input => by
        by_cases member : contains (searchRegion input) cell = true
        · simp [member]
        · simp [member]
  exact cellRelation.forall_mem_list.comp
    (boxCellList_primrec.comp searchRadius_primrec) Primrec.id

include contains_primrec in
theorem isComputableListValid_primrec (tromino : Tromino) :
    PrimrecPred fun input : SearchInput α =>
      IsComputableListValid contains tromino (searchRegion input)
        (searchRadius input) (searchStates input) := by
  simpa only [IsComputableListValid, searchOffsets, searchStateAt] using
    (insideOffsets_primrec contains_primrec tromino).and (coverageCells_primrec contains_primrec tromino)

include contains_primrec in
theorem isComputableListBoxSatisfiable_primrec (tromino : Tromino) :
    PrimrecPred fun input : α × Nat =>
      IsComputableListBoxSatisfiable contains tromino input.1 input.2 := by
  have validRelation : PrimrecRel fun
      (states : List (Option SquareSymmetry))
      (input : α × Nat) =>
      IsComputableListValid contains tromino input.1 input.2 states :=
    ((isComputableListValid_primrec contains_primrec tromino).primrecRel.swap).of_eq
      fun _ _ => Iff.rfl
  have finiteSearch : PrimrecPred fun input : α × Nat =>
      ∃ states ∈ assignmentWords tromino input.2,
        IsComputableListValid contains tromino input.1 input.2 states :=
    validRelation.exists_mem_list.comp
      ((assignmentWords_primrec tromino).comp Primrec.snd) Primrec.id
  exact finiteSearch.of_eq fun _ => Iff.rfl


end LeanTrominoes.TrominoAssignment.ComputableRegionSearch
