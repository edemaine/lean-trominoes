import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Lean.Elab.Tactic.Omega

/-!
# Verified finite exact-cover search

The constant-size tromino gadgets are exact-cover instances.  This module
provides a generic backtracking enumerator and proves that it returns exactly
the irredundant exact covers of a finite target.  Choosing a target cell before
branching avoids the exponential powerset materialization used by the abstract
specification.
-/

namespace LeanTrominoes

namespace ExactCover

variable {Piece CellType : Type*} [DecidableEq Piece] [DecidableEq CellType]

/-- A finite collection of pieces covers `target` exactly: every selected
piece covers at least one cell, their union is the target, and distinct pieces
are disjoint. -/
structure IsExactCover (footprint : Piece → Finset CellType)
    (target : Finset CellType) (selection : Finset Piece) : Prop where
  nonempty : ∀ piece ∈ selection, (footprint piece).Nonempty
  union_eq : selection.biUnion footprint = target
  pairwiseDisjoint : (selection : Set Piece).Pairwise fun first second =>
    Disjoint (footprint first) (footprint second)

omit [DecidableEq Piece] in
theorem IsExactCover.footprint_subset {footprint : Piece → Finset CellType}
    {target : Finset CellType} {selection : Finset Piece}
    (cover : IsExactCover footprint target selection)
    {piece : Piece} (pieceMember : piece ∈ selection) :
    footprint piece ⊆ target := by
  intro cell cellMember
  rw [← cover.union_eq]
  exact Finset.mem_biUnion.mpr ⟨piece, pieceMember, cellMember⟩

theorem IsExactCover.eq_empty_of_target_empty
    {footprint : Piece → Finset CellType} {selection : Finset Piece}
    (cover : IsExactCover footprint ∅ selection) : selection = ∅ := by
  by_contra nonempty
  obtain ⟨piece, pieceMember⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
  obtain ⟨cell, cellMember⟩ := cover.nonempty piece pieceMember
  have impossible : cell ∈ (∅ : Finset CellType) :=
    cover.footprint_subset pieceMember cellMember
  simp at impossible

@[simp]
theorem isExactCover_empty_iff (footprint : Piece → Finset CellType)
    (selection : Finset Piece) :
    IsExactCover footprint ∅ selection ↔ selection = ∅ := by
  constructor
  · exact IsExactCover.eq_empty_of_target_empty
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩

theorem IsExactCover.insertPiece {footprint : Piece → Finset CellType}
    {target : Finset CellType} {rest : Finset Piece} {piece : Piece}
    (pieceNonempty : (footprint piece).Nonempty)
    (pieceSubset : footprint piece ⊆ target)
    (restCover : IsExactCover footprint (target \ footprint piece) rest) :
    IsExactCover footprint target (insert piece rest) := by
  have pieceNotMember : piece ∉ rest := by
    intro pieceMember
    obtain ⟨cell, cellMember⟩ := pieceNonempty
    have remainingMember :=
      restCover.footprint_subset pieceMember cellMember
    exact (Finset.mem_sdiff.mp remainingMember).2 cellMember
  constructor
  · intro other otherMember
    rw [Finset.mem_insert] at otherMember
    rcases otherMember with rfl | otherMember
    · exact pieceNonempty
    · exact restCover.nonempty other otherMember
  · rw [Finset.biUnion_insert, restCover.union_eq,
      Finset.union_sdiff_of_subset pieceSubset]
  · rw [show (↑(insert piece rest) : Set Piece) =
        insert piece (↑rest : Set Piece) by simp,
      Set.pairwise_insert]
    constructor
    · exact restCover.pairwiseDisjoint
    · intro other otherMember distinct
      have otherSubset := restCover.footprint_subset otherMember
      have disjoint : Disjoint (footprint piece) (footprint other) := by
        rw [Finset.disjoint_left]
        intro cell pieceMember otherCellMember
        exact (Finset.mem_sdiff.mp (otherSubset otherCellMember)).2 pieceMember
      exact ⟨disjoint, disjoint.symm⟩

theorem IsExactCover.erase {footprint : Piece → Finset CellType}
    {target : Finset CellType} {selection : Finset Piece}
    (cover : IsExactCover footprint target selection)
    {piece : Piece} (pieceMember : piece ∈ selection) :
    IsExactCover footprint (target \ footprint piece)
      (selection.erase piece) := by
  constructor
  · intro other otherMember
    exact cover.nonempty other (Finset.mem_of_mem_erase otherMember)
  · ext cell
    constructor
    · intro cellMember
      obtain ⟨other, otherMember, otherCovers⟩ :=
        Finset.mem_biUnion.mp cellMember
      have erased := Finset.mem_erase.mp otherMember
      refine Finset.mem_sdiff.mpr
        ⟨cover.footprint_subset erased.2 otherCovers, ?_⟩
      intro pieceCovers
      have disjoint := cover.pairwiseDisjoint
        erased.2 pieceMember erased.1
      exact Finset.disjoint_left.mp disjoint otherCovers pieceCovers
    · intro cellMember
      have targetMember := (Finset.mem_sdiff.mp cellMember).1
      rw [← cover.union_eq] at targetMember
      obtain ⟨other, otherMember, otherCovers⟩ :=
        Finset.mem_biUnion.mp targetMember
      have distinct : other ≠ piece := by
        intro equality
        subst other
        exact (Finset.mem_sdiff.mp cellMember).2 otherCovers
      exact Finset.mem_biUnion.mpr
        ⟨other, Finset.mem_erase.mpr ⟨distinct, otherMember⟩, otherCovers⟩
  · apply Set.Pairwise.mono _ cover.pairwiseDisjoint
    intro piece erasedMember
    exact Finset.mem_of_mem_erase erasedMember

theorem isExactCover_iff_card_one (footprint : Piece → Finset CellType)
    (target : Finset CellType) (selection : Finset Piece) :
    IsExactCover footprint target selection ↔
      (∀ piece ∈ selection,
        (footprint piece).Nonempty ∧ footprint piece ⊆ target) ∧
      ∀ cell ∈ target,
        (selection.filter fun piece => cell ∈ footprint piece).card = 1 := by
  constructor
  · intro cover
    constructor
    · intro piece pieceMember
      exact ⟨cover.nonempty piece pieceMember,
        cover.footprint_subset pieceMember⟩
    · intro cell cellMember
      have unionMember : cell ∈ selection.biUnion footprint := by
        rw [cover.union_eq]
        exact cellMember
      obtain ⟨piece, pieceMember, pieceCovers⟩ :=
        Finset.mem_biUnion.mp unionMember
      apply Finset.card_eq_one.mpr
      refine ⟨piece, Finset.ext ?_⟩
      intro other
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨otherMember, otherCovers⟩
        by_contra distinct
        have disjoint := cover.pairwiseDisjoint
          otherMember pieceMember distinct
        exact Finset.disjoint_left.mp disjoint otherCovers pieceCovers
      · rintro rfl
        exact ⟨pieceMember, pieceCovers⟩
  · rintro ⟨pieceData, covered⟩
    constructor
    · intro piece pieceMember
      exact (pieceData piece pieceMember).1
    · ext cell
      constructor
      · intro unionMember
        obtain ⟨piece, pieceMember, pieceCovers⟩ :=
          Finset.mem_biUnion.mp unionMember
        exact (pieceData piece pieceMember).2 pieceCovers
      · intro cellMember
        obtain ⟨piece, filteredEquality⟩ :=
          Finset.card_eq_one.mp (covered cell cellMember)
        have pieceFiltered : piece ∈
            selection.filter fun candidate => cell ∈ footprint candidate := by
          rw [filteredEquality]
          simp
        have data := Finset.mem_filter.mp pieceFiltered
        exact Finset.mem_biUnion.mpr ⟨piece, data.1, data.2⟩
    · intro first firstMember second secondMember distinct
      rw [Finset.disjoint_left]
      intro cell firstCovers secondCovers
      have cellMember := (pieceData first firstMember).2 firstCovers
      obtain ⟨only, filteredEquality⟩ :=
        Finset.card_eq_one.mp (covered cell cellMember)
      have firstFiltered : first ∈
          selection.filter fun candidate => cell ∈ footprint candidate :=
        Finset.mem_filter.mpr ⟨firstMember, firstCovers⟩
      have secondFiltered : second ∈
          selection.filter fun candidate => cell ∈ footprint candidate :=
        Finset.mem_filter.mpr ⟨secondMember, secondCovers⟩
      rw [filteredEquality] at firstFiltered secondFiltered
      have firstEquality : first = only := by simpa using firstFiltered
      have secondEquality : second = only := by simpa using secondFiltered
      exact distinct (firstEquality.trans secondEquality.symm)

/-- Fuelled backtracking. At each step, select one remaining target cell and
branch only over candidates that cover it without leaving the target. -/
def searchAux
    (choose : ∀ target : Finset CellType, target.Nonempty → CellType)
    (footprint : Piece → Finset CellType) (candidates : List Piece) :
    Nat → Finset CellType → List (Finset Piece)
  | 0, target => if target = ∅ then [∅] else []
  | fuel + 1, target =>
      if targetNonempty : target.Nonempty then
        let pivot := choose target targetNonempty
        candidates.flatMap fun piece =>
            if pivot ∈ footprint piece ∧ footprint piece ⊆ target then
              (searchAux choose footprint candidates fuel
                (target \ footprint piece)).map (insert piece)
            else
              []
      else
        [∅]

theorem mem_searchAux_iff
    (choose : ∀ target : Finset CellType, target.Nonempty → CellType)
    (chooseMember : ∀ target nonempty, choose target nonempty ∈ target)
    (footprint : Piece → Finset CellType) (candidates : List Piece)
    (fuel : Nat) (target : Finset CellType) (selection : Finset Piece)
    (bound : target.card ≤ fuel) :
    selection ∈ searchAux choose footprint candidates fuel target ↔
      (∀ piece ∈ selection, piece ∈ candidates) ∧
        IsExactCover footprint target selection := by
  induction fuel generalizing target selection with
  | zero =>
      have targetEmpty : target = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero bound)
      subst target
      simp [searchAux]
      intro equality
      subst selection
      simp
  | succ fuel induction =>
      by_cases targetEmpty : target = ∅
      · subst target
        simp [searchAux]
        intro equality
        subst selection
        simp
      · have targetNonempty : target.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr targetEmpty
        let pivot := choose target targetNonempty
        have pivotMember : pivot ∈ target := chooseMember target targetNonempty
        simp only [searchAux, dif_pos targetNonempty, List.mem_flatMap]
        constructor
        · rintro ⟨piece, pieceCandidate, branch⟩
          by_cases valid : pivot ∈ footprint piece ∧
              footprint piece ⊆ target
          · rw [if_pos valid] at branch
            rw [List.mem_map] at branch
            obtain ⟨rest, restMember, equality⟩ := branch
            have footprintNonempty : (footprint piece).Nonempty :=
              ⟨pivot, valid.1⟩
            have remainingBound :
                (target \ footprint piece).card ≤ fuel := by
              rw [Finset.card_sdiff_of_subset valid.2]
              have positive : 0 < (footprint piece).card :=
                Finset.card_pos.mpr footprintNonempty
              omega
            have restData :=
              (induction (target \ footprint piece) rest
                remainingBound).mp restMember
            rw [← equality]
            constructor
            · intro other otherMember
              rw [Finset.mem_insert] at otherMember
              rcases otherMember with rfl | otherMember
              · exact pieceCandidate
              · exact restData.1 other otherMember
            · exact restData.2.insertPiece footprintNonempty valid.2
          · rw [if_neg valid] at branch
            simp at branch
        · rintro ⟨allCandidates, cover⟩
          have pivotUnion : pivot ∈ selection.biUnion footprint := by
            rw [cover.union_eq]
            exact pivotMember
          obtain ⟨piece, pieceMember, pieceCovers⟩ :=
            Finset.mem_biUnion.mp pivotUnion
          have pieceCandidate := allCandidates piece pieceMember
          have pieceSubset := cover.footprint_subset pieceMember
          have footprintNonempty : (footprint piece).Nonempty :=
            ⟨pivot, pieceCovers⟩
          have remainingBound :
              (target \ footprint piece).card ≤ fuel := by
            rw [Finset.card_sdiff_of_subset pieceSubset]
            have positive : 0 < (footprint piece).card :=
              Finset.card_pos.mpr footprintNonempty
            omega
          have restMember : selection.erase piece ∈
              searchAux choose footprint candidates fuel
                (target \ footprint piece) := by
            apply (induction _ _ remainingBound).mpr
            constructor
            · intro other otherMember
              exact allCandidates other
                (Finset.mem_of_mem_erase otherMember)
            · exact cover.erase pieceMember
          refine ⟨piece, pieceCandidate, ?_⟩
          rw [if_pos ⟨pieceCovers, pieceSubset⟩, List.mem_map]
          exact ⟨selection.erase piece, restMember,
            Finset.insert_erase pieceMember⟩

/-- Enumerate exact covers, with one recursion level available for each target
cell. -/
def search (choose : ∀ target : Finset CellType, target.Nonempty → CellType)
    (footprint : Piece → Finset CellType) (candidates : List Piece)
    (target : Finset CellType) :
    List (Finset Piece) :=
  searchAux choose footprint candidates target.card target

theorem mem_search_iff
    (choose : ∀ target : Finset CellType, target.Nonempty → CellType)
    (chooseMember : ∀ target nonempty, choose target nonempty ∈ target)
    (footprint : Piece → Finset CellType) (candidates : List Piece)
    (target : Finset CellType) (selection : Finset Piece) :
    selection ∈ search choose footprint candidates target ↔
      (∀ piece ∈ selection, piece ∈ candidates) ∧
        IsExactCover footprint target selection := by
  exact mem_searchAux_iff choose chooseMember footprint candidates target.card
    target selection (by rfl)

end ExactCover
end LeanTrominoes
