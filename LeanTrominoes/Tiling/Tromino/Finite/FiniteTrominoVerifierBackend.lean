/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ExactOne.FiniteExactCoverVerifier
import LeanTrominoes.Tiling.Completion.FiniteTrominoCompletionCertificate
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic

/-! # Geometric correctness of the finite tromino verifier backend

Canonical binary names identify cells and whole footprints. The exact-cover
machine verifies both finite-region tilings and finite box covers preserving
preplacements. Its input includes the generated candidate table; this file
does not claim a polynomial-time emitter from the original coordinate input.
-/
namespace LeanTrominoes.Tromino.FiniteVerifier
open _root_.Computability Turing
open FiniteWitness
abbrev Word := List Bool

def cellWord (cell : Cell) : Word := encodeNat (Encodable.encode cell)

theorem cellWord_injective : Function.Injective cellWord := by
  intro first second equal
  apply Encodable.encode_injective
  simpa [cellWord] using congrArg decodeNat equal

def footprintWords (tile : Finset Cell) : List Word :=
  ((tile.image Encodable.encode).sort (·≤·)).map encodeNat

@[simp] theorem mem_footprintWords (tile : Finset Cell) (cell : Cell) :
    cellWord cell∈footprintWords tile ↔ cell∈tile := by
  simp only [footprintWords,List.mem_map,Finset.mem_sort,Finset.mem_image]
  constructor
  · rintro ⟨code,⟨other,member,rfl⟩,equal⟩
    exact cellWord_injective equal ▸ member
  · intro member
    exact ⟨Encodable.encode cell,⟨cell,member,rfl⟩,rfl⟩

theorem word_of_footprint (tile : Finset Cell) (word : Word)
    (member : word∈footprintWords tile) : ∃ cell∈tile, cellWord cell=word := by
  obtain ⟨code,hm,rfl⟩ := List.mem_map.mp member
  obtain ⟨cell,hc,rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hm)
  exact ⟨cell,hc,rfl⟩

theorem footprintWords_injective : Function.Injective footprintWords := by
  intro first second equal
  ext cell
  rw [← mem_footprintWords,← mem_footprintWords,equal]

theorem footprintWords_nodup (tile : Finset Cell) : (footprintWords tile).Nodup := by
  apply (Finset.sort_nodup _ _).map
  intro first second equal
  simpa using congrArg decodeNat equal

@[simp] theorem footprintWords_length (tile : Finset Cell) :
    (footprintWords tile).length=tile.card := by
  simp [footprintWords,Finset.card_image_of_injective _ Encodable.encode_injective]

def tileKey (tile : Finset Cell) : Word := BinaryWordBlocks.pack (footprintWords tile)

theorem tileKey_injective : Function.Injective tileKey :=
  BinaryWordBlocks.pack_injective.comp footprintWords_injective

def candidateTiles (t : Tromino) (cells : List Cell) : List (Finset Cell) :=
  (FiniteRegion.candidateList t cells).dedup

@[simp] theorem mem_candidateTiles (t : Tromino) (cells : List Cell) (tile : Finset Cell) :
    tile∈candidateTiles t cells ↔ tile∈candidates t cells.toFinset := by
  rw [candidateTiles,List.mem_dedup,← FiniteRegion.candidateList_eq]
  simp

theorem candidateTiles_length_le (t : Tromino) (cells : List Cell) :
    (candidateTiles t cells).length≤24*cells.length := by
  simpa [candidateTiles] using (List.dedup_sublist (FiniteRegion.candidateList t cells)).length_le

def selectedTiles (t : Tromino) (cells : List Cell) (bits : List Bool) : List (Finset Cell) :=
  DelimitedBinaryWordBooleanFilter.selected bits (candidateTiles t cells)

theorem selected_sublist {Value : Type} (bits : List Bool) (values : List Value) :
    List.Sublist (DelimitedBinaryWordBooleanFilter.selected bits values) values := by
  induction bits generalizing values with
  | nil => simp [DelimitedBinaryWordBooleanFilter.selected]
  | cons bit bits ih =>
    cases values with
    | nil => simp [DelimitedBinaryWordBooleanFilter.selected]
    | cons value values =>
      cases bit <;> simp only [DelimitedBinaryWordBooleanFilter.selected,Bool.false_eq_true,
        if_false,if_true,List.nil_append,List.singleton_append]
      · exact (ih values).cons _
      · exact (ih values).cons_cons _

theorem selectedTiles_nodup (t : Tromino) (cells : List Cell) (bits : List Bool) :
    (selectedTiles t cells bits).Nodup :=
  (List.nodup_dedup (FiniteRegion.candidateList t cells)).sublist (selected_sublist bits _)

theorem selectedTiles_candidate (t : Tromino) (cells : List Cell) (bits : List Bool) :
    (selectedTiles t cells bits).toFinset⊆candidates t cells.toFinset := by
  intro tile member
  exact (mem_candidateTiles t cells tile).mp
    ((selected_sublist bits _).subset (List.mem_toFinset.mp member))

theorem flatten_nodup_iff (tiles : List (Finset Cell)) (nodup : tiles.Nodup) :
    (tiles.flatMap footprintWords).Nodup ↔
      ∀ first∈tiles, ∀ second∈tiles, ∀ cell∈first, cell∈second → first=second := by
  letI : Std.Symm (fun first second : Finset Cell => List.Disjoint (footprintWords first) (footprintWords second)) :=
    ⟨fun _ _ h => h.symm⟩
  rw [List.nodup_flatMap]
  constructor
  · rintro ⟨_,pairwise⟩ first hf second hs cell hc hd
    by_contra different
    have disjoint := pairwise.forall hf hs different
    exact List.disjoint_left.mp disjoint (mem_footprintWords first cell |>.mpr hc)
      (mem_footprintWords second cell |>.mpr hd)
  · intro nonoverlap
    refine ⟨fun tile _ => footprintWords_nodup tile,?_⟩
    apply List.pairwise_iff_get.mpr
    intro i j ordered
    apply List.disjoint_left.mpr
    intro word first second
    obtain ⟨cell,hc,equal⟩ := word_of_footprint (tiles.get i) word first
    have hd : cell∈tiles.get j := (mem_footprintWords _ _).mp (equal ▸ second)
    have same := nonoverlap _ (List.get_mem _ _) _ (List.get_mem _ _) cell hc hd
    have indices := (List.nodup_iff_injective_get.mp nodup) same
    exact (ne_of_lt ordered) indices

def nativeRequest (t : Tromino) (cells : List Cell) (prefill : List (Finset Cell))
    (bits : List Bool) : FiniteExactCoverVerifier.Request where
  region := cells.map cellWord
  candidates := (candidateTiles t cells).map footprintWords
  required := prefill.map footprintWords
  bits := bits

theorem native_selected (t : Tromino) (cells : List Cell) (prefill : List (Finset Cell))
    (bits : List Bool) :
    (nativeRequest t cells prefill bits).selected=(selectedTiles t cells bits).map footprintWords := by
  exact FiniteExactCoverVerifier.selected_map footprintWords bits _

def check (strict : Bool) (t : Tromino) (cells : List Cell) (prefill : List (Finset Cell))
    (bits : List Bool) : Bool := FiniteExactCoverVerifier.check strict (nativeRequest t cells prefill bits)

theorem check_correct (strict : Bool) (t : Tromino) (cells : List Cell)
    (prefill : List (Finset Cell)) (bits : List Bool) :
    check strict t cells prefill bits=true ↔
      Valid t cells.toFinset prefill.toFinset (selectedTiles t cells bits).toFinset ∧
      (strict=true → ∀ tile∈selectedTiles t cells bits, tile⊆cells.toFinset) := by
  rw [check,FiniteExactCoverVerifier.check_correct,native_selected]
  simp only [nativeRequest,← List.flatMap_def,List.map_map,Function.comp_def]
  rw [flatten_nodup_iff _ (selectedTiles_nodup t cells bits)]
  have cover :
      (∀ word∈cells.map cellWord, word∈(selectedTiles t cells bits).flatMap footprintWords) ↔
      ∀ cell∈cells.toFinset, ∃ tile∈(selectedTiles t cells bits).toFinset, cell∈tile := by
    constructor
    · intro h cell hc
      obtain ⟨tile,ht,hw⟩ := List.mem_flatMap.mp
        (h (cellWord cell) (List.mem_map.mpr ⟨cell,List.mem_toFinset.mp hc,rfl⟩))
      exact ⟨tile,List.mem_toFinset.mpr ht,(mem_footprintWords _ _).mp hw⟩
    · intro h word hw
      obtain ⟨cell,hc,rfl⟩ := List.mem_map.mp hw
      obtain ⟨tile,ht,covers⟩ := h cell (List.mem_toFinset.mpr hc)
      exact List.mem_flatMap.mpr ⟨tile,List.mem_toFinset.mp ht,(mem_footprintWords _ _).mpr covers⟩
  have retained :
      (∀ block∈prefill.map footprintWords,
        BinaryWordBlocks.pack block∈(selectedTiles t cells bits).map (fun tile => BinaryWordBlocks.pack (footprintWords tile))) ↔
      prefill.toFinset⊆(selectedTiles t cells bits).toFinset := by
    simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,
      List.mem_toFinset,Finset.subset_iff]
    constructor
    · intro h tile ht
      obtain ⟨other,ho,equal⟩ := h tile ht
      exact tileKey_injective equal ▸ ho
    · intro h tile ht
      exact ⟨tile,h ht,rfl⟩
  have inside :
      (∀ word∈(selectedTiles t cells bits).flatMap footprintWords, word∈cells.map cellWord) ↔
      ∀ tile∈selectedTiles t cells bits, tile⊆cells.toFinset := by
    constructor
    · intro h tile ht cell hc
      obtain ⟨other,ho,equal⟩ := List.mem_map.mp
        (h (cellWord cell) (List.mem_flatMap.mpr ⟨tile,ht,(mem_footprintWords _ _).mpr hc⟩))
      exact List.mem_toFinset.mpr (cellWord_injective equal ▸ ho)
    · intro h word hw
      obtain ⟨tile,ht,member⟩ := List.mem_flatMap.mp hw
      obtain ⟨cell,hc,rfl⟩ := word_of_footprint tile word member
      exact List.mem_map.mpr ⟨cell,List.mem_toFinset.mp (h tile ht hc),rfl⟩
  rw [cover,retained,inside]
  simp only [Valid,List.mem_toFinset]
  have candidate := selectedTiles_candidate t cells bits
  tauto

theorem selected_filter {Value : Type} [DecidableEq Value] (values : List Value)
    (tiles : Finset Value) :
    DelimitedBinaryWordBooleanFilter.selected (values.map fun value => decide (value∈tiles)) values=
      values.filter (fun value => decide (value∈tiles)) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    by_cases member : value∈tiles <;> simp [DelimitedBinaryWordBooleanFilter.selected,member,ih]

theorem encode_valid (strict : Bool) (t : Tromino) (cells : List Cell) (prefill : List (Finset Cell))
    (tiles : Finset (Finset Cell)) (valid : Valid t cells.toFinset prefill.toFinset tiles)
    (inside : strict=true → ∀ tile∈tiles, tile⊆cells.toFinset) :
    ∃ bits : List Bool, bits.length≤24*cells.length ∧ check strict t cells prefill bits=true := by
  let bits := (candidateTiles t cells).map fun tile => decide (tile∈tiles)
  have selected : (selectedTiles t cells bits).toFinset=tiles := by
    unfold selectedTiles bits
    rw [selected_filter]
    ext tile
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,mem_candidateTiles]
    exact ⟨fun h => h.2,fun h => ⟨valid.1 h,h⟩⟩
  refine ⟨bits,?_,(check_correct strict t cells prefill bits).mpr ⟨?_,?_⟩⟩
  · simpa [bits] using candidateTiles_length_le t cells
  · simpa [selected] using valid
  · intro hs tile member
    exact inside hs tile (selected ▸ List.mem_toFinset.mpr member)

theorem tileable_iff_certificate (t : Tromino) (cells : List Cell) :
    t.Tileable (cells.toFinset : Set Cell) ↔
      ∃ bits : List Bool, bits.length≤24*cells.length ∧ check true t cells [] bits=true := by
  rw [FiniteRegion.tileable_iff_valid]
  constructor
  · rintro ⟨tiles,valid⟩
    exact encode_valid true t cells [] tiles valid.1 (fun _ => valid.2)
  · rintro ⟨bits,_,checked⟩
    obtain ⟨valid,inside⟩ := (check_correct true t cells [] bits).mp checked
    exact ⟨_,valid,fun tile ht => inside rfl tile (List.mem_toFinset.mp ht)⟩

theorem completion_iff_certificate (t : Tromino) (r : Nat) (prefill : List (Finset Cell))
    (meets : ∀ tile∈prefill, ∃ cell∈box r, cell∈tile) :
    t.Completable Set.univ (prefill.toFinset : Set (Finset Cell)) ↔
      ∃ bits : List Bool, bits.length≤24*(2*r+1)^2 ∧ check false t (boxList r) prefill bits=true := by
  constructor
  · intro completion
    obtain ⟨tiles,valid⟩ := of_completion t (box r) prefill.toFinset
      (by simpa using meets) completion
    obtain ⟨bits,bound,checked⟩ := encode_valid false t (boxList r) prefill tiles
      (by simpa using valid) (by simp)
    exact ⟨bits,by simpa using bound,checked⟩
  · rintro ⟨bits,_,checked⟩
    have valid := ((check_correct false t (boxList r) prefill bits).mp checked).1
    exact completion_of_witness t (by simpa using valid)

/-- The canonical-box statement requires no well-formedness assumption on
the supplied preplacements. Malformed footprints are rejected. -/
theorem completion_iff_bounded_certificate (t : Tromino) (prefill : List (Finset Cell)) :
    t.Completable Set.univ (prefill.toFinset : Set (Finset Cell)) ↔
      ∃ bits : List Bool, bits.length≤24*(2*radius prefill.toFinset+1)^2 ∧
        check false t (boxList (radius prefill.toFinset)) prefill bits=true := by
  constructor
  · intro completion
    exact (completion_iff_certificate t (radius prefill.toFinset) prefill
      (by simpa using completion_meets_box t prefill.toFinset completion)).mp completion
  · rintro ⟨bits,_,checked⟩
    have valid := ((check_correct false t (boxList (radius prefill.toFinset)) prefill bits).mp checked).1
    exact completion_of_witness t (by simpa using valid)

structure Input where
  cells : List Cell
  prefill : List (Finset Cell)

def preparedEncoding (t : Tromino) (input : Input × List Bool) : List FiniteExactCoverVerifier.Token :=
  (nativeRequest t input.1.cells input.1.prefill input.2).encode

/-- The geometric verifier runs in polynomial time once its explicit
candidate-table request has been emitted. -/
noncomputable def computableInPolyTime (strict : Bool) (t : Tromino) :
    TM2ComputableInPolyTime (preparedEncoding t) (fun bit : Bool => [bit])
      (fun input => check strict t input.1.cells input.1.prefill input.2) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    (fun input => nativeRequest t input.1.cells input.1.prefill input.2)
    (FiniteExactCoverVerifier.computableInPolyTime strict) (fun _ => rfl) (fun _ => rfl)

end LeanTrominoes.Tromino.FiniteVerifier
