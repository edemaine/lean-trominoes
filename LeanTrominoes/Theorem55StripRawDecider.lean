/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripRawTransition
import LeanTrominoes.PolyominoConnectivityPacked
import LeanTrominoes.PolyominoStripIndexedSearch

/-! # Strip decision by natural-record transitions and streamed cuts -/

namespace LeanTrominoes.PolyominoStripWindow.Raw

def tilingCheck (cells : Bool → List Cell) (height bound : Nat) : Bool :=
  FiniteState.cycleSearchIndexDFSBoolAtDepth (2 ^ stateBits Bool height bound)
    (stateBits Bool height bound) (check cells height bound)

theorem tilingCheck_correct (cells : Bool → List Cell) (height bound : Nat)
    (bounded : Bounded (tiles cells) bound) :
    tilingCheck cells height bound = true ↔ Tileable (tiles cells) (horizontalStrip height) := by
  have eq : check cells height bound =
      (fun a b => decide (packedTransition (tiles cells) height bound a b)) := by
    funext a b
    apply Bool.eq_iff_iff.mpr
    simpa using check_correct cells height bound a b
  rw [tilingCheck,eq]
  exact indexedTilingCheck_correct (tiles cells) height bound bounded

end LeanTrominoes.PolyominoStripWindow.Raw

namespace LeanTrominoes.Theorem55StripDecider

/-- A fixed executable list for the 15-omino. -/
def smallCells : List Cell :=
  [(-1,0),(0,0),(1,0),(0,1),(0,-1),(2,0),(3,0),(4,0),(3,1),(3,-1),
    (5,0),(6,0),(7,0),(6,1),(6,-1)]

theorem smallCells_toFinset : smallCells.toFinset = PlusRefinement.bumpy := by decide

def rawCells (input : Theorem55.StripInput) (kind : Bool) : List Cell :=
  if kind then input.2 else smallCells

theorem rawCells_tiles (input : Theorem55.StripInput) :
    PolyominoStripWindow.Raw.tiles (rawCells input) = pairTiles PlusRefinement.bumpy input.2.toFinset := by
  funext kind
  cases kind <;> simp [PolyominoStripWindow.Raw.tiles,rawCells,pairTiles,smallCells_toFinset]

def decideStripRaw (input : Theorem55.StripInput) : Bool :=
  decide (0 < input.1) && decide (input.2 ≠ []) &&
    PolyominoConnectivitySearch.disconnectedPacked input.2 &&
      PolyominoStripWindow.Raw.tilingCheck (rawCells input) input.1 (bound input)

theorem decideStripRaw_correct (input : Theorem55.StripInput) :
    decideStripRaw input = true ↔ Theorem55.stripProblem input := by
  have bounded : PolyominoStripWindow.Bounded (PolyominoStripWindow.Raw.tiles (rawCells input)) (bound input) := by
    rw [rawCells_tiles]
    exact tiles_bounded input
  simp only [decideStripRaw,Bool.and_eq_true,decide_eq_true_eq,
    PolyominoStripWindow.Raw.tilingCheck_correct _ _ _ bounded,rawCells_tiles]
  by_cases nonempty : input.2 = []
  · simp [nonempty,Theorem55.stripProblem]
  · rw [PolyominoConnectivitySearch.disconnectedPacked_correct _ nonempty]
    simp [Theorem55.stripProblem,nonempty,and_assoc]

/-- Only polynomially many placement records are enumerated by the edge checker. -/
theorem raw_keys_length_le (input : Theorem55.StripInput) :
    (PolyominoStripWindow.Raw.keys input.1 (bound input)).length ≤
      statePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length := by
  rw [PolyominoStripWindow.Raw.keys_length]
  exact stateBits_le input

theorem cellCount_le_encoding_length (input : Theorem55.StripInput) :
    input.2.length ≤ (Theorem55StripEncoding.finEncoding.encode input).length := by
  rw [Theorem55StripEncoding.encoding_length]
  simp only [Theorem55StripEncoding.fields,List.sum_append,List.sum_cons,List.sum_nil]
  omega

/-- A streamed cut candidate needs at most one bit per input cell. -/
theorem cut_mask_bits_le (input : Theorem55.StripInput) (word : Nat)
    (below : word < 2^input.2.length) :
    (Computability.encodeNat word).length ≤ (Theorem55StripEncoding.finEncoding.encode input).length :=
  (FiniteState.encodeNat_length_le_of_lt_pow _ _ below).trans (cellCount_le_encoding_length input)

end LeanTrominoes.Theorem55StripDecider
