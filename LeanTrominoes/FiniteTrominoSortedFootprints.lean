/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnarySortedTripleCompiler
import LeanTrominoes.FiniteTrominoVerifierBackend

/-! # Canonical footprint names from three placed vertex codes -/
namespace LeanTrominoes.Tromino.FiniteVerifier

def vertex (t : Tromino) : Fin 3 → Cell
  | 0 => (0,0)
  | 1 => (1,0)
  | 2 => if t=.I then (2,0) else (0,1)

def placedVertex (t : Tromino) (p : Placement Unit) (i : Fin 3) : Cell :=
  Cell.add p.offset (p.symmetry.act (vertex t i))

def vertexCode (t : Tromino) (p : Placement Unit) (i : Fin 3) : Nat :=
  Encodable.encode (placedVertex t p i)

def vertexCodes (t : Tromino) (p : Placement Unit) : List Nat :=
  [vertexCode t p 0,vertexCode t p 1,vertexCode t p 2]

theorem vertexCodes_nodup (t : Tromino) (p : Placement Unit) : (vertexCodes t p).Nodup := by
  have base : (FiniteRegion.baseCells t).Nodup := by cases t <;> decide
  have mapped := base.map (Encodable.encode_injective.comp (Placement.cellMap_injective p))
  cases t <;> simpa [FiniteRegion.baseCells,vertexCodes,vertexCode,placedVertex,vertex] using mapped

theorem vertexCodes_toFinset (t : Tromino) (p : Placement Unit) :
    (vertexCodes t p).toFinset=(p.cells (fun _ => t.cells)).image Encodable.encode := by
  cases t <;> simp [vertexCodes,vertexCode,placedVertex,vertex,Placement.cells,Tromino.cells,
    Finset.image_insert,Finset.image_singleton]

def footprintCodes (tile : Finset Cell) : List Nat :=
  (tile.image Encodable.encode).sort (·≤·)

def footprintCode (tile : Finset Cell) (i : Fin 3) : Nat :=
  (footprintCodes tile)[i.val]?.getD 0

theorem footprintCodes_placed (t : Tromino) (p : Placement Unit) :
    footprintCodes (p.cells (fun _ => t.cells)) =
      UnarySortedTriple.sorted (vertexCode t p 0) (vertexCode t p 1) (vertexCode t p 2) := by
  unfold footprintCodes
  rw [← vertexCodes_toFinset]
  exact (UnarySortedTriple.sorted_eq_finset_sort _ _ _ (vertexCodes_nodup t p)).symm

theorem footprintWords_placed (t : Tromino) (p : Placement Unit) :
    footprintWords (p.cells (fun _ => t.cells)) =
      (UnarySortedTriple.sorted (vertexCode t p 0) (vertexCode t p 1) (vertexCode t p 2)).map
        _root_.Computability.encodeNat := by
  unfold footprintWords
  rw [← vertexCodes_toFinset]
  congr 1
  exact (UnarySortedTriple.sorted_eq_finset_sort _ _ _ (vertexCodes_nodup t p)).symm

end LeanTrominoes.Tromino.FiniteVerifier
