/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCandidateColumns
import LeanTrominoes.CompiledBinaryTripleBlocks
import LeanTrominoes.BinaryWordRepresentativeColumns

/-! # An actual polynomial-time candidate-footprint table emitter -/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open EncodedUnaryColumn FiniteVerifier

def rowTile (t : Tromino) (row : Row) : Finset Cell :=
  (candidatePlacement row).cells (fun _ => t.cells)

theorem candidateRows_tiles (t : Tromino) (input : Input × List Bool) :
    (candidateRows t input).map (rowTile t)=FiniteRegion.candidateList t input.1.cells := by
  simp [candidateRows,localTable,rowTile,candidatePlacement,FiniteRegion.candidateList,
    FiniteRegion.coveringList,List.map_flatMap,List.map_map,Function.comp_def]

private def orderedVertex (t : Tromino) (i : Fin 3) :
    Compiler encode (candidateRows t) (fun _ row => footprintCode (rowTile t row) i) := match i with
  | 0 => by exact (sortedLow (candidateVertexCode t 0) (candidateVertexCode t 1)
      (candidateVertexCode t 2)).of_eq (fun input => List.map_congr_left (fun row _ => by
      simp [footprintCode,rowTile,footprintCodes_placed,UnarySortedTriple.sorted]))
  | 1 => by exact (sortedMiddle (candidateVertexCode t 0) (candidateVertexCode t 1)
      (candidateVertexCode t 2)).of_eq (fun input => List.map_congr_left (fun row _ => by
      simp [footprintCode,rowTile,footprintCodes_placed,UnarySortedTriple.sorted]))
  | 2 => by exact (sortedHigh (candidateVertexCode t 0) (candidateVertexCode t 1)
      (candidateVertexCode t 2)).of_eq (fun input => List.map_congr_left (fun row _ => by
      simp [footprintCode,rowTile,footprintCodes_placed,UnarySortedTriple.sorted]))

private def candidateCode (t : Tromino) (i : Fin 3) :
    Compiler encode (fun input => FiniteRegion.candidateList t input.1.cells)
      (fun _ tile => footprintCode tile i) := by
  apply (orderedVertex t i).of_eq
  intro input
  dsimp only
  rw [← candidateRows_tiles t input]
  simp [List.map_map]

private theorem tripleKey_placed (t : Tromino) (p : Placement Unit) :
    BinaryWordBlocks.pack [encodeNat (footprintCode (p.cells (fun _ => t.cells)) 0),
      encodeNat (footprintCode (p.cells (fun _ => t.cells)) 1),
      encodeNat (footprintCode (p.cells (fun _ => t.cells)) 2)] =
      tileKey (p.cells (fun _ => t.cells)) := by
  simp [footprintCode,footprintCodes_placed,UnarySortedTriple.sorted,tileKey,footprintWords_placed]

private def rawCandidateNames (t : Tromino) :
    TM2ComputableInPolyTime encode DelimitedBinaryWords.encode
      (fun input => ⟨(FiniteRegion.candidateList t input.1.cells).map tileKey⟩) := by
  let computed := packedTriples (candidateCode t 0) (candidateCode t 1) (candidateCode t 2)
  apply computed.of_eq
  intro input
  congr 1
  apply List.map_congr_left
  intro tile member
  obtain ⟨cell,hc,hm⟩ := List.mem_flatMap.mp member
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  exact tripleKey_placed t p

private def uniqueCandidateCode (t : Tromino) (i : Fin 3) :
    Compiler encode (fun input => candidateTiles t input.1.cells)
      (fun _ tile => footprintCode tile i) :=
  binaryNamedDedup (rawCandidateNames t) (candidateCode t i) (fun _ => tileKey_injective)

/-- Canonical packed footprints, in the backend's stable deduplicated order. -/
def candidateTableComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime encode DelimitedBinaryWords.encode
      (fun input => ⟨(candidateTiles t input.1.cells).map tileKey⟩) := by
  let computed := packedTriples (uniqueCandidateCode t 0) (uniqueCandidateCode t 1)
    (uniqueCandidateCode t 2)
  apply computed.of_eq
  intro input
  congr 1
  apply List.map_congr_left
  intro tile member
  have raw := List.mem_dedup.mp member
  obtain ⟨cell,hc,hm⟩ := List.mem_flatMap.mp raw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  exact tripleKey_placed t p

end LeanTrominoes.Tromino.FiniteCoordinateColumns
