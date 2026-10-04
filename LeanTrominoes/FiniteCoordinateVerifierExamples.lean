/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCompletionInNP

/-! # Boundary examples for native finite coordinate verification -/
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns

example : UnarySortedTriple.sorted 8 0 3=[0,3,8] := by decide +kernel
example : UnarySortedTriple.sorted 0 0 0=[0,0,0] := by decide +kernel

#guard BinaryWordTripleBlocks.tokens
    (DelimitedBinaryWords.encode ⟨[[],[false,true],[]]⟩) =
  DelimitedBinaryWords.encode ⟨[BinaryWordBlocks.pack [[],[false,true],[]]]⟩

#guard (decodeInput (encodeInput ⟨[(-1,2),(0,-2)],
    [⟨(),.reflectAntidiagonal,(-2,1)⟩]⟩)).map (fun input => (input.cells,input.prefill)) =
  some ([(-1,2),(0,-2)],[⟨(),.reflectAntidiagonal,(-2,1)⟩])

#guard positive (Encodable.encode (-3 : Int))=0 ∧
  negative (Encodable.encode (-3 : Int))=3

#guard FiniteVerifier.tileKey
    ((⟨(),.identity,(0,0)⟩ : Placement Unit).cells (fun _ => Tromino.I.cells)) =
  FiniteVerifier.tileKey
    ((⟨(),.rotate180,(2,0)⟩ : Placement Unit).cells (fun _ => Tromino.I.cells))

#guard (candidateRows .L (⟨[(0,0),(0,0)],[]⟩,[])).length=48
#guard (FiniteVerifier.candidateTiles .L [(0,0),(0,0)]).length=
  (FiniteVerifier.candidateTiles .L [(0,0)]).length

end LeanTrominoes.Tromino.FiniteCoordinateColumns
