/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCandidateTableCompiler

/-! # Canonical preplacement footprint emission from unary coordinates -/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open EncodedUnaryColumn FiniteVerifier

private def symmetryVertexColumn (t : Tromino) (i : Fin 3) (value : Cell → Nat) :
    Compiler encode (fun input => input.1.prefill)
      (fun _ p => value (p.symmetry.act (vertex t i))) := by
  let computed := lookup prefillSymmetry
    (FiniteRegion.symmetries.map fun symmetry => value (symmetry.act (vertex t i)))
    (fun input p _ => by cases p.symmetry <;>
      simp [CompletionStripEncoding.symmetryCode,FiniteRegion.symmetries])
  apply computed.of_eq
  intro input
  apply List.map_congr_left
  intro p _
  cases h : p.symmetry <;> simp [h,FiniteRegion.symmetries,CompletionStripEncoding.symmetryCode]

private theorem translateOffset (z d : Int) :
    ((positive (Encodable.encode z)+d.toNat : Nat):Int)-
      (negative (Encodable.encode z)+(-d).toNat)=z+d := by
  rw [positive_encode,negative_encode]
  omega

private def prefillVertexX (t : Tromino) (i : Fin 3) :
    Compiler encode (fun input => input.1.prefill)
      (fun _ p => Encodable.encode (p.offset.1+(p.symmetry.act (vertex t i)).1)) := by
  let computed := signedDifference
    (add (signedPositive prefillX) (symmetryVertexColumn t i (fun d => d.1.toNat)))
    (add (signedNegative prefillX) (symmetryVertexColumn t i (fun d => (-d.1).toNat)))
  exact computed.of_eq (fun input => List.map_congr_left (fun p _ =>
    congrArg Encodable.encode (translateOffset p.offset.1 (p.symmetry.act (vertex t i)).1)))

private def prefillVertexY (t : Tromino) (i : Fin 3) :
    Compiler encode (fun input => input.1.prefill)
      (fun _ p => Encodable.encode (p.offset.2+(p.symmetry.act (vertex t i)).2)) := by
  let computed := signedDifference
    (add (signedPositive prefillY) (symmetryVertexColumn t i (fun d => d.2.toNat)))
    (add (signedNegative prefillY) (symmetryVertexColumn t i (fun d => (-d.2).toNat)))
  exact computed.of_eq (fun input => List.map_congr_left (fun p _ =>
    congrArg Encodable.encode (translateOffset p.offset.2 (p.symmetry.act (vertex t i)).2)))

private def prefillVertexCode (t : Tromino) (i : Fin 3) :
    Compiler encode (fun input => input.1.prefill) (fun _ p => vertexCode t p i) :=
  pair (prefillVertexX t i) (prefillVertexY t i)

def prefillTableComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime encode DelimitedBinaryWords.encode
      (fun input => ⟨input.1.prefill.map fun p => tileKey (p.cells (fun _ => t.cells))⟩) := by
  let a := prefillVertexCode t 0
  let b := prefillVertexCode t 1
  let c := prefillVertexCode t 2
  let computed := packedTriples (sortedLow a b c) (sortedMiddle a b c) (sortedHigh a b c)
  apply computed.of_eq
  intro input
  congr 1
  apply List.map_congr_left
  intro p _
  simp [tileKey,footprintWords_placed,UnarySortedTriple.sorted]

end LeanTrominoes.Tromino.FiniteCoordinateColumns
