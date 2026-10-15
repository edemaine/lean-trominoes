/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteCoordinateColumns
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoSortedFootprints

/-! # Compiling vertex codes for the finite candidate table -/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open EncodedUnaryColumn

abbrev Local := SquareSymmetry × Cell
abbrev Row := Cell × Local

def localTable (t : Tromino) : List Local :=
  FiniteRegion.symmetries.flatMap fun symmetry =>
    (FiniteRegion.baseCells t).map fun source => (symmetry,source)

def candidateRows (t : Tromino) (input : Input × List Bool) : List Row :=
  input.1.cells.flatMap fun cell => (localTable t).map fun entry => (cell,entry)

def candidatePlacement (row : Row) : Placement Unit :=
  ⟨(),row.2.1,Cell.sub row.1 (row.2.1.act row.2.2)⟩

def delta (t : Tromino) (i : Fin 3) (entry : Local) : Cell :=
  Cell.sub (entry.1.act (FiniteVerifier.vertex t i)) (entry.1.act entry.2)

private def liftedX (t : Tromino) :
    Compiler encode (candidateRows t) (fun _ row => Encodable.encode row.1.1) :=
  cartesianLeft regionX (table (localTable t) (fun _ => 0))

private def liftedY (t : Tromino) :
    Compiler encode (candidateRows t) (fun _ row => Encodable.encode row.1.2) :=
  cartesianLeft regionY (table (localTable t) (fun _ => 0))

private def offsetColumn (t : Tromino) (i : Fin 3) (value : Cell → Nat) :
    Compiler encode (candidateRows t) (fun _ row => value (delta t i row.2)) :=
  cartesianRight regionX (table (localTable t) (fun entry => value (delta t i entry)))

private theorem translate (z d : Int) :
    ((positive (Encodable.encode z)+d.toNat : Nat):Int)-
      (negative (Encodable.encode z)+(-d).toNat)=z+d := by
  rw [positive_encode,negative_encode]
  omega

private def translatedX (t : Tromino) (i : Fin 3) :
    Compiler encode (candidateRows t)
      (fun _ row => Encodable.encode (row.1.1+(delta t i row.2).1)) := by
  let computed := signedDifference
    (add (signedPositive (liftedX t)) (offsetColumn t i (fun d => d.1.toNat)))
    (add (signedNegative (liftedX t)) (offsetColumn t i (fun d => (-d.1).toNat)))
  apply computed.of_eq
  intro input
  apply List.map_congr_left
  intro row _
  exact congrArg Encodable.encode (translate row.1.1 (delta t i row.2).1)

private def translatedY (t : Tromino) (i : Fin 3) :
    Compiler encode (candidateRows t)
      (fun _ row => Encodable.encode (row.1.2+(delta t i row.2).2)) := by
  let computed := signedDifference
    (add (signedPositive (liftedY t)) (offsetColumn t i (fun d => d.2.toNat)))
    (add (signedNegative (liftedY t)) (offsetColumn t i (fun d => (-d.2).toNat)))
  apply computed.of_eq
  intro input
  apply List.map_congr_left
  intro row _
  exact congrArg Encodable.encode (translate row.1.2 (delta t i row.2).2)

noncomputable def candidateVertexCode (t : Tromino) (i : Fin 3) :
    Compiler encode (candidateRows t)
      (fun _ row => FiniteVerifier.vertexCode t (candidatePlacement row) i) := by
  let computed := pair (translatedX t i) (translatedY t i)
  apply computed.of_eq
  intro input
  apply List.map_congr_left
  intro row _
  change Nat.pair (Encodable.encode _) (Encodable.encode _) = Encodable.encode _
  change Nat.pair (Encodable.encode _) (Encodable.encode _) =
    Nat.pair (Encodable.encode _) (Encodable.encode _)
  congr 2 <;> simp [FiniteVerifier.placedVertex,candidatePlacement,delta,Cell.add,Cell.sub] <;> omega

noncomputable def candidateSortedCodes (t : Tromino) :
    TM2ComputableInPolyTime encode UnaryFieldEncoderMachine.unaryFields
      (fun input => (candidateRows t input).flatMap fun row =>
        UnarySortedTriple.sorted
          (FiniteVerifier.vertexCode t (candidatePlacement row) 0)
          (FiniteVerifier.vertexCode t (candidatePlacement row) 1)
          (FiniteVerifier.vertexCode t (candidatePlacement row) 2)) :=
  sortedTriples (candidateVertexCode t 0) (candidateVertexCode t 1) (candidateVertexCode t 2)

end LeanTrominoes.Tromino.FiniteCoordinateColumns
