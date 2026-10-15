/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.FiniteTrominoCompletionInNP
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnMaximum

/-! # Computing the canonical completion radius from placement columns -/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing UnaryColumn FiniteVerifier
set_option maxHeartbeats 3000000
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (prefill : List Symbol → List (Placement Unit))
    (cs : Compiler prefill (fun _ p => CompletionStripEncoding.symmetryCode p.symmetry))
    (cx : Compiler prefill (fun _ p => Encodable.encode p.offset.1))
    (cy : Compiler prefill (fun _ p => Encodable.encode p.offset.2))

private def vertexRows (s : List Symbol) : List (Placement Unit × Fin 3) :=
  (prefill s).flatMap fun p => (List.finRange 3).map fun i => (p,i)

private def displacementCompiler (t : Tromino) (value : Cell → Nat) :
    Compiler (vertexRows prefill) (fun _ row => value (row.1.symmetry.act (vertex t row.2))) := by
  let indices := table (Symbol := Symbol) (List.finRange 3) (fun i => i.val)
  let syms := cartesianLeft cs indices
  let verts := cartesianRight cs indices
  let keys := add syms (scale verts 8)
  let data := (List.finRange 3).flatMap fun i =>
    FiniteRegion.symmetries.map fun symmetry => value (symmetry.act (vertex t i))
  let result := lookup keys data (by
    intro s row member
    have lt := row.2.isLt
    have sym : CompletionStripEncoding.symmetryCode row.1.symmetry<8 := by
      cases row.1.symmetry <;> decide
    have length : data.length=24 := by simp [data,FiniteRegion.symmetries,List.finRange]
    rw [length]
    omega)
  apply result.of_eq
  intro s
  apply List.map_congr_left
  intro row _
  rcases row with ⟨p,i⟩
  fin_cases i <;> cases h : p.symmetry <;>
    simp [data,FiniteRegion.symmetries,CompletionStripEncoding.symmetryCode,List.finRange,h]

private def coordinateCompiler (t : Tromino) (horizontal : Bool) :
    Compiler (vertexRows prefill) (fun _ row => Encodable.encode
      (if horizontal then (placedVertex t row.1 row.2).1 else (placedVertex t row.1 row.2).2)) := by
  let indices := table (Symbol := Symbol) (List.finRange 3) (fun i => i.val)
  let offset : Compiler (vertexRows prefill) (fun _ row => Encodable.encode
      (if horizontal then row.1.offset.1 else row.1.offset.2)) := by
    cases horizontal
    · exact cartesianLeft cy indices
    · exact cartesianLeft cx indices
  let coord : Cell → Int := fun c => if horizontal then c.1 else c.2
  let positive := add (EncodedUnaryColumn.signedPositive offset)
    (displacementCompiler prefill cs t (fun c => (coord c).toNat))
  let negative := add (EncodedUnaryColumn.signedNegative offset)
    (displacementCompiler prefill cs t (fun c => (-coord c).toNat))
  let result := signedDifference positive negative
  apply result.of_eq
  intro s
  apply List.map_congr_left
  intro row _
  apply congrArg Encodable.encode
  simp only [positive_encode,negative_encode]
  cases horizontal <;> simp [coord,placedVertex,Cell.add] <;> omega

private theorem vertexRows_cells (t : Tromino) (ps : List (Placement Unit)) :
    ((completionFootprints t ps).toFinset.biUnion id)=
      (ps.flatMap fun p => (List.finRange 3).map fun i => placedVertex t p i).toFinset := by
  ext c
  have range : List.finRange 3=([0,1,2] : List (Fin 3)) := by decide
  cases t <;> simp [completionFootprints,Finset.mem_biUnion,List.mem_flatMap,List.mem_map,
    range,placedVertex,vertex,Placement.cells,Tromino.cells,Finset.mem_image] <;> aesop

/-- The maximum is over actual preplaced cells, so this emits exactly the
canonical radius used by the completion encoding. -/
def prefillRadiusCompiler (t : Tromino) :
    ScalarCompiler (fun s => FiniteWitness.radius (completionFootprints t (prefill s)).toFinset) := by
  let xs := coordinateCompiler prefill cs cx cy t true
  let ys := coordinateCompiler prefill cs cx cy t false
  let ax := add (EncodedUnaryColumn.signedPositive xs) (EncodedUnaryColumn.signedNegative xs)
  let ay := add (EncodedUnaryColumn.signedPositive ys) (EncodedUnaryColumn.signedNegative ys)
  let magnitude := add ax (sub ay ax)
  let result := maximum magnitude
  apply result.of_eq
  intro s
  dsimp only
  apply congrArg (fun n : Nat => [n])
  rw [FiniteWitness.radius,vertexRows_cells]
  have mapEq : (vertexRows prefill s).map (fun row =>
      positive (Encodable.encode (placedVertex t row.1 row.2).1)+negative (Encodable.encode (placedVertex t row.1 row.2).1)+
      (positive (Encodable.encode (placedVertex t row.1 row.2).2)+negative (Encodable.encode (placedVertex t row.1 row.2).2)-
      (positive (Encodable.encode (placedVertex t row.1 row.2).1)+negative (Encodable.encode (placedVertex t row.1 row.2).1))))=
      ((prefill s).flatMap fun p => (List.finRange 3).map fun i => placedVertex t p i).map
        (fun c => max c.1.natAbs c.2.natAbs) := by
    simp only [vertexRows,List.map_flatMap,List.map_map,Function.comp_def]
    apply congrArg ((prefill s).flatMap)
    funext p
    apply List.map_congr_left
    intro i _
    rw [positive_encode,negative_encode,positive_encode,negative_encode]
    omega
  change ((vertexRows prefill s).map _).toFinset.sup id=_
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [mapEq]
  generalize ((prefill s).flatMap fun p => (List.finRange 3).map fun i => placedVertex t p i)=cells
  induction cells with
  | nil => simp
  | cons c cells ih => simpa using congrArg (max (max c.1.natAbs c.2.natAbs)) ih
end LeanTrominoes.Tromino.FiniteCoordinateColumns
