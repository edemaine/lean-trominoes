/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATCoverIndex

/-! # Cover construction with indexed-RAM operation accounting

One arithmetic operation, array access, list-cell construction, or list-cell
traversal costs one unit. Base-M encoding and decoding use at most d digit
operations, each with at most d multiplications to obtain the digit power.
The conservative index charge below includes both endpoint encodings, offset
wrapping and addition, and the loop/record operations. The counters are ghost
costs, not Lean VM runtime measurements.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph
variable {n d M : Nat} [NeZero M]

def indexCharge (d : Nat) : Nat := 20*(d+1)^2

def emitRow (z : CoverLattice d M) : List (Arc (Signed (Fin n)) d) →
    List (Fin (n*2*M^d) × Fin (n*2*M^d)) × Nat
  | [] => ([],1)
  | e :: es =>
    let rest := emitRow z es
    ((coverIndex n d M (e.source,z),coverIndex n d M (e.target,z+wrap M e.offset)) :: rest.1,
      indexCharge d+rest.2+3)

theorem emitRow_value (z : CoverLattice d M) (es : List (Arc (Signed (Fin n)) d)) :
    (emitRow z es).1=es.map (fun e => (coverIndex n d M (e.source,z),coverIndex n d M (e.target,z+wrap M e.offset))) := by
  induction es <;> simp_all [emitRow]

theorem emitRow_cost (z : CoverLattice d M) (es : List (Arc (Signed (Fin n)) d)) :
    (emitRow z es).2=es.length*(indexCharge d+3)+1 := by
  induction es <;> simp_all [emitRow] <;> ring

def emitRows (es : List (Arc (Signed (Fin n)) d)) : List (Fin (M^d)) →
    List (Fin (n*2*M^d) × Fin (n*2*M^d)) × Nat
  | [] => ([],1)
  | i :: indices =>
    let row := emitRow ((coordinateIndex d M).symm i) es
    let rest := emitRows es indices
    (row.1++rest.1,row.2+rest.2+row.1.length+indexCharge d+4)

theorem emitRows_value (es : List (Arc (Signed (Fin n)) d)) (indices : List (Fin (M^d))) :
    (emitRows es indices).1=indices.flatMap (fun i => es.map (fun e =>
      (coverIndex n d M (e.source,(coordinateIndex d M).symm i),
        coverIndex n d M (e.target,(coordinateIndex d M).symm i+wrap M e.offset)))) := by
  induction indices <;> simp_all [emitRows,emitRow_value]

theorem emitRows_cost (es : List (Arc (Signed (Fin n)) d)) (indices : List (Fin (M^d))) :
    (emitRows es indices).2=indices.length*((es.length+1)*(indexCharge d+4)+1)+1 := by
  induction indices with
  | nil => simp [emitRows]
  | cons i indices ih =>
    simp only [emitRows,Prod.snd,emitRow_cost,emitRow_value,List.length_map,List.length_cons,ih]
    ring

/-- Includes the finite coordinate enumeration, protoarc construction, and edge table. -/
def compileCover (formula : Formula (Fin n) d) (M : Nat) [NeZero M] :
    List (Fin (n*2*M^d) × Fin (n*2*M^d)) × Nat :=
  let es := arcs formula
  let table := emitRows es (List.finRange (M^d))
  (table.1,formula.length*(4*d+10)+M^d+table.2+1)

theorem compileCover_value (formula : Formula (Fin n) d) : (compileCover formula M).1=coverEdges formula M :=
  emitRows_value _ _

theorem compileCover_cost (formula : Formula (Fin n) d) : (compileCover formula M).2=
    formula.length*(4*d+10)+M^d*((arcs formula).length+1)*(indexCharge d+4)+2*M^d+2 := by
  simp only [compileCover,Prod.snd,emitRows_cost,List.length_finRange]
  ring

theorem arcs_length (formula : Formula (Fin n) d) : (arcs formula).length ≤ 2*formula.length := by
  induction formula with
  | nil => simp [arcs]
  | cons c formula ih =>
    have bound : (clauseArcs c).length ≤ 2 := by cases c <;> simp [clauseArcs]
    simp only [arcs,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

end LeanTrominoes.PeriodicTwoSAT
