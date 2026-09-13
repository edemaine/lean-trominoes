/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripPlacementExpr

/-! # The compiled containment test for an input placement -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

def fitsCell (depth : Nat) : Expr :=
  inside (var (depth+1)) (var (depth+2)) (var 2) (var 1)
    (cellCode (depth+1) 3 0 0) (cellCode (depth+1) 3 0 1)

def fitsAt (depth : Nat) : Expr := .all (cellCount depth 2) (fitsCell depth)

theorem fitsCell_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (front : List Nat) (a : Raw.Candidate)
    (index : Nat) (hi : index < (cells a.2.1).length) :
    (fitsCell (front.length+4)).Truth
      (index :: (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))) ↔
      (0 ≤ (a.2.2.2 : Int)-bound+(a.2.2.1.act (cells a.2.1)[index]).2 ∧
        (a.2.2.2 : Int)-bound+(a.2.2.1.act (cells a.2.1)[index]).2 < height) := by
  let source := index :: (Arithmetic.candidateFields a ++ front)
  let values := index :: (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))
  have len : source.length = front.length+5 := by simp [source,Arithmetic.candidateFields]
  have hx := cellCode_eval cells height bound first second source a.2.1 3 0 index (0 : Fin 2)
    (by rfl) (by rfl) hi
  have hy := cellCode_eval cells height bound first second source a.2.1 3 0 index (1 : Fin 2)
    (by rfl) (by rfl) hi
  rw [len] at hx hy
  change (cellCode (front.length+5) 3 0 0).eval values = Encodable.encode ((cells a.2.1)[index]).1 at hx
  change (cellCode (front.length+5) 3 0 1).eval values = Encodable.encode ((cells a.2.1)[index]).2 at hy
  have hh := Arithmetic.header_get cells height bound first second source 0 (by decide)
  have hb := Arithmetic.header_get cells height bound first second source 1 (by decide)
  rw [len] at hh hb
  change values[front.length+5]?.getD 0 = height at hh
  change values[front.length+6]?.getD 0 = bound at hb
  rw [fitsCell,inside_truth,hx,hy]
  simp only [eval_var]
  change (2*(values[front.length+6]?.getD 0) ≤ a.2.2.2+
      Arithmetic.bias (values[front.length+6]?.getD 0)
        (Arithmetic.orientedY (Raw.symmetryIndex a.2.2.1) (Encodable.encode ((cells a.2.1)[index]).1) (Encodable.encode ((cells a.2.1)[index]).2)) ∧
    a.2.2.2+Arithmetic.bias (values[front.length+6]?.getD 0)
        (Arithmetic.orientedY (Raw.symmetryIndex a.2.2.1) (Encodable.encode ((cells a.2.1)[index]).1) (Encodable.encode ((cells a.2.1)[index]).2)) <
          (values[front.length+5]?.getD 0)+2*(values[front.length+6]?.getD 0)) ↔ _
  rw [hh,hb]
  exact Arithmetic.inside_iff bounded a.2.1 a.2.2.1 a.2.2.2 (cells a.2.1)[index] (List.getElem_mem hi)

theorem fitsAt_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (front : List Nat) (a : Raw.Candidate) :
    (fitsAt (front.length+4)).Truth
      (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) ↔
      Raw.Fits cells height bound a.2 := by
  let values := Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)
  have count := cellCount_eval cells height bound first second (Arithmetic.candidateFields a ++ front) a.2.1 2 (by rfl)
  have len : (Arithmetic.candidateFields a ++ front).length = front.length+4 := by simp [Arithmetic.candidateFields]
  rw [len] at count
  change (cellCount (front.length+4) 2).eval values = (cells a.2.1).length at count
  rw [fitsAt,truth_all,count]
  constructor
  · intro h c hc
    obtain ⟨index,hi,eq⟩ := List.mem_iff_getElem.mp hc
    have inside := (fitsCell_truth cells height bound first second bounded front a index hi).mp (h index hi)
    simpa [eq] using inside
  · intro h index hi
    apply (fitsCell_truth cells height bound first second bounded front a index hi).mpr
    exact h _ (List.getElem_mem hi)

theorem fitsAt_noPower (depth : Nat) : (fitsAt depth).noPower = true := by
  simp [fitsAt,fitsCell,inside,biased,orientY,negate,andE,leE,ltE,notE,orE,eqE,
    cellCount,cellCode,Expr.noPower]

end LeanTrominoes.PolyominoStripWindow.Formula
