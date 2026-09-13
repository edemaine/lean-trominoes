/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripContainmentExpr

/-! # Compiled coverage by a selected placement -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

def coversCell (depth rowField : Nat) : Expr :=
  covers (var (depth+2)) (var 2) (var 4) (var 1) (var (rowField+1))
    (cellCode (depth+1) 3 0 0) (cellCode (depth+1) 3 0 1)

def coversAt (depth rowField : Nat) : Expr :=
  andE (selected depth false 0) (existsE (cellCount depth 2) (coversCell depth rowField))

theorem coversCell_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (front : List Nat) (a : Raw.Candidate)
    (index rowField : Nat) (hi : index < (cells a.2.1).length) :
    (coversCell (front.length+4) rowField).Truth
      (index :: (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))) ↔
    Cell.add ((a.1 : Int),(a.2.2.2 : Int)-bound) (a.2.2.1.act (cells a.2.1)[index]) =
      ((bound : Int),(((Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))[rowField]?.getD 0) : Int)) := by
  let source := index :: (Arithmetic.candidateFields a ++ front)
  let values := Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)
  have len : source.length = front.length+5 := by simp [source,Arithmetic.candidateFields]
  have hx := cellCode_eval cells height bound first second source a.2.1 3 0 index (0 : Fin 2)
    (by rfl) (by rfl) hi
  have hy := cellCode_eval cells height bound first second source a.2.1 3 0 index (1 : Fin 2)
    (by rfl) (by rfl) hi
  rw [len] at hx hy
  change (cellCode (front.length+5) 3 0 0).eval (index :: values) = Encodable.encode ((cells a.2.1)[index]).1 at hx
  change (cellCode (front.length+5) 3 0 1).eval (index :: values) = Encodable.encode ((cells a.2.1)[index]).2 at hy
  have hb := Arithmetic.header_get cells height bound first second source 1 (by decide)
  rw [len] at hb
  change (index :: values)[front.length+6]?.getD 0 = bound at hb
  rw [coversCell,covers_truth,hx,hy]
  simp only [eval_var,List.getElem?_cons_succ]
  change (a.1+Arithmetic.bias (values[front.length+5]?.getD 0)
      (Arithmetic.orientedX (Raw.symmetryIndex a.2.2.1) (Encodable.encode ((cells a.2.1)[index]).1) (Encodable.encode ((cells a.2.1)[index]).2)) =
        2*(values[front.length+5]?.getD 0) ∧
    a.2.2.2+Arithmetic.bias (values[front.length+5]?.getD 0)
      (Arithmetic.orientedY (Raw.symmetryIndex a.2.2.1) (Encodable.encode ((cells a.2.1)[index]).1) (Encodable.encode ((cells a.2.1)[index]).2)) =
        (values[rowField]?.getD 0)+2*(values[front.length+5]?.getD 0)) ↔ _
  change values[front.length+5]?.getD 0 = bound at hb
  rw [hb]
  exact Arithmetic.covers_iff bounded a.2.1 a.2.2.1 a.1 a.2.2.2 (values[rowField]?.getD 0)
    (cells a.2.1)[index] (List.getElem_mem hi)

theorem coversAt_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (front : List Nat) (a : Raw.Candidate)
    (rowField : Nat) (ha : a ∈ Raw.keys height bound) :
    (coversAt (front.length+4) rowField).Truth
      (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) ↔
    Raw.Covers cells height bound first
      ((Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))[rowField]?.getD 0) a := by
  let values := Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)
  have selectedEq : (selected (front.length+4) false 0).Truth values ↔ Raw.selected height bound first a = true := by
    simpa [values,Raw.selected_eq_testBit_address height bound first a ha] using
      selected_truth cells height bound first second front a false 0
  have count := cellCount_eval cells height bound first second (Arithmetic.candidateFields a ++ front) a.2.1 2 (by rfl)
  have len : (Arithmetic.candidateFields a ++ front).length = front.length+4 := by simp [Arithmetic.candidateFields]
  rw [len] at count
  change (cellCount (front.length+4) 2).eval values = (cells a.2.1).length at count
  rw [coversAt,truth_and,selectedEq,truth_exists,count]
  change (_ ∧ ∃ i < (cells a.2.1).length, (coversCell (front.length+4) rowField).Truth (i :: values)) ↔
    (_ ∧ ∃ c ∈ cells a.2.1, Cell.add ((a.1 : Int),(a.2.2.2 : Int)-bound) (a.2.2.1.act c) =
      ((bound : Int),((values[rowField]?.getD 0) : Int)))
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨index,hi,h⟩
    exact ⟨(cells a.2.1)[index],List.getElem_mem hi,
      (coversCell_truth cells height bound first second bounded front a index rowField hi).mp h⟩
  · rintro ⟨c,hc,h⟩
    obtain ⟨index,hi,eq⟩ := List.mem_iff_getElem.mp hc
    refine ⟨index,hi,(coversCell_truth cells height bound first second bounded front a index rowField hi).mpr ?_⟩
    simpa [eq] using h

theorem coversAt_noPower (depth rowField : Nat) : (coversAt depth rowField).noPower = true := by
  simp [coversAt,coversCell,covers,biased,orientX,orientY,negate,andE,existsE,notE,orE,eqE,
    cellCount,cellCode,Expr.noPower,selected_noPower]

end LeanTrominoes.PolyominoStripWindow.Formula
