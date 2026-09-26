/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationFlatEncoding
import LeanTrominoes.BoundedArithmeticFiniteTable
import Mathlib.Data.List.GetD

/-! # Space-certified queries of native orientation cell fields -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.FieldQueries
open PeriodicOrthogonalDrawing FlatEncoding BoundedArithmetic BoundedArithmetic.Expr

def cell (depth : Nat) (index : Expr) : Expr := .load (.literal (depth+2)+index)

theorem cell_eval (d : PeriodicOrthogonalDrawing) (front : List Nat) (index : Expr) :
    (cell front.length index).eval (front++fields d) =
      cellCode (d.cellTypes.getD (index.eval (front++fields d)) .blank) := by
  change ((front++fields d)[front.length+2+index.eval (front++fields d)]?).getD 0 = _
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+2+index.eval (front++fields d)-front.length =
      2+index.eval (front++fields d) := by omega
  rw [address]
  simp only [fields,Nat.add_comm 2,List.getElem?_cons_succ,List.getElem?_map]
  have h := List.getD_map d.cellTypes .blank cellCode
    (n := index.eval (front++fields d))
  simpa only [cellCode_blank,List.getD_eq_getElem?_getD,List.getElem?_map,fields] using h

def types : List OrthogonalCellType := Finset.univ.toList

def port (side : Side) (query : Expr) : Expr :=
  tableLookup (types.map (fun c => (cellCode c,Encodable.encode (c.portColor side)))) query

def vertex (query : Expr) : Expr :=
  tableLookup (types.map (fun c => (cellCode c,c.isVertex.toNat))) query

theorem port_eval (side : Side) (query : Expr) (values : List Nat) (c : OrthogonalCellType)
    (atQuery : query.eval values = cellCode c) :
    (port side query).eval values = Encodable.encode (c.portColor side) :=
  tableLookup_encoded types cellCode (fun c => Encodable.encode (c.portColor side))
    cellCode_injective query values c (by simp [types]) atQuery

theorem vertex_eval (query : Expr) (values : List Nat) (c : OrthogonalCellType)
    (atQuery : query.eval values = cellCode c) :
    (vertex query).eval values = c.isVertex.toNat :=
  tableLookup_encoded types cellCode (fun c => c.isVertex.toNat)
    cellCode_injective query values c (by simp [types]) atQuery

theorem cell_noPower (depth : Nat) (index : Expr) (allowed : index.noPower = true) :
    (cell depth index).noPower = true := by simp [cell,Expr.noPower,allowed]

theorem port_noPower (side : Side) (query : Expr) (allowed : query.noPower = true) :
    (port side query).noPower = true := tableLookup_noPower _ _ allowed

theorem vertex_noPower (query : Expr) (allowed : query.noPower = true) :
    (vertex query).noPower = true := tableLookup_noPower _ _ allowed

end LeanTrominoes.Gadget.NormalizedOrientation.FieldQueries
end
