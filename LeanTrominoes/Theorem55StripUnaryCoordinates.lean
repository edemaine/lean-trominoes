/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnarySource

/-! # Coordinate semantics of the unary source-column compiler -/

namespace LeanTrominoes.Theorem55StripUnary
open PeriodicStripFlatEncoding (stripFields cellFields)

def cellAxis (axis : Fin 2) (c : Cell) : Int := if axis.val = 0 then c.1 else c.2

theorem flat_cell_get (cells : List Cell) (axis : Fin 2) (i : Nat) (hi : i < cells.length) :
    (cells.flatMap cellFields).getD (i*2+axis.val) 0 = Encodable.encode (cellAxis axis cells[i]) := by
  induction cells generalizing i with
  | nil => simp at hi
  | cons c cells ih =>
    cases i with
    | zero =>
      have ha := axis.isLt
      have cases : axis.val = 0 ∨ axis.val = 1 := by omega
      rcases cases with h | h <;> simp [List.flatMap_cons,cellFields,cellAxis,h]
    | succ i =>
      have hi' : i < cells.length := by simpa using hi
      have h := ih i hi'
      have index : (i+1)*2+axis.val = (i*2+axis.val)+2 := by omega
      simpa [List.flatMap_cons,cellFields,index] using h

theorem strip_cell_get (source : PeriodicStrip) (axis : Fin 2) (i : Nat) (hi : i < source.motif.length) :
    (stripFields source).getD (i*2+(3+axis.val)) 0 = Encodable.encode (cellAxis axis source.motif[i]) := by
  have index : i*2+(3+axis.val) = (i*2+axis.val)+3 := by omega
  simpa [stripFields,index] using flat_cell_get source.motif axis i hi

theorem axisCodes_eq (axis : Fin 2) (source : PeriodicStrip) :
    axisCodes axis source = source.motif.map (fun c => Encodable.encode (cellAxis axis c)) := by
  unfold axisCodes axisQueries
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,Function.comp_apply]
    exact strip_cell_get source axis i (by simpa using h₁)

theorem axisCoordinates_eq (axis : Fin 2) (source : PeriodicStrip) :
    axisCoordinates axis source = source.motif.map (fun c => Encodable.encode (cellAxis axis c)/2) := by
  rw [axisCoordinates,axisCodes_eq,List.map_map]
  rfl

def naturalMotif (source : PeriodicStrip) : List (Nat×Nat) :=
  source.motif.map (fun c => (Encodable.encode c.1/2,Encodable.encode c.2/2))

theorem naturalMotif_x (source : PeriodicStrip) : (naturalMotif source).map Prod.fst = axisCoordinates 0 source := by
  simp [naturalMotif,axisCoordinates_eq,cellAxis,List.map_map,Function.comp_def]
theorem naturalMotif_y (source : PeriodicStrip) : (naturalMotif source).map Prod.snd = axisCoordinates 1 source := by
  simp [naturalMotif,axisCoordinates_eq,cellAxis,List.map_map,Function.comp_def]

end LeanTrominoes.Theorem55StripUnary
