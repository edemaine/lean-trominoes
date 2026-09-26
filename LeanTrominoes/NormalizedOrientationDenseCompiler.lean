/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationSafePreparation
import LeanTrominoes.CompletionDenseDrawing

/-! # Polynomial-time dense drawing columns from bounded native input -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
open Turing UnaryColumn CompletionPattern CompletionPattern.Runtime PeriodicOrthogonalDrawing

abbrev sites (s : List PeriodicCNFFlatEncoding.Symbol) :=
  gridSites (drawing s).horizontalPeriod (drawing s).verticalPeriod

def xCompiler : Compiler sites (fun _ p => p.1) := gridXCompiler widthCompiler heightCompiler
def yCompiler : Compiler sites (fun _ p => p.2) := gridYCompiler widthCompiler heightCompiler

theorem drawing_getAt (s : List PeriodicCNFFlatEncoding.Symbol) (x y : Nat)
    (hx : x < (drawing s).horizontalPeriod) (hy : y < (drawing s).verticalPeriod) :
    (drawing s).getAt ((x:Int),(y:Int)) =
      safeCell (value s (y*(drawing s).horizontalPeriod+x+2)) := by
  rw [getAt_nat _ x y hx hy]
  have bound : y*(drawing s).horizontalPeriod+x <
      (drawing s).horizontalPeriod*(drawing s).verticalPeriod := by
    have h := Nat.mul_le_mul_right (drawing s).horizontalPeriod (Nat.succ_le_of_lt hy)
    nlinarith
  change ((List.range ((drawing s).horizontalPeriod*(drawing s).verticalPeriod)).map
    (fun n => safeCell (value s (n+2)))).getD (y*(drawing s).horizontalPeriod+x) .blank = _
  rw [List.getD_eq_getElem _ _ (by simpa using bound)]
  simp only [List.getElem_map,List.getElem_range]

def siteKindCompiler : Compiler sites
    (fun s p => (kindIndex (LBricks.kindOf ((drawing s).getAt ((p.1:Int),(p.2:Int))))).val) := by
  let index := add (add (multiplyScalar yCompiler widthCompiler) xCompiler) (constant xCompiler 2)
  let queried := fieldLookup index BoundedPreparation.compiler
  let result := residue (sub queried (constant queried 1)) BoundedPreparation.cellBound
    (by unfold BoundedPreparation.cellBound; omega)
    (fun i => (kindIndex (LBricks.kindOf ((FlatEncoding.decodeCell i.val).getD .blank))).val)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro p hp
  have bounds := gridSites_bounds hp
  dsimp only
  rw [drawing_getAt s p.1 p.2 bounds.1 bounds.2]
  rfl

def denseXCompiler : Compiler (fun s => denseEntries (drawing s)) (fun _ a => a.1.1.toNat) := by
  apply TM2ComputableInPolyTime.of_eq xCompiler
  intro s
  simp [denseEntries,densePoints,List.map_map,Function.comp_def,sites]

def denseYCompiler : Compiler (fun s => denseEntries (drawing s)) (fun _ a => a.1.2.toNat) := by
  apply TM2ComputableInPolyTime.of_eq yCompiler
  intro s
  simp [denseEntries,densePoints,List.map_map,Function.comp_def,sites]

def denseKindCompiler : Compiler (fun s => denseEntries (drawing s))
    (fun _ a => (kindIndex (LBricks.kindOf a.2)).val) := by
  apply TM2ComputableInPolyTime.of_eq siteKindCompiler
  intro s
  simp only [denseEntries,densePoints,List.map_map,Function.comp_def]

end LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
end
