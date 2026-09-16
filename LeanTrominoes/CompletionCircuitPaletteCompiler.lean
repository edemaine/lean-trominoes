/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalCompiler
import LeanTrominoes.CompletionOrientationStripCompiler

/-! # Polynomial-time evaluation of the fixed completion palette tables -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn LBricks DiagonalRouting

def kindIndex : CircuitKind → Fin 9
  | .blank => 0 | .horizontal => 1 | .vertical => 2 | .northwest => 3
  | .southeast => 4 | .northeast => 5 | .southwest => 6 | .copy => 7 | .exactone => 8

def indexKind (i : Fin 9) : CircuitKind :=
  ![.blank,.horizontal,.vertical,.northwest,.southeast,.northeast,.southwest,.copy,.exactone] i
@[simp] theorem index_kind (k : CircuitKind) : indexKind (kindIndex k) = k := by cases k <;> rfl

def localLabel (kind : Fin 9) (x y : Nat) : Fin 24 :=
  (circuitFor (indexKind kind)).labelAt (((x%64:Nat):Int),((y%64:Nat):Int))

private def labelTable (i : Fin 36864) : Nat :=
  ((circuitFor (indexKind ⟨i.val/4096,by omega⟩)).labelAt (((i.val%64:Nat):Int),((i.val/64%64:Nat):Int))).val

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {x y : List Symbol → Index → Nat}
  {kind : List Symbol → Index → Fin 9}

def localLabelCompiler (cx : Compiler rows x) (cy : Compiler rows y)
    (ck : Compiler rows (fun s i => (kind s i).val)) :
    Compiler rows (fun s i => (localLabel (kind s i) (x s i) (y s i)).val) := by
  let key := add (add (residue cx 64 (by decide) Fin.val)
    (scale (residue cy 64 (by decide) Fin.val) 64)) (scale ck 4096)
  let result := residue key 36864 (by decide) labelTable
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i _
  simp only [labelTable,localLabel]
  have hk := (kind s i).isLt
  have bound : x s i%64+y s i%64*64+(kind s i).val*4096 < 36864 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  have ax : (x s i%64+y s i%64*64+(kind s i).val*4096)%64 = x s i%64 := by omega
  have ay : (x s i%64+y s i%64*64+(kind s i).val*4096)/64%64 = y s i%64 := by omega
  have ak : (x s i%64+y s i%64*64+(kind s i).val*4096)/4096 = (kind s i).val := by omega
  simp only [ax,ay,ak]

def refinedLabel (label : Fin 24) (role : Fin 8) : Fin 24 :=
  if label = 0 then 0 else if role = 0 then label else wireLabel role

private def refinedTable (i : Fin 192) : Nat :=
  (refinedLabel ⟨i.val%24,by omega⟩ ⟨i.val/24,by omega⟩).val

def refinedLabelCompiler {label : List Symbol → Index → Fin 24}
    {role : List Symbol → Index → Fin 8}
    (cl : Compiler rows (fun s i => (label s i).val))
    (cr : Compiler rows (fun s i => (role s i).val)) :
    Compiler rows (fun s i => (refinedLabel (label s i) (role s i)).val) := by
  let result := residue (add cl (scale cr 24)) 192 (by decide) refinedTable
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i _
  dsimp [refinedTable]
  have hl := (label s i).isLt
  have hr := (role s i).isLt
  have bound : (label s i).val+(role s i).val*24 < 192 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  have al : ((label s i).val+(role s i).val*24)%24 = (label s i).val := by omega
  have ar : ((label s i).val+(role s i).val*24)/24 = (role s i).val := by omega
  simp only [al,ar]

def natPalette (kind : Fin 9) (x y : Nat) : Fin 24 :=
  refinedLabel (localLabel kind (natSourceX x y) (natSourceY x y)) (natRole x y)

def natPaletteCompiler (cx : Compiler rows x) (cy : Compiler rows y)
    (ck : Compiler rows (fun s i => (kind s i).val)) :
    Compiler rows (fun s i => (natPalette (kind s i) (x s i) (y s i)).val) :=
  refinedLabelCompiler (localLabelCompiler (sourceXCompiler cx cy) (sourceYCompiler cx cy) ck)
    (roleCompiler cx cy)

theorem natPalette_correct (d : Gadget.PeriodicOrthogonalDrawing) (x y : Nat) :
    natPalette (kindIndex (stripKinds d (Circuit.macroIndex (natSourceX x y,natSourceY x y)))) x y =
      StripOrientation.palette d ((x:Int),(y:Int)) := by
  unfold StripOrientation.palette brickPalette boundedPalette refinePalette
  rw [sourceAt_nat,roleAt_nat]
  have eq : localLabel (kindIndex (stripKinds d (Circuit.macroIndex (natSourceX x y,natSourceY x y))))
      (natSourceX x y) (natSourceY x y) =
      Circuit.macroPalette (stripKinds d) (natSourceX x y,natSourceY x y) := by
    simp [localLabel,Circuit.macroPalette,Circuit.macroLocal]
  simp only [natPalette,refinedLabel,eq]
end LeanTrominoes.CompletionPattern.Runtime
