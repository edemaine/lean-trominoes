/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripMotifRows
import LeanTrominoes.CompletionPlacementColumnCompiler

/-! # Polynomial-time expansion and serialization of all prescribed brick placements -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
set_option maxHeartbeats 3000000
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
  {period count : List Symbol → Nat} {palette : List Symbol → Cell → Fin 24}

def expandedSiteColumn (t : Tromino) {f : List Symbol → (Nat×Nat) → Nat}
    (c : Compiler (fun s => gridSites (period s) (count s)) f) :
    Compiler (fun s => expandedRows t (period s) (count s)) (fun s r => f s r.1) :=
  cartesianLeft c (table (taggedMotifs t) (fun a => a.1.val))

def expandedTableColumn (t : Tromino) {f : List Symbol → (Nat×Nat) → Nat}
    (c : Compiler (fun s => gridSites (period s) (count s)) f)
    (value : (Fin 24 × Placement Unit) → Nat) :
    Compiler (fun s => expandedRows t (period s) (count s)) (fun _ r => value r.2) :=
  cartesianRight c (table (taggedMotifs t) value)

def keepCompiler (t : Tromino)
    (cp : Compiler (fun s => gridSites (period s) (count s))
      (fun s p => (palette s ((p.1:Int),(p.2:Int))).val)) :
    TM2ComputableInPolyTime id id (fun s => (expandedRows t (period s) (count s)).map (keepRow (palette s))) := by
  let labels := expandedSiteColumn t cp
  let tags := expandedTableColumn t cp (fun a => a.1.val)
  let equality := residue (add tags (scale labels 24)) 576 (by decide)
    (fun n => (decide (n.val%24 = n.val/24)).toNat)
  let result := bits equality
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro r _
  dsimp only
  have hl := (palette s ((r.1.1:Int),(r.1.2:Int))).isLt
  have ht := r.2.1.isLt
  have bound : r.2.1.val+(palette s ((r.1.1:Int),(r.1.2:Int))).val*24 < 576 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  have a : (r.2.1.val+(palette s ((r.1.1:Int),(r.1.2:Int))).val*24)%24 = r.2.1.val := by omega
  have b : (r.2.1.val+(palette s ((r.1.1:Int),(r.1.2:Int))).val*24)/24 =
      (palette s ((r.1.1:Int),(r.1.2:Int))).val := by omega
  simp [a,b,keepRow,Fin.ext_iff]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq,Fin.ext_iff]

def selectedSiteColumn (t : Tromino)
    (cp : Compiler (fun s => gridSites (period s) (count s))
      (fun s p => (palette s ((p.1:Int),(p.2:Int))).val))
    {f : List Symbol → (Nat×Nat) → Nat}
    (c : Compiler (fun s => gridSites (period s) (count s)) f) :
    Compiler (fun s => selectedRows t (period s) (count s) (palette s)) (fun s r => f s r.1) :=
  filter (expandedSiteColumn t c) (keepCompiler t cp)

def selectedTableColumn (t : Tromino)
    (cp : Compiler (fun s => gridSites (period s) (count s))
      (fun s p => (palette s ((p.1:Int),(p.2:Int))).val))
    (value : (Fin 24 × Placement Unit) → Nat) :
    Compiler (fun s => selectedRows t (period s) (count s) (palette s)) (fun _ r => value r.2) :=
  filter (expandedTableColumn t cp value) (keepCompiler t cp)

def brickWidth : Tromino → Nat | .L => 24 | .I => 36
def brickSkew : Tromino → Nat | .L => 12 | .I => 18
def brickHeight : Tromino → Nat | .L => 36 | .I => 162

theorem row_placement_shift (t : Tromino) (r : MotifRow) :
    (rowPlacement t r).shift (0,2) = r.2.2.shift
      (((r.1.1*brickWidth t+r.1.2*brickSkew t:Nat):Int),((r.1.2*brickHeight t+2:Nat):Int)) := by
  cases t <;> simp [rowPlacement,brickOrigin,brickWidth,brickSkew,brickHeight,LBricks.origin,IBricks.origin,
    Placement.shift,Cell.add,Nat.cast_add,Nat.cast_mul,Int.add_assoc,Int.mul_comm,Int.add_comm,Int.add_left_comm]

def bandFieldsCompiler (t : Tromino)
    (cx : Compiler (fun s => gridSites (period s) (count s)) (fun _ p => p.1))
    (cy : Compiler (fun s => gridSites (period s) (count s)) (fun _ p => p.2))
    (cp : Compiler (fun s => gridSites (period s) (count s))
      (fun s p => (palette s ((p.1:Int),(p.2:Int))).val)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (selectedRows t (period s) (count s) (palette s)).flatMap fun r =>
        CompletionStripEncoding.placementFields ((rowPlacement t r).shift (0,2))) := by
  let rawY := selectedSiteColumn t cp cy
  let xs := add (scale (selectedSiteColumn t cp cx) (brickWidth t)) (scale rawY (brickSkew t))
  let ys := add (scale rawY (brickHeight t)) (constant rawY 2)
  let syms := selectedTableColumn t cp (fun a => CompletionStripEncoding.symmetryCode a.2.symmetry)
  let px := selectedTableColumn t cp (fun a => a.2.offset.1.toNat)
  let nx := selectedTableColumn t cp (fun a => (-a.2.offset.1).toNat)
  let py := selectedTableColumn t cp (fun a => a.2.offset.2.toNat)
  let ny := selectedTableColumn t cp (fun a => (-a.2.offset.2).toNat)
  let result := placementFieldsCompiler xs ys syms px nx py ny
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp only [row_placement_shift])
end LeanTrominoes.CompletionPattern.Runtime
