/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripSourcePaletteCompiler

/-! # Fixed-table row expansion for the finite prescribed brick motif -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime

def brickMotif (t : Tromino) (k : Fin 24) : List (Placement Unit) :=
  match t with | .L => LBricks.motif k | .I => IBricks.motif k

def taggedMotifs (t : Tromino) : List (Fin 24 × Placement Unit) :=
  (List.finRange 24).flatMap fun k => (brickMotif t k).map fun p => (k,p)

private theorem filter_labels (k : Fin 24) : (List.finRange 24).filter (fun l => l == k) = [k] := by
  revert k
  decide +kernel

theorem tagged_filter (t : Tromino) (k : Fin 24) :
    ((taggedMotifs t).filter (fun a => a.1 == k)).map Prod.snd = brickMotif t k := by
  have general (labels : List (Fin 24)) :
      ((labels.flatMap fun l => (brickMotif t l).map fun p => (l,p)).filter (fun a => a.1 == k)).map Prod.snd =
        (labels.filter (fun l => l == k)).flatMap (brickMotif t) := by
    induction labels with
    | nil => rfl
    | cons l labels ih =>
      simp only [List.flatMap_cons,List.filter_append,List.map_append,ih]
      by_cases eq : l = k
      · subst l
        simp [List.filter_map,Function.comp_def]
      · have ne : (l == k) = false := beq_eq_false_iff_ne.mpr eq
        simp [List.filter_map,Function.comp_def,ne]
  rw [taggedMotifs,general,filter_labels]
  simp

abbrev MotifRow := (Nat×Nat) × (Fin 24 × Placement Unit)

def expandedRows (t : Tromino) (period count : Nat) : List MotifRow :=
  (gridSites period count).flatMap fun c => (taggedMotifs t).map fun a => (c,a)

def keepRow (palette : Cell → Fin 24) (r : MotifRow) : Bool :=
  r.2.1 == palette ((r.1.1:Int),(r.1.2:Int))

def selectedRows (t : Tromino) (period count : Nat) (palette : Cell → Fin 24) : List MotifRow :=
  (expandedRows t period count).filter (keepRow palette)

def brickOrigin (t : Tromino) (c : Cell) : Cell :=
  match t with | .L => LBricks.origin c | .I => IBricks.origin c

def rowPlacement (t : Tromino) (r : MotifRow) : Placement Unit :=
  r.2.2.shift (brickOrigin t ((r.1.1:Int),(r.1.2:Int)))

theorem selected_placements (t : Tromino) (period count : Nat) (palette : Cell → Fin 24) :
    (selectedRows t period count palette).map (rowPlacement t) =
      (gridSites period count).flatMap fun c =>
        (brickMotif t (palette ((c.1:Int),(c.2:Int)))).map fun p =>
          p.shift (brickOrigin t ((c.1:Int),(c.2:Int))) := by
  unfold selectedRows expandedRows
  rw [List.filter_flatMap,List.map_flatMap]
  apply congrArg ((gridSites period count).flatMap)
  funext c
  rw [List.filter_map,List.map_map]
  have eq := congrArg (fun ps : List (Placement Unit) =>
    ps.map fun p => p.shift (brickOrigin t ((c.1:Int),(c.2:Int))))
    (tagged_filter t (palette ((c.1:Int),(c.2:Int))))
  simpa only [List.map_map,Function.comp_def,keepRow,rowPlacement] using eq

theorem selected_placements_L (period count : Nat) (palette : Cell → Fin 24) :
    (selectedRows .L period count palette).map (rowPlacement .L) =
      LBricks.bandMotif period count palette := by
  rw [selected_placements]
  simp [LBricks.bandMotif,LBricks.bandSites,gridSites,brickMotif,brickOrigin,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,Function.comp_def]

theorem selected_placements_I (period count : Nat) (palette : Cell → Fin 24) :
    (selectedRows .I period count palette).map (rowPlacement .I) =
      IBricks.bandMotif period count palette := by
  rw [selected_placements]
  simp [IBricks.bandMotif,IBricks.bandSites,gridSites,brickMotif,brickOrigin,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,Function.comp_def]
end LeanTrominoes.CompletionPattern.Runtime
