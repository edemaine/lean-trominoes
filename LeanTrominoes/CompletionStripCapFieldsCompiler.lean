/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPrefillEncodingCompiler
import LeanTrominoes.CompletionStripCapCompiler

/-! # Polynomial-time emission of finite repeated cap motifs -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

def affinePlacementTable (items : List (Placement Unit)) (factor : Nat)
    {repeats height : List Symbol → Nat} (cr : ScalarCompiler repeats) (ch : ScalarCompiler height) :
    PlacementListCompiler (fun s => (List.range (repeats s)).flatMap fun i =>
      items.map fun p => p.shift (((i*factor:Nat):Int),(height s:Int))) := by
  let reference := naturalRange cr
  let tx := table (Symbol := Symbol) items (fun p => p.offset.1.toNat)
  let index := cartesianLeft reference tx
  let xs := scale index factor
  let ys := broadcast index ch
  let syms := cartesianRight reference (table (Symbol := Symbol) items (fun p => CompletionStripEncoding.symmetryCode p.symmetry))
  let px := cartesianRight reference tx
  let nx := cartesianRight reference (table (Symbol := Symbol) items (fun p => (-p.offset.1).toNat))
  let py := cartesianRight reference (table (Symbol := Symbol) items (fun p => p.offset.2.toNat))
  let ny := cartesianRight reference (table (Symbol := Symbol) items (fun p => (-p.offset.2).toNat))
  refine ⟨?_,?_⟩
  · let result := placementFieldsCompiler xs ys syms px nx py ny
    apply TM2ComputableInPolyTime.of_eq result
    intro s
    simp [List.flatMap_assoc,List.flatMap_map,List.map_flatMap,Function.comp_def]
  · exact TM2ComputableInPolyTime.of_eq (countRows index) (fun s => by simp)

def capListCompiler (t : Tromino) (top : Bool) {period height : List Symbol → Nat}
    (cp : ScalarCompiler period) (ch : ScalarCompiler height) :
    PlacementListCompiler (fun s => (StripCaps.expandedCap t top (period s)).map
      (fun p => p.shift (0,(height s:Int)))) := by
  let p : Compiler (fun _ : List Symbol => [()]) (fun s _ => period s) := cp
  let repeats : ScalarCompiler (fun s => 2*period s) :=
    TM2ComputableInPolyTime.of_eq (scale p 2) (fun s => by simp [Nat.mul_comm])
  let result := affinePlacementTable (StripCaps.capMotif t top) (StripCaps.width t).toNat repeats ch
  apply result.ofEq
  intro s
  cases t <;> simp [StripCaps.expandedCap,HorizontalPrefill.expand,StripCaps.width,
    List.map_flatMap,List.map_map,Function.comp_def,Placement.shift,Cell.add,Int.add_assoc]
end LeanTrominoes.CompletionPattern.Runtime
