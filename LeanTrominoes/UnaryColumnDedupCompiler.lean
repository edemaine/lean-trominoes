/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.UnaryFieldStableDedupSemantics

/-! # Compiling one value per distinct row using injective numeric identities -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol] [DecidableEq Index]
  {rows : List Symbol → List Index} {key value : List Symbol → Index → Nat}

def dedupKeys (keys : Compiler rows key) (injective : ∀ s, Function.Injective (key s)) :
    Compiler (fun s => (rows s).dedup) key := by
  let result := UnaryFieldStableDedup.valuesComputableInPolyTime id _ keys
  exact TM2ComputableInPolyTime.of_eq result (fun s => by
    rw [UnaryFieldStableDedup.values_eq_dedup,List.dedup_map_of_injective (injective s)])

def dedup (keys : Compiler rows key) (values : Compiler rows value)
    (injective : ∀ s, Function.Injective (key s)) :
    Compiler (fun s => (rows s).dedup) value := by
  classical
  let datum (s : List Symbol) (n : Nat) : Nat := if h : ∃ i, key s i=n then value s h.choose else 0
  have atKey (s : List Symbol) (i : Index) : datum s (key s i)=value s i := by
    simp only [datum,dif_pos (show ∃ j, key s j=key s i from ⟨i,rfl⟩)]
    congr 1
    exact injective s (Exists.choose_spec (show ∃ j, key s j=key s i from ⟨i,rfl⟩))
  let result := keyed (dedupKeys keys injective) keys values datum
    (fun s i _ => (atKey s i).symm)
    (fun _ i hi => ⟨i,List.mem_dedup.mp hi,rfl⟩)
  exact TM2ComputableInPolyTime.of_eq result (fun s => List.map_congr_left (fun i _ => atKey s i))

end LeanTrominoes.UnaryColumn
end
