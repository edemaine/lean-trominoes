/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHornLinearTime

/-! # Kernel-checked edge cases for indexed Horn worklists -/
namespace LeanTrominoes.Horn.WorklistExamples
open Indexed

-- Both occurrences must be discharged by the same single processing of atom 0.
def duplicatePremises : Input 2 := ⟨#[⟨[],some 0⟩,⟨[0,0],some 1⟩,⟨[1],none⟩]⟩
example : Indexed.check duplicatePremises=false := by decide +kernel

-- Several rules may enqueue one atom; its occurrence bucket is read only once.
def duplicateHeads : Input 2 := ⟨#[⟨[],some 0⟩,⟨[],some 0⟩,⟨[0],some 1⟩]⟩
example : Indexed.check duplicateHeads=true := by decide +kernel
example : [model duplicateHeads 0,model duplicateHeads 1]=[true,true] := by decide +kernel
example : totalCost duplicateHeads ≤ 64*inputSize duplicateHeads := by decide +kernel

-- No initial fact: a cycle produces the empty least model.
def cycle : Input 2 := ⟨#[⟨[0],some 1⟩,⟨[1],some 0⟩]⟩
example : Indexed.check cycle=true := by decide +kernel
example : [model cycle 0,model cycle 1]=[false,false] := by decide +kernel

example : Indexed.check (⟨#[]⟩ : Input 0)=true := by decide +kernel
example : Indexed.check (⟨#[⟨[],none⟩]⟩ : Input 0)=false := by decide +kernel

-- Arbitrarily distant three-dimensional offsets disappear in the quotient.
def spatial : Array (PeriodicRule (Fin 2) (Fin 3 → Int)) := #[
  ⟨[],some (0,fun _ => 1000000)⟩,
  ⟨[(0,fun _ => -999999)],some (1,fun _ => 3)⟩]
example : PeriodicIndexed.check spatial=true := by decide +kernel
example : PeriodicIndexed.model spatial 1=true := by decide +kernel
example : PeriodicIndexed.totalCost spatial ≤ 72*PeriodicIndexed.inputSize spatial := by decide +kernel

end LeanTrominoes.Horn.WorklistExamples
