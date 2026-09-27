/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHornDecision

/-! # Kernel-checked boundary cases for the periodic Horn solver -/
namespace LeanTrominoes.PeriodicCNF.HornExamples

private def lit (a : Nat) (p : Cell) (value : Bool) : PeriodicLiteral Nat := ⟨a,p,value⟩

-- A fact propagates along a chain even when references have distant offsets.
def chain : PeriodicCNF Nat := ⟨[
  [lit 0 (100,-20) true],
  [lit 0 (-7,5) false,lit 1 (0,0) true],
  [lit 1 (0,0) false,lit 2 (0,91) true]]⟩
example : chain.hornCheck=true := by decide
example : [chain.hornModel 0,chain.hornModel 1,chain.hornModel 2]=[true,true,true] := by decide

-- A negative constraint can contradict a fact at a different translate.
def contradiction : PeriodicCNF Nat := ⟨chain.clauses++[[lit 2 (-100,3) false]]⟩
example : contradiction.hornCheck=false := by decide

-- A cycle without a fact does not force either variable to become true.
def cycle : PeriodicCNF Nat := ⟨[
  [lit 0 (0,0) false,lit 1 (1,0) true],
  [lit 1 (0,0) false,lit 0 (-1,0) true]]⟩
example : cycle.hornCheck=true := by decide
example : [cycle.hornModel 0,cycle.hornModel 1]=[false,false] := by decide

example : (⟨[]⟩ : PeriodicCNF Nat).hornCheck=true := by decide
example : (⟨[[]]⟩ : PeriodicCNF Nat).hornCheck=false := by decide

-- Repeated copies of the same literal are harmless; distinct positive literals are rejected.
example : (⟨[[lit 0 (0,0) true,lit 0 (0,0) true]]⟩ : PeriodicCNF Nat).hornCheck=true := by decide
example : (⟨[[lit 0 (0,0) true,lit 1 (0,0) true]]⟩ : PeriodicCNF Nat).hornCheck=false := by decide

example : chain.complementLiterals.dualHornCheck=true := by decide
example : [chain.complementLiterals.dualHornModel 0,chain.complementLiterals.dualHornModel 2]=[false,false] := by decide

end LeanTrominoes.PeriodicCNF.HornExamples
