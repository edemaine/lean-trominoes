/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFBounds
import LeanTrominoes.FiniteCNFWidth
import LeanTrominoes.PeriodicCNFFlatEncodingSize

/-! # A flat finite-alphabet encoding of ordinary finite tableaux

Variable pairs are paired once, while clauses and literals remain flat.
The zero-offset field format reuses the checked native binary-field codec.
-/
namespace LeanTrominoes.FiniteCNFFlatEncoding
open Computability

def asPeriodic (formula : FiniteCNF.Formula (Nat × Nat)) : PeriodicCNF Nat :=
  FiniteCNF.periodize (FiniteCNF.rename Nat.pairEquiv formula)

def fromPeriodic (formula : PeriodicCNF Nat) : FiniteCNF.Formula (Nat × Nat) :=
  formula.clauses.map fun clause => clause.map fun literal => (Nat.unpair literal.atom,literal.value)

@[simp] theorem fromPeriodic_asPeriodic (formula : FiniteCNF.Formula (Nat × Nat)) :
    fromPeriodic (asPeriodic formula)=formula := by
  have pair (p : Nat × Nat) : Nat.unpair (Function.uncurry Nat.pair p)=p := by
    rcases p with ⟨a,b⟩
    exact Nat.unpair_pair a b
  simp [fromPeriodic,asPeriodic,FiniteCNF.periodize,FiniteCNF.rename,List.map_map,
    Function.comp_def,Nat.pairEquiv,pair]

def fields (formula : FiniteCNF.Formula (Nat × Nat)) : List Nat :=
  PeriodicCNFFlatEncoding.formulaFields (asPeriodic formula)

def decodeFields (fields : List Nat) : Option (FiniteCNF.Formula (Nat × Nat)) :=
  (PeriodicCNFFlatEncoding.decodeFormulaFields fields).map fromPeriodic

@[simp] theorem decodeFields_fields (formula : FiniteCNF.Formula (Nat × Nat)) :
    decodeFields (fields formula)=some formula := by
  simp [decodeFields,fields]

def finEncoding : _root_.LeanTrominoes.FiniteEncoding (FiniteCNF.Formula (Nat × Nat)) :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decodeFields decodeFields_fields

theorem satisfiable_asPeriodic (formula : FiniteCNF.Formula (Nat × Nat)) :
    (asPeriodic formula).Satisfiable ↔ FiniteCNF.Satisfiable formula := by
  rw [asPeriodic,FiniteCNF.satisfiable_periodize,FiniteCNF.satisfiable_pair_rename]

theorem encode_length_le (formula : FiniteCNF.Formula (Nat × Nat))
    (timeBound atomBound clauseBound : Nat)
    (width : FiniteCNF.WidthAtMost 3 formula)
    (ranges : ∀ clause∈formula, ∀ literal∈clause,
      literal.1.1 ≤ timeBound ∧ literal.1.2 ≤ atomBound)
    (clauses : formula.length ≤ clauseBound) :
    (finEncoding.encode formula).length ≤
      1+2*clauseBound+clauseBound*3*((timeBound+atomBound+1)^2+
        PeriodicCNFFlatEncoding.forwardLiteralFieldBudget+5) := by
  have periodicWidth : (asPeriodic formula).WidthAtMost 3 := by
    intro clause member
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp ho
    simpa [PeriodicClause.WidthAtMost] using width old hm
  have forward : (asPeriodic formula).IsForwardLocal := by
    intro clause member literal hl
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp hl
    exact Or.inl rfl
  have atoms : PeriodicCNF.ClausesAtomsBelow (asPeriodic formula).clauses ((timeBound+atomBound+1)^2) := by
    intro clause member literal hl
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp ho
    obtain ⟨mapped,hmap,rfl⟩ := List.mem_map.mp hl
    obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hmap
    obtain ⟨ht,ha⟩ := ranges old hm source hs
    have pair := Nat.pair_lt_max_add_one_sq source.1.1 source.1.2
    have maxBound : max source.1.1 source.1.2+1 ≤ timeBound+atomBound+1 := by omega
    exact pair.trans_le (Nat.pow_le_pow_left maxBound 2)
  have count : (asPeriodic formula).clauses.length ≤ clauseBound := by
    simpa [asPeriodic,FiniteCNF.periodize,FiniteCNF.rename] using clauses
  exact PeriodicCNFFlatEncoding.finEncoding_encode_length_le (asPeriodic formula) 3 _ clauseBound
    periodicWidth forward atoms count

end LeanTrominoes.FiniteCNFFlatEncoding
