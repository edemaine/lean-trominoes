/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBatch

/-! # Flat natural-word formulas for dense Horn inputs

The formulas remove dependent finite-array indices from the encoding. A table
compiler can consequently prove its output by ordinary list/index arithmetic.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATBatch

variable {n p : ℕ}

theorem atomIndex_value (q : Fin p) (direction : Bool) (v : Fin n) :
    (atomIndex n p (q,direction,v)).val=(2*q.val+(if direction then 1 else 0))*n+v.val := by
  cases direction <;>
    simp [atomIndex,Equiv.prodAssoc,finProdFinEquiv,finTwoEquiv,Nat.add_comm,Nat.mul_comm ]

def ruleHeads (rs : List (Horn.Rule (Fin n))) : List ℕ :=
  rs.map (fun r => Horn.WordRAM.atomCode r.conclusion)

def occurrenceAtoms (rs : List (Horn.Rule (Fin n))) : List ℕ :=
  rs.flatMap (fun r => r.premises.map (fun a => a.val+1))

def occurrenceRules (rs : List (Horn.Rule (Fin n))) : List ℕ :=
  rs.zipIdx.flatMap (fun ar => List.replicate ar.1.premises.length ar.2)

theorem finRange_get (rs : List (Horn.Rule (Fin n))) :
    (List.finRange rs.length).map (fun i => rs[i.val])=rs := by
  calc
    _=(List.finRange rs.length).map rs.get := by
      apply List.map_congr_left
      intro i hi
      rfl
    _=rs := List.map_get_finRange rs

theorem finRange_zipIdx (rs : List (Horn.Rule (Fin n))) :
    (List.finRange rs.length).map (fun i => (rs[i.val],i.val))=rs.zipIdx := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

theorem array_finRange {V : Type} (array : Array V) :
    (List.finRange array.size).map (fun i => array[i])=array.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [Fin.getElem_fin]

theorem array_finRange_zipIdx {V : Type} (array : Array V) :
    (List.finRange array.size).map (fun i => (array[i],i.val))=array.toList.zipIdx := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [Fin.getElem_fin]

theorem words_of_rules (rs : List (Horn.Rule (Fin n))) :
    Horn.WordRAM.words ⟨n,⟨rs.toArray⟩⟩=
      [n,rs.length,(occurrenceAtoms rs).length]++ruleHeads rs++occurrenceAtoms rs++occurrenceRules rs := by
  have atoms : (Horn.Indexed.edges (⟨rs.toArray⟩ : Horn.Indexed.Input n)).map
      (fun ar => Horn.WordRAM.atomCode ar.1)=occurrenceAtoms rs := by
    have equal := congrArg (List.flatMap (fun r : Horn.Rule (Fin n) => r.premises.map (fun a => a.val+1))) (array_finRange rs.toArray)
    simpa only [Horn.Indexed.edges,List.toList_toArray,List.map_flatMap,
      List.map_map,List.flatMap_map,Horn.WordRAM.atomCode,occurrenceAtoms,Function.comp_def] using equal
  have ruleIds : (Horn.Indexed.edges (⟨rs.toArray⟩ : Horn.Indexed.Input n)).map
      (fun ar => ar.2.val)=occurrenceRules rs := by
    have equal := congrArg (List.flatMap (fun ar : Horn.Rule (Fin n) × ℕ => List.replicate ar.1.premises.length ar.2))
      (array_finRange_zipIdx rs.toArray)
    simpa only [Horn.Indexed.edges,List.toList_toArray,List.map_flatMap,
      List.map_map,List.flatMap_map,occurrenceRules,Function.comp_def,List.map_const'] using equal
  have heads : (List.finRange rs.toArray.size).map (fun i => Horn.WordRAM.atomCode (rs.toArray[i]).conclusion)=ruleHeads rs := by
    have equal := congrArg (List.map (fun r : Horn.Rule (Fin n) => Horn.WordRAM.atomCode r.conclusion)) (array_finRange rs.toArray)
    simpa only [List.map_map,Function.comp_def,ruleHeads,List.toList_toArray] using equal
  have occurrenceLength : (Horn.Indexed.edges (⟨rs.toArray⟩ : Horn.Indexed.Input n)).length=(occurrenceAtoms rs).length := by
    simpa only [List.length_map] using congrArg List.length atoms
  simpa only [Horn.WordRAM.words,List.size_toArray,occurrenceLength,heads,atoms,ruleIds]

end LeanTrominoes.ImplicationGraph.TwoSATBatch
