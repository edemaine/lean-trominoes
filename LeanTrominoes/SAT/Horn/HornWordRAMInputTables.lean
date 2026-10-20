/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMIndexArrays

/-! # The input tables read by the Horn RAM program

These equalities connect physical input cells to the original rules and
premise occurrences. The encoding contains neither an index nor a solution.
-/
namespace LeanTrominoes.Horn.WordRAM

theorem atomCode_injective {n : ℕ} : Function.Injective (@atomCode n) := by
  intro a b same
  cases a <;> cases b <;> simp_all [atomCode,Fin.ext_iff]

private theorem word_slice (input : Input) (prior values rest : List ℕ)
    (table : words input=prior++values++rest) (i : ℕ) (within : i<values.length) :
    (initialData input).2 (prior.length+1+i)=values[i] := by
  have address : prior.length+1+i≠0 := by omega
  simp only [initialData,address,ite_false]
  have offset : prior.length+1+i-1=prior.length+i := by omega
  rw [offset,table,List.append_assoc,List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left within,List.getElem?_eq_getElem within]

theorem initialContents_head (input : Input) (r : Indexed.RuleId input.2) :
    initialContents input Slot.heads r.val=atomCode (Indexed.head input.2 r) := by
  let heads := (List.finRange input.2.rules.size).map (fun i => atomCode input.2.rules[i].conclusion)
  have read := word_slice input [input.1,input.2.rules.size,(Indexed.edges input.2).length]
    heads ((Indexed.edges input.2).map (fun ar => atomCode ar.1)++
      (Indexed.edges input.2).map (fun ar => ar.2.val))
    (by simp [words,heads,List.append_assoc]) r.val (by simpa [heads] using r.isLt)
  simpa [initialContents,Layout.ofInput,Layout.base,Slot.heads,heads,Indexed.head] using read

theorem initialContents_edgeAtom (input : Input) (i : ℕ) (within : i<(Indexed.edges input.2).length) :
    initialContents input Slot.edgeAtoms i=atomCode (Indexed.edges input.2)[i].1 := by
  let heads := (List.finRange input.2.rules.size).map (fun r => atomCode input.2.rules[r].conclusion)
  have read := word_slice input ([input.1,input.2.rules.size,(Indexed.edges input.2).length]++heads)
    ((Indexed.edges input.2).map (fun ar => atomCode ar.1))
    ((Indexed.edges input.2).map (fun ar => ar.2.val)) rfl i (by simpa using within)
  have offset : ([input.1,input.2.rules.size,(Indexed.edges input.2).length]++heads).length+1+i=4+input.2.rules.size+i := by simp [heads]; omega
  rw [offset] at read
  simpa [initialContents,Layout.ofInput,Layout.base,Slot.edgeAtoms] using read

theorem initialContents_edgeRule (input : Input) (i : ℕ) (within : i<(Indexed.edges input.2).length) :
    initialContents input Slot.edgeRules i=(Indexed.edges input.2)[i].2.val := by
  let heads := (List.finRange input.2.rules.size).map (fun r => atomCode input.2.rules[r].conclusion)
  have read := word_slice input
    (([input.1,input.2.rules.size,(Indexed.edges input.2).length]++heads)++
      (Indexed.edges input.2).map (fun ar => atomCode ar.1))
    ((Indexed.edges input.2).map (fun ar => ar.2.val)) []
    (by simp [words,heads]) i (by simpa using within)
  have offset : (([input.1,input.2.rules.size,(Indexed.edges input.2).length]++heads)++(Indexed.edges input.2).map (fun ar => atomCode ar.1)).length+1+i=4+input.2.rules.size+(Indexed.edges input.2).length+i := by simp [heads]; omega
  rw [offset] at read
  simpa [initialContents,Layout.ofInput,Layout.base,Slot.edgeRules] using read

end LeanTrominoes.Horn.WordRAM
