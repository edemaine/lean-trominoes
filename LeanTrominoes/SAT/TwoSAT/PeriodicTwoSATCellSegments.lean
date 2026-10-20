/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellTables

/-! # Arithmetic generation of the Horn head and occurrence segments -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph ImplicationGraph.TwoSATExpression
variable {d : ℕ}

abbrev tablePeriod (raw : Raw.Input d) := PeriodicTwoSAT.period (Fin (raw.1+1)) d
abbrev tableEdges (raw : Raw.Input d) := edgeList raw (tablePeriod raw)
abbrev tableVertices (raw : Raw.Input d) := (raw.1+1)*2*(tablePeriod raw)^d
abbrev tableAtoms (raw : Raw.Input d) := raw.1*2*tableVertices raw+1

def headWords (raw : Raw.Input d) : List ℕ :=
  TwoSATBatch.factHeads (liftedPairs raw.1 d)++
    (List.replicate raw.1 0++(TwoSATBatch.edgeHeads (p:=raw.1) (tableEdges raw)++
      (clauseFlags raw.2).map (fun flag => if flag then tableAtoms raw else 0)))

def atomWords (raw : Raw.Input d) : List ℕ :=
  TwoSATBatch.negativeAtoms (liftedPairs raw.1 d)++TwoSATBatch.edgeAtoms (p:=raw.1) (tableEdges raw)

def ruleWords (raw : Raw.Input d) : List ℕ :=
  TwoSATBatch.negativeRuleIds raw.1++TwoSATBatch.edgeRuleIds raw.1 (tableEdges raw).length

theorem headWords_length (raw : Raw.Input d) :
    (headWords raw).length=3*raw.1+2*raw.1*(tableEdges raw).length+raw.2.length := by
  simp [headWords,TwoSATBatch.factHeads,TwoSATBatch.edgeHeads,clauseFlags]
  ring

theorem atomWords_length (raw : Raw.Input d) :
    (atomWords raw).length=2*raw.1+2*raw.1*(tableEdges raw).length := by
  simp [atomWords,TwoSATBatch.negativeAtoms,TwoSATBatch.edgeAtoms]
  ring

theorem ruleWords_length (raw : Raw.Input d) : (ruleWords raw).length=(atomWords raw).length := by
  simp [ruleWords,atomWords_length,TwoSATBatch.negativeRuleIds,TwoSATBatch.edgeRuleIds]
  ring

theorem getD_append_left (xs ys : List ℕ) (i : ℕ) (inside : i < xs.length) :
    (xs++ys)[i]?.getD 0=xs[i]?.getD 0 := by rw [List.getElem?_append_left inside]

theorem getD_append_right (xs ys : List ℕ) (i : ℕ) (outside : xs.length ≤ i) :
    (xs++ys)[i]?.getD 0=ys[i-xs.length]?.getD 0 := by rw [List.getElem?_append_right outside]

theorem markerCell_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (header : Metadata raw (tablePeriod raw) env) (e : Expression) (i : Fin raw.2.length)
    (value : e.eval env memory = i.val) :
    (flag d e).eval env memory*env 12 =
      (((clauseFlags raw.2).map (fun flag => if flag then tableAtoms raw else 0))[i.val]?.getD 0 : ℕ) := by
  have flagValue := Raw.record_eval raw sourceBase env memory source baseValue header.clauses e 0
    (by dsimp [Raw.recordSize]; omega)
  norm_num at flagValue
  rw [show (flag d e).eval env memory = (Raw.clauseWords (Raw.recordAt raw (e.eval env memory)))[0]?.getD 0 from flagValue,
    value,Raw.recordAt_original raw i.val i.isLt,Raw.flag_word,Option.getD_some,header.atoms]
  simp only [clauseFlags,List.map_map,Function.comp_def,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
    Option.map_some,Option.getD_some]
  cases raw.2[i.val] <;> simp [Raw.validFlag,tableAtoms,tableVertices,tablePeriod]

theorem headCell_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (header : Metadata raw (tablePeriod raw) env) (e : Expression) (i : ℕ) (iBound : i < (headWords raw).length)
    (value : e.eval env memory = i) :
    (headCell d e).eval env memory = ((headWords raw)[i]?.getD 0 : ℕ) := by
  have strictInside : (i : ℤ) < env 2 := by
    rw [header.length]
    have bound := iBound
    rw [headWords_length,edgeList_length] at bound
    exact_mod_cast (by omega : i < 4+(3*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))+raw.2.length)+
      2*(2*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))))
  have inside : i ≤ (env 2 : ℤ) := by
    rw [header.length]
    have bound := iBound
    rw [headWords_length,edgeList_length] at bound
    exact_mod_cast (by omega : i ≤ 4+(3*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))+raw.2.length)+
      2*(2*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))))
  rw [headCell_selected raw (tablePeriod raw) env memory header e (by rw [value]; positivity) (by rw [value]; exact inside)]
  have factLength : (TwoSATBatch.factHeads (liftedPairs raw.1 d)).length=raw.1*2 := by simp [TwoSATBatch.factHeads]
  have edgeLength : (TwoSATBatch.edgeHeads (p:=raw.1) (tableEdges raw)).length=(raw.1*2)*(tableEdges raw).length := by simp [TwoSATBatch.edgeHeads]
  have copiesComm : raw.1*2*(tableEdges raw).length = 2*raw.1*(tableEdges raw).length := by ring
  by_cases first : i < raw.1*2
  · have test : e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : i < 2*raw.1)
    rw [if_pos test,headWords,getD_append_left _ _ _ (by rwa [factLength])]
    exact sourceFact_eval raw env memory header ⟨i,first⟩ e value
  · have test : ¬e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : ¬i < 2*raw.1)
    rw [if_neg test,headWords,getD_append_right _ _ _ (by rw [factLength]; omega),factLength]
    by_cases second : i < 3*raw.1
    · have test2 : e.eval env memory < 3*env 6 := by rw [value,header.numVars]; exact_mod_cast second
      rw [if_pos test2,getD_append_left _ _ _ (by simp; omega)]
      simp [List.getElem?_replicate,show i-raw.1*2 < raw.1 by omega]
    · have test2 : ¬e.eval env memory < 3*env 6 := by rw [value,header.numVars]; exact_mod_cast second
      rw [if_neg test2,getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      have subtract : i-raw.1*2-raw.1=i-3*raw.1 := by omega
      rw [subtract]
      by_cases third : i < 3*raw.1+2*raw.1*(tableEdges raw).length
      · have test3 : e.eval env memory < 3*env 6+2*env 6*env 11 := by
          rw [value,header.numVars,header.edges]
          rw [edgeList_length] at third
          exact_mod_cast third
        rw [if_pos test3,getD_append_left _ _ _ (by rw [edgeLength]; omega)]
        apply unaryHead_eval raw sourceBase (tablePeriod raw) env memory source baseValue header
          ⟨i-3*raw.1,by simpa only [tableEdges] using (show i-3*raw.1 < (raw.1*2)*(tableEdges raw).length by omega)⟩
        simp only [mask,sub_eval,mod_eval,three,mul_eval,constant_eval,input_eval,value,header.numVars]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      · have test3 : ¬e.eval env memory < 3*env 6+2*env 6*env 11 := by
          rw [value,header.numVars,header.edges]
          rw [edgeList_length] at third
          exact_mod_cast third
        rw [if_neg test3,getD_append_right _ _ _ (by rw [edgeLength]; omega),edgeLength]
        have markerSmall : i-3*raw.1-(raw.1*2)*(tableEdges raw).length < raw.2.length := by
          have bound := iBound
          rw [headWords_length] at bound
          omega
        apply markerCell_eval raw sourceBase env memory source baseValue header _
          ⟨i-3*raw.1-(raw.1*2)*(tableEdges raw).length,markerSmall⟩
        simp only [sub_eval,add_eval,mul_eval,three,two,constant_eval,input_eval,value,header.numVars,header.edges]
        rw [Nat.cast_sub (by omega : (raw.1*2)*(tableEdges raw).length ≤ i-3*raw.1),
          Nat.cast_sub (by omega : 3*raw.1 ≤ i)]
        simp only [tableEdges,edgeList_length]
        push_cast
        ring

theorem atomCell_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (header : Metadata raw (tablePeriod raw) env) (e : Expression) (i : ℕ) (iBound : i < (atomWords raw).length)
    (value : e.eval env memory = i) :
    (atomCell d e).eval env memory = ((atomWords raw)[i]?.getD 0 : ℕ) := by
  have strictInside : (i : ℤ) < env 2 := by
    rw [header.length]
    have bound := iBound
    rw [atomWords_length,edgeList_length] at bound
    exact_mod_cast (by omega : i < 4+(3*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))+raw.2.length)+
      2*(2*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))))
  rw [atomCell_selected raw (tablePeriod raw) env memory header e (by rw [value]; positivity)
    (by rw [value]; omega)]
  have negativeLength : (TwoSATBatch.negativeAtoms (liftedPairs raw.1 d)).length=raw.1*2 := by simp [TwoSATBatch.negativeAtoms]
  have copiesComm : raw.1*2*(tableEdges raw).length = 2*raw.1*(tableEdges raw).length := by ring
  by_cases first : i < raw.1*2
  · have test : e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : i < 2*raw.1)
    rw [if_pos test,atomWords,getD_append_left _ _ _ (by rwa [negativeLength])]
    exact oppositeTarget_eval raw env memory header ⟨i,first⟩ e value
  · have test : ¬e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : ¬i < 2*raw.1)
    rw [if_neg test,atomWords,getD_append_right _ _ _ (by rw [negativeLength]; omega),negativeLength]
    have bound := iBound
    rw [atomWords_length] at bound
    apply unaryAtom_eval raw sourceBase (tablePeriod raw) env memory source baseValue header
      ⟨i-raw.1*2,by simpa only [tableEdges] using (show i-raw.1*2 < (raw.1*2)*(tableEdges raw).length by omega)⟩
    simp only [mask,sub_eval,mod_eval,two,mul_eval,constant_eval,input_eval,value,header.numVars]
    rw [Int.emod_eq_of_lt (by omega) (by omega),Nat.cast_sub (by omega : raw.1*2 ≤ i)]
    push_cast
    ring

theorem ruleCell_eval (raw : Raw.Input d) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw (tablePeriod raw) env) (e : Expression) (i : ℕ) (iBound : i < (ruleWords raw).length)
    (value : e.eval env memory = i) :
    (ruleCell e).eval env memory = ((ruleWords raw)[i]?.getD 0 : ℕ) := by
  have strictInside : (i : ℤ) < env 2 := by
    rw [header.length]
    have bound := iBound
    rw [ruleWords_length,atomWords_length,edgeList_length] at bound
    exact_mod_cast (by omega : i < 4+(3*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))+raw.2.length)+
      2*(2*raw.1+2*raw.1*((tablePeriod raw)^d*(raw.2.length*2))))
  rw [ruleCell_selected raw (tablePeriod raw) env memory header e (by rw [value]; positivity)
    (by rw [value]; omega)]
  have negativeLength : (TwoSATBatch.negativeRuleIds raw.1).length=raw.1*2 := by simp [TwoSATBatch.negativeRuleIds]
  have copiesComm : raw.1*2*(tableEdges raw).length = 2*raw.1*(tableEdges raw).length := by ring
  by_cases first : i < raw.1*2
  · have test : e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : i < 2*raw.1)
    rw [if_pos test,ruleWords,getD_append_left _ _ _ (by rwa [negativeLength])]
    simp only [TwoSATBatch.negativeRuleIds,List.getElem?_ofFn,first,reduceDIte,Option.getD_some,value,header.numVars]
    push_cast
    rfl
  · have test : ¬e.eval env memory < 2*env 6 := by rw [value,header.numVars]; exact_mod_cast (by omega : ¬i < 2*raw.1)
    rw [if_neg test,ruleWords,getD_append_right _ _ _ (by rw [negativeLength]; omega),negativeLength]
    have bound := iBound
    rw [ruleWords_length,atomWords_length] at bound
    have copySmall : i-raw.1*2 < (raw.1*2)*(tableEdges raw).length := by omega
    simp only [TwoSATBatch.edgeRuleIds,List.getElem?_ofFn,copySmall,reduceDIte,Option.getD_some,
      mask,sub_eval,mod_eval,two,mul_eval,constant_eval,input_eval,value,header.numVars]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega : raw.1*2 ≤ i)]
    push_cast
    ring

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
