/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellSegments

/-! # Correctness of every word produced by the original-input constructor -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d : ℕ}

def fullWords (raw : Raw.Input d) : List ℕ :=
  [3+(headWords raw).length+2*(atomWords raw).length,tableAtoms raw,
    (headWords raw).length,(atomWords raw).length]++
      (headWords raw++(atomWords raw++ruleWords raw))

theorem fullWords_length (raw : Raw.Input d) :
    (fullWords raw).length=4+(headWords raw).length+2*(atomWords raw).length := by
  simp [fullWords,ruleWords_length]
  omega

theorem uniformWords (raw : Raw.Input d) :
    Horn.WordRAM.words (uniformInput raw.2)=
      [tableAtoms raw,(headWords raw).length,(atomWords raw).length]++
        (headWords raw++(atomWords raw++ruleWords raw)) := by
  rw [headWords_length,atomWords_length]
  unfold uniformInput
  rw [words_marked_batch]
  simp only [clauseFlags,List.length_map]
  simp only [headWords,atomWords,ruleWords,tableEdges,edgeList,tableAtoms,tableVertices,tablePeriod,List.append_assoc,clauseFlags]

theorem fullWords_uniform (raw : Raw.Input d) :
    fullWords raw=(Horn.WordRAM.words (uniformInput raw.2)).length::Horn.WordRAM.words (uniformInput raw.2) := by
  rw [uniformWords]
  simp [fullWords,ruleWords_length]
  omega

theorem cast_getD (xs : List ℕ) (i : ℕ) :
    ((xs.map Int.ofNat)[i]?.getD 0 : ℤ)=(xs[i]?.getD 0 : ℕ) := by
  simp only [List.getElem?_map]
  cases xs[i]? <;> rfl

theorem fullWords_initial (raw : Raw.Input d) (i : ℕ) :
    ((initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.2))).memory i) =
      ((fullWords raw)[i]?.getD 0 : ℕ) := by
  rw [fullWords_uniform]
  cases i with
  | zero => simp [initial,Horn.WordRAM.encode]
  | succ i => simpa only [initial,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
      List.getElem?_cons_succ,Horn.WordRAM.encode] using cast_getD (Horn.WordRAM.words (uniformInput raw.2)) i

theorem cell_selected (raw : Raw.Input d) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw (tablePeriod raw) env) (nonnegative : 0 ≤ env 1) (inside : env 1 ≤ env 2) :
    (cell d).eval env memory =
      if env 1 < 1 then env 2-1 else if env 1 < 2 then env 12 else if env 1 < 3 then env 13
      else if env 1 < 4 then env 14 else if env 1 < 4+env 13 then
        (headCell d (mask (sub position (constant 4)))).eval env memory
      else if env 1 < 4+env 13+env 14 then
        (atomCell d (mask (sub position (add (constant 4) rules)))).eval env memory
      else (ruleCell (mask (sub position (add (add (constant 4) rules) occurrences)))).eval env memory := by
  have ruleNonnegative : 0 ≤ env 13 := by rw [header.rules]; positivity
  have occurrenceNonnegative : 0 ≤ env 14 := by rw [header.occurrences]; positivity
  have lengthValue : env 2 = 4+env 13+2*env 14 := by rw [header.length,header.rules,header.occurrences]
  have lengthPositive : 0 < env 2 := by omega
  unfold cell
  repeat rw [select_eval]
  all_goals try simp only [add_eval,sub_eval,constant_eval,input_eval]
  all_goals omega

theorem cell_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (header : Metadata raw (tablePeriod raw) env) (i : ℕ) (iBound : i < (fullWords raw).length)
    (value : env 1 = i) :
    (cell d).eval env memory = ((fullWords raw)[i]?.getD 0 : ℕ) := by
  have rulesValue : env 13 = (headWords raw).length := by
    rw [header.rules,headWords_length,edgeList_length]
    push_cast
    rfl
  have occurrencesValue : env 14 = (atomWords raw).length := by
    rw [header.occurrences,atomWords_length,edgeList_length]
    push_cast
    rfl
  have lengthValue : env 2 = (fullWords raw).length := by
    rw [header.length,fullWords_length,headWords_length,atomWords_length,edgeList_length]
    push_cast
    rfl
  have natLength : (fullWords raw).length = 4+(headWords raw).length+(atomWords raw).length+(ruleWords raw).length := by
    rw [fullWords_length,ruleWords_length]
    omega
  rw [cell_selected raw env memory header (by rw [value]; positivity) (by rw [value,lengthValue]; exact_mod_cast Nat.le_of_lt iBound)]
  by_cases first : i < 4
  · interval_cases i <;> simp [value,fullWords,lengthValue,ruleWords_length,rulesValue,occurrencesValue,header.atoms,tableAtoms,tableVertices,tablePeriod] <;> ring
  · have t1 : ¬env 1 < 1 := by rw [value]; omega
    have t2 : ¬env 1 < 2 := by rw [value]; omega
    have t3 : ¬env 1 < 3 := by rw [value]; omega
    have t4 : ¬env 1 < 4 := by rw [value]; omega
    rw [if_neg t1,if_neg t2,if_neg t3,if_neg t4,fullWords,getD_append_right _ _ _ (by simp; omega)]
    simp only [List.length_cons,List.length_nil]
    by_cases heads : i < 4+(headWords raw).length
    · have test : env 1 < 4+env 13 := by rw [value,rulesValue]; exact_mod_cast heads
      rw [if_pos test,getD_append_left _ _ _ (by omega)]
      apply headCell_eval raw sourceBase env memory source baseValue header _ (i-4) (by omega)
      simp only [mask,sub_eval,mod_eval,constant_eval,input_eval,value]
      have subtract : (i : ℤ)-4 = (i-4 : ℕ) := by rw [Nat.cast_sub (by omega : 4 ≤ i)]; norm_num
      rw [subtract,Int.emod_eq_of_lt (by positivity) (by rw [lengthValue]; exact_mod_cast (by omega : i-4 < (fullWords raw).length))]
    · have test : ¬env 1 < 4+env 13 := by rw [value,rulesValue]; exact_mod_cast heads
      rw [if_neg test,getD_append_right _ _ _ (by omega)]
      by_cases atoms : i < 4+(headWords raw).length+(atomWords raw).length
      · have test2 : env 1 < 4+env 13+env 14 := by rw [value,rulesValue,occurrencesValue]; exact_mod_cast atoms
        rw [if_pos test2,getD_append_left _ _ _ (by omega)]
        apply atomCell_eval raw sourceBase env memory source baseValue header _
          (i-4-(headWords raw).length) (by omega)
        simp only [mask,sub_eval,mod_eval,add_eval,constant_eval,input_eval,value,rulesValue]
        have subtract : (i : ℤ)-(4+(headWords raw).length) = (i-4-(headWords raw).length : ℕ) := by
          rw [Nat.cast_sub (by omega : (headWords raw).length ≤ i-4),Nat.cast_sub (by omega : 4 ≤ i)]
          push_cast
          ring
        rw [subtract,Int.emod_eq_of_lt (by positivity) (by rw [lengthValue]; exact_mod_cast (by omega : i-4-(headWords raw).length < (fullWords raw).length))]
      · have test2 : ¬env 1 < 4+env 13+env 14 := by rw [value,rulesValue,occurrencesValue]; exact_mod_cast atoms
        rw [if_neg test2,getD_append_right _ _ _ (by omega)]
        apply ruleCell_eval raw env memory header _ (i-4-(headWords raw).length-(atomWords raw).length) (by omega)
        simp only [mask,sub_eval,mod_eval,add_eval,constant_eval,input_eval,value,rulesValue,occurrencesValue]
        have subtract : (i : ℤ)-(4+(headWords raw).length+(atomWords raw).length) =
            (i-4-(headWords raw).length-(atomWords raw).length : ℕ) := by
          rw [Nat.cast_sub (by omega : (atomWords raw).length ≤ i-4-(headWords raw).length),
            Nat.cast_sub (by omega : (headWords raw).length ≤ i-4),Nat.cast_sub (by omega : 4 ≤ i)]
          push_cast
          ring
        rw [subtract,Int.emod_eq_of_lt (by positivity) (by rw [lengthValue]; exact_mod_cast (by omega :
          i-4-(headWords raw).length-(atomWords raw).length < (fullWords raw).length))]

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
