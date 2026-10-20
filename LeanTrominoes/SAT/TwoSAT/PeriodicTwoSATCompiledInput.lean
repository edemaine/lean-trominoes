/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATMarkers
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawInput

/-! # The complete Horn table generated from original local clause records -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph ImplicationGraph
variable {n d : ℕ}

theorem clauseArcs_normalize (c : Clause (Fin n) d) : clauseArcs (normalizeClause c)=clauseArcs c := by
  cases c with
  | none => rfl
  | some pair =>
    rcases pair with ⟨a,b⟩
    simp [normalizeClause,clauseArcs,neg_sub]

theorem arcs_normalize (formula : Formula (Fin n) d) : arcs (normalize formula)=arcs formula := by
  simp [arcs,normalize,List.flatMap_map,clauseArcs_normalize]

theorem none_normalize (formula : Formula (Fin n) d) : none ∈ normalize formula ↔ none ∈ formula := by
  constructor
  · intro member
    obtain ⟨c,hc,eq⟩ := List.mem_map.mp member
    cases c with
    | none => exact hc
    | some pair => simp [normalizeClause] at eq
  · intro member
    exact List.mem_map.mpr ⟨none,member,rfl⟩

theorem localDifferences_cover (formula : Formula (Fin n) d) (locality : LocalDifferences formula) :
    Satisfiable formula ↔ none ∉ formula ∧ ∀ a : Fin n,
      ¬(CoverReach (arcs formula) (period (Fin n) d) ((a,true),0) ((a,false),0) ∧
        CoverReach (arcs formula) (period (Fin n) d) ((a,false),0) ((a,true),0)) := by
  rw [← normalize_satisfiable formula,satisfiable_iff_cover _ (normalize_local formula locality),
    arcs_normalize,none_normalize]

def clauseFlags (formula : Formula (Fin n) d) : List Bool := formula.map Option.isSome

theorem clauseFlags_correct (formula : Formula (Fin n) d) :
    (∀ flag ∈ clauseFlags formula, flag=true) ↔ none ∉ formula := by
  constructor
  · intro all member
    have bad := all false (List.mem_map.mpr ⟨none,member,rfl⟩)
    contradiction
  · intro noEmpty flag member
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp member
    cases c with
    | none => exact False.elim (noEmpty hc)
    | some pair => rfl

def fullInput (positive : 0<n) (formula : Formula (Fin n) d) : Horn.WordRAM.Input :=
  ⟨n*2*(n*2*(period (Fin n) d)^d)+1,
    appendMarkers (TwoSATBatch.input (paddedCoverEdges positive formula (period (Fin n) d)) (pairs n d))
      (clauseFlags formula)⟩

theorem fullInput_correct (positive : 0<n) (formula : Formula (Fin n) d) (locality : LocalDifferences formula) :
    Horn.Satisfiable (fullInput positive formula).2.rules.toList ↔ Satisfiable formula := by
  rw [localDifferences_cover formula locality]
  change Horn.Satisfiable (appendMarkers _ _).rules.toList ↔ _
  rw [appendMarkers_correct,TwoSATBatch.input_correct,clauseFlags_correct]
  simp only [TwoSATBatch.Consistent,pairs,paddedCoverEdges_reach]
  tauto

theorem fullInput_rules (positive : 0<n) (formula : Formula (Fin n) d) :
    (fullInput positive formula).2.rules.size=3*n+2*n*(2*formula.length*(period (Fin n) d)^d)+formula.length := by
  simp [fullInput,appendMarkers_rules,TwoSATBatch.input_rules,paddedCoverEdges_length,clauseFlags]

theorem fullInput_occurrences (positive : 0<n) (formula : Formula (Fin n) d) :
    (Horn.Indexed.edges (fullInput positive formula).2).length=2*n+2*n*(2*formula.length*(period (Fin n) d)^d) := by
  simp [fullInput,appendMarkers_occurrences,TwoSATBatch.input_occurrences,paddedCoverEdges_length]

theorem fullInput_size (positive : 0<n) (formula : Formula (Fin n) d) :
    Horn.WordRAM.size (fullInput positive formula)=
      4*n*n*(period (Fin n) d)^d+5*n+8*n*formula.length*(period (Fin n) d)^d+formula.length+2 := by
  simp only [Horn.WordRAM.size,fullInput,appendMarkers_rules,appendMarkers_occurrences,
    TwoSATBatch.input_rules,TwoSATBatch.input_occurrences,paddedCoverEdges_length,clauseFlags,List.length_map]
  ring

end LeanTrominoes.PeriodicTwoSAT.WordRAM
