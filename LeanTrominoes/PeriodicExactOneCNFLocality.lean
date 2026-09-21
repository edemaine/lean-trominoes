/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneCNF
import LeanTrominoes.PeriodicCNFLineSearch
import LeanTrominoes.PeriodicCNFVariableSizeBounds

/-! # Local one-dimensional exact-one SAT reduces to local CNF

Pairwise exclusion introduces no variables or offsets. For width three,
the clause-plus-literal size grows by at most a factor of four.
-/
namespace LeanTrominoes.PeriodicExactOneCNF
open PeriodicOneInThree
variable {V : Type}

private theorem mutex_pair (c d : PeriodicClause V) (hd : d ∈ mutex c) :
    ∃ l ∈ c, ∃ r ∈ c, d = [negate l,negate r] := by
  induction c with
  | nil => simp [mutex] at hd
  | cons l ls ih =>
    simp only [mutex,List.mem_append,List.mem_map] at hd
    rcases hd with ⟨r,hr,rfl⟩ | hd
    · exact ⟨l,by simp,r,by simp [hr],rfl⟩
    · obtain ⟨a,ha,b,hb,rfl⟩ := ih hd
      exact ⟨a,by simp [ha],b,by simp [hb],rfl⟩

theorem isOneDimensional_iff (f : PeriodicCNF V) :
    (formula f).IsOneDimensional ↔ f.IsOneDimensional := by
  constructor
  · intro h c hc l hl
    exact h c (List.mem_flatMap.mpr ⟨c,hc,by simp [clause]⟩) l hl
  · intro h d hd l hl
    obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h d hc l hl
    · obtain ⟨a,ha,b,hb,rfl⟩ := mutex_pair c d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl
      · exact h c hc a ha
      · exact h c hc b hb

theorem isLocal_iff (f : PeriodicCNF V) :
    (formula f).IsLocal ↔ f.IsLocal := by
  constructor
  · intro h c hc
    exact h c (List.mem_flatMap.mpr ⟨c,hc,by simp [clause]⟩)
  · intro h d hd
    obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h d hc
    · obtain ⟨a,ha,b,hb,rfl⟩ := mutex_pair c d hd
      intro l hl r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl hr
      rcases hl with rfl | rfl <;> rcases hr with rfl | rfl
      · exact h c hc a ha a ha
      · exact h c hc a ha b hb
      · exact h c hc b hb a ha
      · exact h c hc b hb b hb

theorem width_three (f : PeriodicCNF V) (hw : f.WidthAtMost 3) :
    (formula f).WidthAtMost 3 := by
  intro d hd
  obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hw d hc
  · obtain ⟨a,_,b,_,rfl⟩ := mutex_pair c d hd
    simp [PeriodicClause.WidthAtMost]

private theorem clause_size (c : PeriodicClause V) (hw : c.length ≤ 3) :
    (clause c).length + ((clause c).map List.length).sum ≤ 4*(1+c.length) := by
  rcases c with _ | ⟨a,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨b,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨d,c⟩
  · simp [clause,mutex]
  cases c with
  | nil => simp [clause,mutex]
  | cons e c => simp only [List.length_cons] at hw; omega

theorem presentationSize_le (f : PeriodicCNF V) (hw : f.WidthAtMost 3) :
    (formula f).presentationSize ≤ 4*f.presentationSize := by
  rcases f with ⟨cs⟩
  induction cs with
  | nil => simp [formula,PeriodicCNF.presentationSize,PeriodicCNF.presentationLiteralCount]
  | cons c cs ih =>
    have hc := clause_size c (hw c (by simp))
    have rest := ih (fun d hd => hw d (by simp [hd]))
    simp only [formula,PeriodicCNF.presentationSize,PeriodicCNF.presentationLiteralCount,List.flatMap_cons,
      List.length_cons,List.length_append,List.flatten_append,List.length_flatten,
      List.map_cons,List.sum_cons] at rest ⊢
    omega

private theorem clause_literals (c : PeriodicClause V) (hw : c.length ≤ 3) :
    ((clause c).map List.length).sum ≤ 3*c.length := by
  rcases c with _ | ⟨a,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨b,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨d,c⟩
  · simp [clause,mutex]
  cases c with
  | nil => simp [clause,mutex]
  | cons e c => simp only [List.length_cons] at hw; omega

theorem literalCount_le (f : PeriodicCNF V) (hw : f.WidthAtMost 3) :
    (formula f).presentationLiteralCount ≤ 3*f.presentationLiteralCount := by
  rcases f with ⟨cs⟩
  induction cs with
  | nil => simp [formula,PeriodicCNF.presentationLiteralCount]
  | cons c cs ih =>
    have hc := clause_literals c (hw c (by simp))
    have rest := ih (fun d hd => hw d (by simp [hd]))
    simp only [formula,PeriodicCNF.presentationLiteralCount,List.flatMap_cons,
      List.flatten_append,List.length_append,List.length_flatten,
      List.map_cons,List.sum_cons] at rest ⊢
    omega

private theorem occurrences_length (f : PeriodicCNF V) :
    f.variableOccurrences.length = f.presentationLiteralCount := by
  simp only [PeriodicCNF.variableOccurrences,PeriodicCNF.presentationLiteralCount,
    List.length_flatMap,List.length_map,List.length_flatten]

/-- The CNF window for a width-three exact-one instance needs at most nine
bits per symbol of the original native flat encoding. -/
theorem state_bits_le_encoding (f : PeriodicCNF Nat) (hw : f.WidthAtMost 3) :
    3*(formula f).variableOccurrences.length ≤
      9*(PeriodicCNFFlatEncoding.finEncoding.encode f).length := by
  have original := PeriodicCNF.LineWindow.state_bits_le_encoding f
  have expansion := literalCount_le f hw
  rw [← occurrences_length,← occurrences_length] at expansion
  omega

/-- The line language uses the same plane syntax, with all vertical offsets zero. -/
def LocalOneDimensionalSAT (f : PeriodicCNF V) : Prop :=
  f.IsOneDimensional ∧ f.IsLocal ∧ PeriodicOneInThree.Satisfiable f

/-- Executable decision procedure, including rejection of nonlocal inputs. -/
def check [DecidableEq V] (f : PeriodicCNF V) : Bool :=
  PeriodicCNF.LineWindow.check (formula f)

theorem check_correct [DecidableEq V] (f : PeriodicCNF V) :
    check f = true ↔ LocalOneDimensionalSAT f := by
  rw [check,PeriodicCNF.LineWindow.check_correct,isOneDimensional_iff,isLocal_iff,satisfiable_iff]
  rfl

/-- Width-three exact-one SAT, without a supplied drawing. -/
def LocalOneDimensionalThreeSAT (f : PeriodicCNF V) : Prop :=
  f.WidthAtMost 3 ∧ LocalOneDimensionalSAT f

def LocalOneDimensionalThreeSATThree [DecidableEq V] (f : PeriodicCNF V) : Prop :=
  f.OccurrencesAtMost 3 ∧ LocalOneDimensionalThreeSAT f

def checkThree [DecidableEq V] (f : PeriodicCNF V) : Bool :=
  (f.clauses.all fun c => decide (c.length ≤ 3)) && check f

theorem checkThree_correct [DecidableEq V] (f : PeriodicCNF V) :
    checkThree f = true ↔ LocalOneDimensionalThreeSAT f := by
  simp only [checkThree,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,check_correct]
  rfl

def occurrenceCheck [DecidableEq V] (f : PeriodicCNF V) : Bool :=
  f.variableOccurrences.all fun v => decide (f.variableOccurrences.count v ≤ 3)

theorem occurrenceCheck_correct [DecidableEq V] (f : PeriodicCNF V) :
    occurrenceCheck f = true ↔ f.OccurrencesAtMost 3 := by
  simp only [occurrenceCheck,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h v
    by_cases hv : v ∈ f.variableOccurrences
    · exact h v hv
    · have zero : f.variableOccurrences.count v = 0 := List.count_eq_zero.mpr hv
      change f.variableOccurrences.count v ≤ 3
      omega
  · intro h v _
    exact h v

def checkThreeThree [DecidableEq V] (f : PeriodicCNF V) : Bool :=
  occurrenceCheck f && checkThree f

theorem checkThreeThree_correct [DecidableEq V] (f : PeriodicCNF V) :
    checkThreeThree f = true ↔ LocalOneDimensionalThreeSATThree f := by
  simp only [checkThreeThree,Bool.and_eq_true,occurrenceCheck_correct,checkThree_correct]
  rfl

end LeanTrominoes.PeriodicExactOneCNF
