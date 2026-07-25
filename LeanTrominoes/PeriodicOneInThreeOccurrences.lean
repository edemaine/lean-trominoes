import LeanTrominoes.PeriodicOccurrences
import LeanTrominoes.PeriodicOneInThreeCorrectness

/-!
# Occurrence bound for the periodic 1-in-3SAT reduction

Each source literal appears once in its clause gadget.  The two choice
variables appear twice, each slack variable appears once, and each padding
variable appears once positively and once in its forcing clause.  Clause
indices make auxiliaries belonging to distinct source-clause occurrences
different even when the source clauses are syntactically equal.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

instance lawfulBEqSum {First Second : Type*}
    [BEq First] [LawfulBEq First] [BEq Second] [LawfulBEq Second] :
    LawfulBEq (Sum First Second) where
  eq_of_beq {first second} equal := by
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            change (first == second) = true at equal
            exact congrArg Sum.inl (eq_of_beq equal)
        | inr second =>
            change false = true at equal
            contradiction
    | inr first =>
        cases second with
        | inl second =>
            change false = true at equal
            contradiction
        | inr second =>
            change (first == second) = true at equal
            exact congrArg Sum.inr (eq_of_beq equal)
  rfl {value} := by
    cases value with
    | inl value =>
        change (value == value) = true
        exact BEq.rfl
    | inr value =>
        change (value == value) = true
        exact BEq.rfl

/-- Generated clauses for a suffix of the source presentation, with explicit
starting clause index. -/
def formulaClausesFrom {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    List (PeriodicClause (OneInThreeVariable Variable)) :=
  (clauses.zipIdx start).flatMap fun (clause, clauseIndex) =>
    clauseClauses clauseIndex clause

theorem formulaClausesFrom_cons {Variable : Type*} (start : Nat)
    (clause : PeriodicClause Variable)
    (rest : List (PeriodicClause Variable)) :
    formulaClausesFrom start (clause :: rest) =
      clauseClauses start clause ++
        formulaClausesFrom (start + 1) rest := by
  rfl

theorem variableOccurrences_append {Variable : Type*}
    (first second : List (PeriodicClause Variable)) :
    PeriodicCNF.variableOccurrences (PeriodicCNF.mk (first ++ second)) =
      PeriodicCNF.variableOccurrences (PeriodicCNF.mk first) ++
        PeriodicCNF.variableOccurrences (PeriodicCNF.mk second) := by
  simp [PeriodicCNF.variableOccurrences, List.flatMap_append]

/-- Keep only original atoms from a list over a sum type. -/
def originalVariables {Original Auxiliary : Type*} :
    List (Sum Original Auxiliary) → List Original
  | [] => []
  | Sum.inl atom :: rest => atom :: originalVariables rest
  | Sum.inr _ :: rest => originalVariables rest

/-- Keep only auxiliary atoms from a list over a sum type. -/
def auxiliaryVariables {Original Auxiliary : Type*} :
    List (Sum Original Auxiliary) → List Auxiliary
  | [] => []
  | Sum.inl _ :: rest => auxiliaryVariables rest
  | Sum.inr atom :: rest => atom :: auxiliaryVariables rest

theorem count_originalVariables {Original Auxiliary : Type*}
    [BEq Original] [LawfulBEq Original]
    [BEq Auxiliary] [LawfulBEq Auxiliary]
    (occurrences : List (Sum Original Auxiliary)) (atom : Original) :
    occurrences.count (Sum.inl atom) =
      (originalVariables occurrences).count atom := by
  induction occurrences with
  | nil => rfl
  | cons head rest induction =>
      cases head with
      | inl current =>
          by_cases same : current = atom
          · subst current
            simp only [originalVariables, List.count_cons_self, induction]
          · rw [originalVariables,
              List.count_cons_of_ne (by simpa using same),
              List.count_cons_of_ne same, induction]
      | inr current =>
          rw [originalVariables,
            List.count_cons_of_ne (by simp), induction]

theorem count_auxiliaryVariables {Original Auxiliary : Type*}
    [BEq Original] [LawfulBEq Original]
    [BEq Auxiliary] [LawfulBEq Auxiliary]
    (occurrences : List (Sum Original Auxiliary)) (atom : Auxiliary) :
    occurrences.count (Sum.inr atom) =
      (auxiliaryVariables occurrences).count atom := by
  induction occurrences with
  | nil => rfl
  | cons head rest induction =>
      cases head with
      | inl current =>
          rw [auxiliaryVariables,
            List.count_cons_of_ne (by simp), induction]
      | inr current =>
          by_cases same : current = atom
          · subst current
            simp only [auxiliaryVariables, List.count_cons_self, induction]
          · rw [auxiliaryVariables,
              List.count_cons_of_ne (by simpa using same),
              List.count_cons_of_ne same, induction]

/-- Auxiliary kinds in one clause gadget, in literal-occurrence order. -/
def clauseAuxiliaryKinds {Variable : Type*} :
    PeriodicClause Variable → List OneInThreeAux
  | [] =>
      [.firstPadding, .firstChoice, .secondChoice,
        .secondPadding, .firstChoice, .firstSlack,
        .thirdPadding, .secondChoice, .secondSlack,
        .firstPadding, .secondPadding, .thirdPadding]
  | [_] =>
      [.firstChoice, .secondChoice,
        .secondPadding, .firstChoice, .firstSlack,
        .thirdPadding, .secondChoice, .secondSlack,
        .secondPadding, .thirdPadding]
  | [_, _] =>
      [.firstChoice, .secondChoice,
        .firstChoice, .firstSlack,
        .thirdPadding, .secondChoice, .secondSlack,
        .thirdPadding]
  | _ :: _ :: _ :: _ =>
      [.firstChoice, .secondChoice,
        .firstChoice, .firstSlack,
        .secondChoice, .secondSlack]

theorem clauseAuxiliaryKinds_count_le_two {Variable : Type*}
    (source : PeriodicClause Variable) (kind : OneInThreeAux) :
    (clauseAuxiliaryKinds source).count kind ≤ 2 := by
  rcases source with _ | ⟨first, rest⟩
  · cases kind <;>
      simp [clauseAuxiliaryKinds, List.count_nil]
  · rcases rest with _ | ⟨second, rest⟩
    · cases kind <;>
        simp [clauseAuxiliaryKinds, List.count_nil]
    · rcases rest with _ | ⟨third, rest⟩
      · cases kind <;>
          simp [clauseAuxiliaryKinds, List.count_nil]
      · cases kind <;>
          simp [clauseAuxiliaryKinds, List.count_nil]

theorem clauseClauses_originalVariables {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (width : source.WidthAtMost 3) :
    originalVariables
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (clauseClauses clauseIndex source))) =
      source.map PeriodicLiteral.atom := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, rest⟩
      · rfl
      · rcases rest with _ | ⟨fourth, rest⟩
        · rfl
        · simp [PeriodicClause.WidthAtMost] at width

theorem clauseClauses_auxiliaryVariables {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (clauseClauses clauseIndex source))) =
      (clauseAuxiliaryKinds source).map fun kind =>
        ((clauseIndex, source), kind) := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, rest⟩
      · rfl
      · rfl

/-- A source atom occurs in a width-three clause gadget exactly as often as
it occurred in that source clause. -/
theorem clauseClauses_count_original {Variable : Type*}
    [DecidableEq Variable] (clauseIndex : Nat)
    (source : PeriodicClause Variable) (width : source.WidthAtMost 3)
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inl atom) =
      (source.map PeriodicLiteral.atom).count atom := by
  rw [count_originalVariables,
    clauseClauses_originalVariables clauseIndex source width]

/-- A particular auxiliary kind belonging to the current clause position
occurs at most twice in that clause gadget. -/
theorem clauseClauses_count_auxiliary_le_two {Variable : Type*}
    [DecidableEq Variable] (clauseIndex : Nat)
    (source selectedSource : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inr ((clauseIndex, selectedSource), kind)) ≤ 2 := by
  rw [count_auxiliaryVariables, clauseClauses_auxiliaryVariables]
  by_cases same : selectedSource = source
  · subst selectedSource
    rw [List.count_map_of_injective
      (clauseAuxiliaryKinds source)
      (fun current => ((clauseIndex, source), current))
      (fun first second equal => congrArg Prod.snd equal) kind]
    exact clauseAuxiliaryKinds_count_le_two source kind
  · have notMem :
        ((clauseIndex, selectedSource), kind) ∉
          (clauseAuxiliaryKinds source).map
            (fun current => ((clauseIndex, source), current)) := by
      intro selectedMem
      simp only [List.mem_map] at selectedMem
      rcases selectedMem with ⟨current, currentMem, equal⟩
      exact same (congrArg (fun atom => atom.1.2) equal).symm
    rw [List.count_eq_zero_of_not_mem notMem]
    omega

/-- Auxiliaries carrying another clause index do not occur in the current
clause gadget. -/
theorem clauseClauses_count_auxiliary_index_ne {Variable : Type*}
    [DecidableEq Variable] (clauseIndex selectedIndex : Nat)
    (source selectedSource : PeriodicClause Variable)
    (kind : OneInThreeAux) (different : selectedIndex ≠ clauseIndex) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) = 0 := by
  rw [count_auxiliaryVariables, clauseClauses_auxiliaryVariables]
  apply List.count_eq_zero_of_not_mem
  intro selectedMem
  simp only [List.mem_map] at selectedMem
  rcases selectedMem with ⟨current, currentMem, equal⟩
  exact different (congrArg (fun atom => atom.1.1) equal).symm

/-- Original-variable counts are preserved across a suffix of the source
presentation. -/
theorem formulaClausesFrom_count_original {Variable : Type*}
    [DecidableEq Variable] (start : Nat)
    (clauses : List (PeriodicClause Variable))
    (width :
      ∀ clause ∈ clauses, clause.WidthAtMost 3)
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk clauses)).count atom := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons, variableOccurrences_append,
        List.count_append]
      rw [clauseClauses_count_original start clause
        (width clause (by simp)) atom]
      have tailWidth :
          ∀ tailClause ∈ rest, tailClause.WidthAtMost 3 := by
        intro tailClause tailMem
        exact width tailClause (by simp [tailMem])
      rw [induction (start + 1) tailWidth]
      simp [PeriodicCNF.variableOccurrences, List.count_append]

/-- An auxiliary whose clause index precedes a source suffix has no
occurrences in the generated suffix. -/
theorem formulaClausesFrom_count_auxiliary_eq_zero_of_lt
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clauses : List (PeriodicClause Variable))
    (selectedIndex : Nat) (selectedSource : PeriodicClause Variable)
    (kind : OneInThreeAux) (before : selectedIndex < start) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) = 0 := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons, variableOccurrences_append,
        List.count_append]
      rw [clauseClauses_count_auxiliary_index_ne start selectedIndex
        clause selectedSource kind (by omega)]
      rw [induction (start + 1) (by omega)]

/-- Across any suffix, a clause-positioned auxiliary occurs at most twice. -/
theorem formulaClausesFrom_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clauses : List (PeriodicClause Variable))
    (selectedIndex : Nat) (selectedSource : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) ≤ 2 := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons, variableOccurrences_append,
        List.count_append]
      by_cases current : selectedIndex = start
      · subst selectedIndex
        have headLe :=
          clauseClauses_count_auxiliary_le_two start clause
            selectedSource kind
        have tailZero :=
          formulaClausesFrom_count_auxiliary_eq_zero_of_lt
            (start + 1) rest start selectedSource kind (by omega)
        omega
      · rw [clauseClauses_count_auxiliary_index_ne start selectedIndex
          clause selectedSource kind current]
        simpa using induction (start + 1)

theorem formula_variableOccurrences_count_original {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) (atom : Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences source).count atom := by
  exact formulaClausesFrom_count_original 0 source.clauses width atom

theorem formula_variableOccurrences_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (sourceClause : PeriodicClause Variable) (kind : OneInThreeAux) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inr ((clauseIndex, sourceClause), kind)) ≤ 2 := by
  exact formulaClausesFrom_count_auxiliary_le_two
    0 source.clauses clauseIndex sourceClause kind

/-- If every source variable occurs at most three times, then every variable
in the exact-one output also occurs at most three times. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) :
    (formula source).OccurrencesAtMost 3 := by
  intro output
  cases output with
  | inl atom =>
      rw [formula_variableOccurrences_count_original source width atom]
      exact occurrences atom
  | inr auxiliary =>
      rcases auxiliary with ⟨⟨clauseIndex, sourceClause⟩, kind⟩
      exact (formula_variableOccurrences_count_auxiliary_le_two
        source clauseIndex sourceClause kind).trans (by omega)

end PeriodicOneInThree
end LeanTrominoes
