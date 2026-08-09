import LeanTrominoes.PeriodicOneInThreePolarityNormalization
import LeanTrominoes.PeriodicOneInThreeOccurrences

/-!
# Occurrence bound for polarity normalization

Each source occurrence contributes exactly one occurrence of its embedded
original variable.  A changed occurrence additionally introduces one fresh
variable, used once in the normalized main clause and once in its binary
complement clause.  Clause and literal indices make those fresh variables
distinct across the finite periodic presentation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

/-- Generated clauses for a suffix of the source presentation, retaining
its absolute starting clause index. -/
def formulaClausesFrom {Variable : Type*} (clauseStart : Nat)
    (clauses : List (PeriodicClause Variable)) :
    List (PeriodicClause (PolarityNormalizedVariable Variable)) :=
  (clauses.zipIdx clauseStart).flatMap fun tagged =>
    clauseClauses tagged.2 tagged.1

theorem formulaClausesFrom_cons {Variable : Type*} (clauseStart : Nat)
    (clause : PeriodicClause Variable)
    (rest : List (PeriodicClause Variable)) :
    formulaClausesFrom clauseStart (clause :: rest) =
      clauseClauses clauseStart clause ++
        formulaClausesFrom (clauseStart + 1) rest := by
  rfl

/-- One local replacement preserves the occurrence count of every original
atom. -/
theorem clauseClausesFrom_count_original {Variable : Type*}
    [DecidableEq Variable] (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (clauseClausesFrom clauseIndex literalStart source))).count
        (Sum.inl atom) =
      (source.map PeriodicLiteral.atom).count atom := by
  induction source generalizing literalStart with
  | nil =>
      simp [clauseClausesFrom, normalizeClauseFrom,
        complementClausesFrom, PeriodicCNF.variableOccurrences]
  | cons literal rest induction =>
      have tailCount := induction (literalStart + 1)
      simp only [clauseClausesFrom,
        PeriodicCNF.variableOccurrences, List.flatMap_cons] at tailCount
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp only [clauseClausesFrom, normalizeClauseFrom_cons,
          complementClausesFrom_cons, compatible, if_pos,
          PeriodicCNF.variableOccurrences, List.flatMap_cons,
          List.map_cons,
          normalizeLiteral]
        change
          (Sum.inl literal.atom ::
            (normalizeClauseFrom clauseIndex (literalStart + 1) rest).map
                PeriodicLiteral.atom ++
              (complementClausesFrom clauseIndex
                (literalStart + 1) rest).flatMap
                (fun clause => clause.map PeriodicLiteral.atom)).count
              (Sum.inl atom) =
            (literal.atom :: rest.map PeriodicLiteral.atom).count atom
        rw [List.count_cons, List.count_append, List.count_cons]
        rw [List.count_append] at tailCount
        have sameIte :
            (if ((Sum.inl literal.atom :
                  PolarityNormalizedVariable Variable) ==
                (Sum.inl atom : PolarityNormalizedVariable Variable)) = true
              then 1 else 0) =
              (if (literal.atom == atom) = true then 1 else 0) := by
          by_cases same : literal.atom = atom <;> simp [same]
        rw [sameIte]
        omega
      · simp only [clauseClausesFrom, normalizeClauseFrom_cons,
          complementClausesFrom_cons, compatible,
          if_false,
          PeriodicCNF.variableOccurrences, List.flatMap_cons,
          List.map_cons,
          normalizeLiteral, complementClause, originalFalseLiteral,
          complementFalseLiteral]
        change
          (Sum.inr ((clauseIndex, literalStart), literal) ::
            (normalizeClauseFrom clauseIndex (literalStart + 1) rest).map
                PeriodicLiteral.atom ++
              Sum.inl literal.atom ::
                Sum.inr ((clauseIndex, literalStart), literal) ::
                  (complementClausesFrom clauseIndex
                    (literalStart + 1) rest).flatMap
                    (fun clause => clause.map PeriodicLiteral.atom)).count
              (Sum.inl atom) =
            (literal.atom :: rest.map PeriodicLiteral.atom).count atom
        rw [List.count_cons, List.count_append, List.count_cons,
          List.count_cons, List.count_cons]
        rw [List.count_append] at tailCount
        have freshFalse :
            (Sum.inr ((clauseIndex, literalStart), literal) ==
              Sum.inl atom) = false := by
          cases equal :
              (Sum.inr ((clauseIndex, literalStart), literal) ==
                Sum.inl atom) with
          | false => rfl
          | true =>
              have impossible :
                  (Sum.inr ((clauseIndex, literalStart), literal) :
                      PolarityNormalizedVariable Variable) =
                    Sum.inl atom := eq_of_beq equal
              contradiction
        have sameIte :
            (if ((Sum.inl literal.atom :
                  PolarityNormalizedVariable Variable) ==
                (Sum.inl atom : PolarityNormalizedVariable Variable)) = true
              then 1 else 0) =
              (if (literal.atom == atom) = true then 1 else 0) := by
          by_cases same : literal.atom = atom <;> simp [same]
        rw [freshFalse, sameIte]
        simp only [Bool.false_eq_true, if_false]
        omega

/-- The fresh variables introduced by incompatible occurrences in one
literal suffix. -/
def freshVariablesFrom {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    List ((Nat × Nat) × PeriodicLiteral Variable) :=
  (source.zipIdx literalStart).filterMap fun tagged =>
    if tagged.1.value = normalizedPolarity tagged.2 then
      none
    else
      some ((clauseIndex, tagged.2), tagged.1)

@[simp]
theorem freshVariablesFrom_cons {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (literal : PeriodicLiteral Variable)
    (rest : PeriodicClause Variable) :
    freshVariablesFrom clauseIndex literalStart (literal :: rest) =
      if literal.value = normalizedPolarity literalStart then
        freshVariablesFrom clauseIndex (literalStart + 1) rest
      else
        ((clauseIndex, literalStart), literal) ::
          freshVariablesFrom clauseIndex (literalStart + 1) rest := by
  unfold freshVariablesFrom
  by_cases compatible : literal.value = normalizedPolarity literalStart <;>
    simp [compatible]

theorem auxiliaryVariables_append {Original Auxiliary : Type*}
    (first second : List (Sum Original Auxiliary)) :
    PeriodicOneInThree.auxiliaryVariables (first ++ second) =
      PeriodicOneInThree.auxiliaryVariables first ++
        PeriodicOneInThree.auxiliaryVariables second := by
  induction first with
  | nil => rfl
  | cons head rest induction =>
      cases head <;>
        simp [PeriodicOneInThree.auxiliaryVariables, induction]

/-- Projecting fresh variables from a normalized main clause gives exactly
the incompatible-occurrence list. -/
theorem normalizeClauseFrom_auxiliaryVariables {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.auxiliaryVariables
        ((normalizeClauseFrom clauseIndex literalStart source).map
          PeriodicLiteral.atom) =
      freshVariablesFrom clauseIndex literalStart source := by
  induction source generalizing literalStart with
  | nil =>
      simp [normalizeClauseFrom, freshVariablesFrom,
        PeriodicOneInThree.auxiliaryVariables]
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [normalizeClauseFrom_cons, freshVariablesFrom_cons,
          compatible,
          normalizeLiteral, liftLiteral,
          PeriodicOneInThree.auxiliaryVariables,
          induction (literalStart + 1)]
      · simp [normalizeClauseFrom_cons, freshVariablesFrom_cons,
          compatible,
          normalizeLiteral, complementLiteral,
          PeriodicOneInThree.auxiliaryVariables,
          induction (literalStart + 1)]

/-- Projecting fresh variables from the binary complement clauses gives the
same incompatible-occurrence list. -/
theorem complementClausesFrom_auxiliaryVariables {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.auxiliaryVariables
        ((complementClausesFrom clauseIndex literalStart source).flatMap
          (fun clause => clause.map PeriodicLiteral.atom)) =
      freshVariablesFrom clauseIndex literalStart source := by
  induction source generalizing literalStart with
  | nil =>
      simp [complementClausesFrom, freshVariablesFrom,
        PeriodicOneInThree.auxiliaryVariables]
  | cons literal rest induction =>
      have tail := induction (literalStart + 1)
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [complementClausesFrom_cons, freshVariablesFrom_cons,
          compatible]
        exact tail
      · simp [complementClausesFrom_cons, freshVariablesFrom_cons,
          compatible,
          complementClause, originalFalseLiteral,
          complementFalseLiteral,
          PeriodicOneInThree.auxiliaryVariables]
        exact tail

/-- Projecting fresh variables from one local replacement gives two copies
of the incompatible-occurrence list. -/
theorem clauseClausesFrom_auxiliaryVariables {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (clauseClausesFrom clauseIndex literalStart source))) =
      freshVariablesFrom clauseIndex literalStart source ++
        freshVariablesFrom clauseIndex literalStart source := by
  simp only [clauseClausesFrom, PeriodicCNF.variableOccurrences,
    List.flatMap_cons,
    auxiliaryVariables_append,
    normalizeClauseFrom_auxiliaryVariables,
    complementClausesFrom_auxiliaryVariables]

/-- Fresh variables inside one literal suffix are pairwise distinct because
their absolute literal indices are distinct. -/
theorem freshVariablesFrom_nodup {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    (freshVariablesFrom clauseIndex literalStart source).Nodup := by
  unfold freshVariablesFrom
  apply List.Nodup.filterMap
  · intro first second output firstOutput secondOutput
    rcases first with ⟨firstLiteral, firstIndex⟩
    rcases second with ⟨secondLiteral, secondIndex⟩
    by_cases firstCompatible :
        firstLiteral.value = normalizedPolarity firstIndex
    · simp [firstCompatible] at firstOutput
    · by_cases secondCompatible :
          secondLiteral.value = normalizedPolarity secondIndex
      · simp [secondCompatible] at secondOutput
      · simp [firstCompatible] at firstOutput
        simp [secondCompatible] at secondOutput
        subst output
        have outputParts :
            (True ∧ firstIndex = secondIndex) ∧
              firstLiteral = secondLiteral := by
          simpa only [Prod.mk.injEq] using secondOutput.symm
        rcases outputParts with ⟨⟨_, sameIndex⟩, sameLiteral⟩
        apply Prod.ext
        · exact sameLiteral
        · exact sameIndex
  · apply List.Nodup.of_map Prod.snd
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'

/-- A selected occurrence-local fresh variable appears at most twice in its
clause replacement. -/
theorem clauseClausesFrom_count_auxiliary_le_two {Variable : Type*}
    [DecidableEq Variable] (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (selected : (Nat × Nat) × PeriodicLiteral Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (clauseClausesFrom clauseIndex literalStart source))).count
        (Sum.inr selected) ≤ 2 := by
  rw [PeriodicOneInThree.count_auxiliaryVariables,
    clauseClausesFrom_auxiliaryVariables, List.count_append]
  have countLeOne :=
    (List.nodup_iff_count_le_one.mp
      (freshVariablesFrom_nodup clauseIndex literalStart source)) selected
  omega

/-- A fresh variable carrying another clause index does not occur in the
current local replacement. -/
theorem clauseClausesFrom_count_auxiliary_index_ne {Variable : Type*}
    [DecidableEq Variable] (clauseIndex selectedClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (selectedLiteralIndex : Nat)
    (selectedLiteral : PeriodicLiteral Variable)
    (different : selectedClauseIndex ≠ clauseIndex) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (clauseClausesFrom clauseIndex literalStart source))).count
        (Sum.inr
          ((selectedClauseIndex, selectedLiteralIndex), selectedLiteral)) = 0 := by
  rw [PeriodicOneInThree.count_auxiliaryVariables,
    clauseClausesFrom_auxiliaryVariables, List.count_append]
  have notMember :
      ((selectedClauseIndex, selectedLiteralIndex), selectedLiteral) ∉
        freshVariablesFrom clauseIndex literalStart source := by
    intro selectedMember
    simp only [freshVariablesFrom, List.mem_filterMap] at selectedMember
    rcases selectedMember with
      ⟨⟨literal, literalIndex⟩, literalMember, outputEq⟩
    split at outputEq
    · contradiction
    · simp only [Option.some.injEq] at outputEq
      exact different
        (congrArg (fun fresh => fresh.1.1) outputEq.symm)
  rw [List.count_eq_zero_of_not_mem notMember]

/-- Original-variable counts are preserved across every source-clause
suffix. -/
theorem formulaClausesFrom_count_original {Variable : Type*}
    [DecidableEq Variable] (clauseStart : Nat)
    (clauses : List (PeriodicClause Variable)) (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom clauseStart clauses))).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences (PeriodicCNF.mk clauses)).count atom := by
  induction clauses generalizing clauseStart with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        List.count_append]
      rw [← clauseClausesFrom_zero clauseStart clause,
        clauseClausesFrom_count_original clauseStart 0 clause atom,
        induction (clauseStart + 1)]
      simp [PeriodicCNF.variableOccurrences, List.count_append]

/-- An auxiliary clause index before a suffix cannot occur in that suffix. -/
theorem formulaClausesFrom_count_auxiliary_eq_zero_of_lt
    {Variable : Type*} [DecidableEq Variable]
    (clauseStart : Nat) (clauses : List (PeriodicClause Variable))
    (selectedClauseIndex selectedLiteralIndex : Nat)
    (selectedLiteral : PeriodicLiteral Variable)
    (before : selectedClauseIndex < clauseStart) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom clauseStart clauses))).count
        (Sum.inr
          ((selectedClauseIndex, selectedLiteralIndex), selectedLiteral)) = 0 := by
  induction clauses generalizing clauseStart with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        List.count_append]
      rw [← clauseClausesFrom_zero clauseStart clause,
        clauseClausesFrom_count_auxiliary_index_ne
          clauseStart selectedClauseIndex 0 clause
          selectedLiteralIndex selectedLiteral (by omega),
        induction (clauseStart + 1) (by omega)]

/-- Every occurrence-local fresh variable appears at most twice throughout
the complete clause suffix. -/
theorem formulaClausesFrom_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (clauseStart : Nat) (clauses : List (PeriodicClause Variable))
    (selectedClauseIndex selectedLiteralIndex : Nat)
    (selectedLiteral : PeriodicLiteral Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom clauseStart clauses))).count
        (Sum.inr
          ((selectedClauseIndex, selectedLiteralIndex), selectedLiteral)) ≤ 2 := by
  induction clauses generalizing clauseStart with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        List.count_append]
      rw [← clauseClausesFrom_zero clauseStart clause]
      by_cases current : selectedClauseIndex = clauseStart
      · subst selectedClauseIndex
        have headLe := clauseClausesFrom_count_auxiliary_le_two
          clauseStart 0 clause
          ((clauseStart, selectedLiteralIndex), selectedLiteral)
        have tailZero := formulaClausesFrom_count_auxiliary_eq_zero_of_lt
          (clauseStart + 1) rest clauseStart selectedLiteralIndex
          selectedLiteral (by omega)
        omega
      · rw [clauseClausesFrom_count_auxiliary_index_ne
          clauseStart selectedClauseIndex 0 clause
          selectedLiteralIndex selectedLiteral current]
        simpa using induction (clauseStart + 1)

theorem formula_variableOccurrences_count_original {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences source).count atom := by
  exact formulaClausesFrom_count_original 0 source.clauses atom

theorem formula_variableOccurrences_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inr ((clauseIndex, literalIndex), literal)) ≤ 2 := by
  exact formulaClausesFrom_count_auxiliary_le_two
    0 source.clauses clauseIndex literalIndex literal

/-- Polarity normalization preserves the degree-three occurrence bound. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    (formula source).OccurrencesAtMost 3 := by
  intro output
  cases output with
  | inl atom =>
      rw [formula_variableOccurrences_count_original source atom]
      exact occurrences atom
  | inr fresh =>
      rcases fresh with ⟨⟨clauseIndex, literalIndex⟩, literal⟩
      exact (formula_variableOccurrences_count_auxiliary_le_two
        source clauseIndex literalIndex literal).trans (by omega)

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
