import LeanTrominoes.PeriodicOneInThreeNoUnits
import LeanTrominoes.PeriodicOneInThreeOccurrences

/-!
# Occurrence bounds for exact-one unit elimination

Every original occurrence survives exactly once.  In an empty-clause triangle
each of the three fresh auxiliaries occurs twice; in a unit gadget the first
two auxiliaries occur twice; and ordinary clauses introduce no auxiliaries.
Clause indices keep auxiliaries from different protoclauses distinct.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- Generated clauses for a suffix, retaining its absolute starting index. -/
def formulaClausesFrom {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    List (PeriodicClause (OneInThreeNoUnitVariable Variable)) :=
  (clauses.zipIdx start).flatMap fun tagged =>
    clauseClauses tagged.2 tagged.1

theorem formulaClausesFrom_cons {Variable : Type*} (start : Nat)
    (clause : PeriodicClause Variable)
    (rest : List (PeriodicClause Variable)) :
    formulaClausesFrom start (clause :: rest) =
      clauseClauses start clause ++
        formulaClausesFrom (start + 1) rest := by
  rfl

/-- Auxiliary kinds in one generated clause family, in occurrence order. -/
def clauseAuxiliaryKinds {Variable : Type*} :
    PeriodicClause Variable → List OneInThreeNoUnitAux
  | [] => [.first, .second, .second, .third, .first, .third]
  | [_] => [.first, .second, .first, .second]
  | _ :: _ :: _ => []

/-- Each fresh auxiliary occurs at most twice in its local replacement. -/
theorem clauseAuxiliaryKinds_count_le_two {Variable : Type*}
    (source : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    (clauseAuxiliaryKinds source).count kind ≤ 2 := by
  rcases source with _ | ⟨first, rest⟩
  · cases kind <;>
      simp [clauseAuxiliaryKinds, List.count_nil]
  · rcases rest with _ | ⟨second, rest⟩
    · cases kind <;>
        simp [clauseAuxiliaryKinds, List.count_nil]
    · cases kind <;>
        simp [clauseAuxiliaryKinds, List.count_nil]

@[simp]
theorem originalVariables_map_liftLiteral_atoms {Variable : Type*}
    (source : PeriodicClause Variable) :
    PeriodicOneInThree.originalVariables
        ((source.map liftLiteral).map PeriodicLiteral.atom) =
      source.map PeriodicLiteral.atom := by
  induction source with
  | nil => rfl
  | cons literal rest induction =>
      change
        PeriodicOneInThree.originalVariables
            (Sum.inl literal.atom ::
              (rest.map liftLiteral).map PeriodicLiteral.atom) =
          literal.atom :: rest.map PeriodicLiteral.atom
      rw [PeriodicOneInThree.originalVariables]
      exact congrArg (List.cons literal.atom) induction

@[simp]
theorem auxiliaryVariables_map_liftLiteral_atoms {Variable : Type*}
    (source : PeriodicClause Variable) :
    PeriodicOneInThree.auxiliaryVariables
        ((source.map liftLiteral).map PeriodicLiteral.atom) = [] := by
  induction source with
  | nil => rfl
  | cons literal rest induction =>
      change
        PeriodicOneInThree.auxiliaryVariables
            (Sum.inl literal.atom ::
              (rest.map liftLiteral).map PeriodicLiteral.atom) = []
      rw [PeriodicOneInThree.auxiliaryVariables]
      exact induction

/-- Projecting original variables from a local replacement recovers exactly
the source occurrence list. -/
theorem clauseClauses_originalVariables {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.originalVariables
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (clauseClauses clauseIndex source))) =
      source.map PeriodicLiteral.atom := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · simpa [clauseClauses, PeriodicCNF.variableOccurrences]
        using originalVariables_map_liftLiteral_atoms
          (first :: second :: rest)

/-- Projecting auxiliaries from a local replacement gives the explicit
occurrence-order list above. -/
theorem clauseClauses_auxiliaryVariables {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (clauseClauses clauseIndex source))) =
      (clauseAuxiliaryKinds source).map fun kind =>
        ((clauseIndex, source), kind) := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · simpa [clauseClauses, clauseAuxiliaryKinds,
        PeriodicCNF.variableOccurrences]
        using auxiliaryVariables_map_liftLiteral_atoms
          (first :: second :: rest)

/-- One local replacement preserves the count of every original atom. -/
theorem clauseClauses_count_original {Variable : Type*}
    [DecidableEq Variable] (clauseIndex : Nat)
    (source : PeriodicClause Variable) (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inl atom) =
      (source.map PeriodicLiteral.atom).count atom := by
  rw [PeriodicOneInThree.count_originalVariables,
    clauseClauses_originalVariables]

/-- A selected auxiliary at the current clause index occurs at most twice. -/
theorem clauseClauses_count_auxiliary_le_two {Variable : Type*}
    [DecidableEq Variable] (clauseIndex : Nat)
    (source selectedSource : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inr ((clauseIndex, selectedSource), kind)) ≤ 2 := by
  rw [PeriodicOneInThree.count_auxiliaryVariables,
    clauseClauses_auxiliaryVariables]
  by_cases same : selectedSource = source
  · subst selectedSource
    rw [List.count_map_of_injective
      (clauseAuxiliaryKinds source)
      (fun current => ((clauseIndex, source), current))
      (fun left right equal => congrArg Prod.snd equal) kind]
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

/-- Auxiliaries with a different absolute clause index do not occur here. -/
theorem clauseClauses_count_auxiliary_index_ne {Variable : Type*}
    [DecidableEq Variable] (clauseIndex selectedIndex : Nat)
    (source selectedSource : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux)
    (different : selectedIndex ≠ clauseIndex) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (clauseClauses clauseIndex source))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) = 0 := by
  rw [PeriodicOneInThree.count_auxiliaryVariables,
    clauseClauses_auxiliaryVariables]
  apply List.count_eq_zero_of_not_mem
  intro selectedMem
  simp only [List.mem_map] at selectedMem
  rcases selectedMem with ⟨current, currentMem, equal⟩
  exact different (congrArg (fun atom => atom.1.1) equal).symm

/-- Original-variable counts are preserved across every presentation suffix. -/
theorem formulaClausesFrom_count_original {Variable : Type*}
    [DecidableEq Variable] (start : Nat)
    (clauses : List (PeriodicClause Variable)) (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk clauses)).count atom := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        List.count_append]
      rw [clauseClauses_count_original start clause atom]
      rw [induction (start + 1)]
      simp [PeriodicCNF.variableOccurrences, List.count_append]

/-- An auxiliary index before a suffix has no occurrence in that suffix. -/
theorem formulaClausesFrom_count_auxiliary_eq_zero_of_lt
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clauses : List (PeriodicClause Variable))
    (selectedIndex : Nat) (selectedSource : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) (before : selectedIndex < start) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) = 0 := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        List.count_append]
      rw [clauseClauses_count_auxiliary_index_ne start selectedIndex
        clause selectedSource kind (by omega)]
      rw [induction (start + 1) (by omega)]

/-- Every clause-positioned auxiliary occurs at most twice globally. -/
theorem formulaClausesFrom_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clauses : List (PeriodicClause Variable))
    (selectedIndex : Nat) (selectedSource : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (formulaClausesFrom start clauses))).count
        (Sum.inr ((selectedIndex, selectedSource), kind)) ≤ 2 := by
  induction clauses generalizing start with
  | nil =>
      simp [formulaClausesFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
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
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inl atom) =
      (PeriodicCNF.variableOccurrences source).count atom := by
  exact formulaClausesFrom_count_original 0 source.clauses atom

theorem formula_variableOccurrences_count_auxiliary_le_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (sourceClause : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    (PeriodicCNF.variableOccurrences (formula source)).count
        (Sum.inr ((clauseIndex, sourceClause), kind)) ≤ 2 := by
  exact formulaClausesFrom_count_auxiliary_le_two
    0 source.clauses clauseIndex sourceClause kind

/-- Unit elimination preserves the occurrence-three restriction. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    (formula source).OccurrencesAtMost 3 := by
  intro output
  cases output with
  | inl atom =>
      rw [formula_variableOccurrences_count_original source atom]
      exact occurrences atom
  | inr auxiliaryAtom =>
      rcases auxiliaryAtom with
        ⟨⟨clauseIndex, sourceClause⟩, kind⟩
      exact
        (formula_variableOccurrences_count_auxiliary_le_two
          source clauseIndex sourceClause kind).trans (by omega)

end PeriodicOneInThreeNoUnits
end LeanTrominoes
