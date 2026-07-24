import LeanTrominoes.PeriodicThreeCNF
import Mathlib.Tactic.Order

/-!
# Correctness of periodic CNF clause splitting

The syntactic construction in `PeriodicThreeCNF` is equisatisfiable with its
source formula.  This file separates the propositional chain argument from the
locality and width invariants.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- Extend an original assignment by making chain bit `i` true exactly when
some literal in the unconsumed suffix `drop (i + 2)` is true. -/
noncomputable def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    ThreeCNFVariable Variable → Cell → Bool := by
  classical
  intro atomOrAux cell
  rcases atomOrAux with atom | data
  · exact assignment atom cell
  · rcases data with ⟨source, index⟩
    exact decide (∃ literal ∈ source.drop (index + 2),
      literal.Holds assignment (Cell.sub cell (anchor source)))

/-- Forget auxiliary atoms in an assignment. -/
def restrictAssignment {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell => assignment (Sum.inl atom) cell

@[simp]
theorem liftLiteral_holds_restrict {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable) :
    (liftLiteral literal).Holds assignment translate ↔
      literal.Holds (restrictAssignment assignment) translate := by
  rfl

@[simp]
theorem liftLiteral_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable) :
    (liftLiteral literal).Holds (extendAssignment assignment) translate ↔
      literal.Holds assignment translate := by
  rfl

@[simp]
theorem auxiliary_true_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable) (index : Nat) :
    (auxiliary source index true).Holds (extendAssignment assignment) translate ↔
      ∃ literal ∈ source.drop (index + 2),
        literal.Holds assignment translate := by
  simp [PeriodicLiteral.Holds, auxiliary, extendAssignment, Cell.add, Cell.sub]

@[simp]
theorem auxiliary_false_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable) (index : Nat) :
    (auxiliary source index false).Holds (extendAssignment assignment) translate ↔
      ¬ ∃ literal ∈ source.drop (index + 2),
        literal.Holds assignment translate := by
  simp [PeriodicLiteral.Holds, auxiliary, extendAssignment, Cell.add, Cell.sub]

/-- The suffix-based auxiliary assignment satisfies every continuation
clause. -/
theorem continuation_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (index : Nat) (remaining : PeriodicClause Variable)
    (remaining_eq : remaining = source.drop (index + 2)) :
    ∀ clause ∈ continuation source index remaining,
      clause.Holds (extendAssignment assignment) translate := by
  induction remaining generalizing index with
  | nil =>
      intro clause clause_mem
      simp only [continuation, List.mem_singleton] at clause_mem
      subst clause
      refine ⟨auxiliary source index false, by simp, ?_⟩
      rw [auxiliary_false_holds_extend]
      simpa [← remaining_eq]
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro clause clause_mem
          simp only [continuation, List.mem_singleton] at clause_mem
          subst clause
          by_cases first_holds : first.Holds assignment translate
          · exact ⟨liftLiteral first, by simp,
              (liftLiteral_holds_extend assignment translate first).2 first_holds⟩
          · refine ⟨auxiliary source index false, by simp, ?_⟩
            rw [auxiliary_false_holds_extend]
            simpa [← remaining_eq, first_holds]
      | cons second rest =>
          cases rest with
          | nil =>
              intro clause clause_mem
              simp only [continuation, List.mem_singleton] at clause_mem
              subst clause
              by_cases first_holds : first.Holds assignment translate
              · exact ⟨liftLiteral first, by simp,
                  (liftLiteral_holds_extend assignment translate first).2
                    first_holds⟩
              · by_cases second_holds : second.Holds assignment translate
                · exact ⟨liftLiteral second, by simp,
                    (liftLiteral_holds_extend assignment translate second).2
                      second_holds⟩
                · refine ⟨auxiliary source index false, by simp, ?_⟩
                  rw [auxiliary_false_holds_extend]
                  simpa [← remaining_eq, first_holds, second_holds]
          | cons third rest =>
              have next_eq :
                  second :: third :: rest =
                    source.drop ((index + 1) + 2) := by
                calc
                  second :: third :: rest =
                      (first :: second :: third :: rest).drop 1 := rfl
                  _ = (source.drop (index + 2)).drop 1 := by
                    rw [← remaining_eq]
                  _ = source.drop ((index + 1) + 2) := by
                    rw [List.drop_drop]
              intro clause clause_mem
              simp only [continuation, List.mem_cons] at clause_mem
              rcases clause_mem with rfl | clause_mem
              · by_cases first_holds : first.Holds assignment translate
                · exact ⟨liftLiteral first, by simp,
                    (liftLiteral_holds_extend assignment translate first).2
                      first_holds⟩
                · by_cases tail_holds :
                      ∃ literal ∈ second :: third :: rest,
                        literal.Holds assignment translate
                  · refine ⟨auxiliary source (index + 1) true, by simp, ?_⟩
                    rw [auxiliary_true_holds_extend, ← next_eq]
                    exact tail_holds
                  · refine ⟨auxiliary source index false, by simp, ?_⟩
                    rw [auxiliary_false_holds_extend, ← remaining_eq]
                    simpa [first_holds] using tail_holds
              · exact ih (index + 1) next_eq clause clause_mem

/-- Completeness of the split of one clause under the canonical suffix
assignment. -/
theorem clauseClauses_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (source_holds : source.Holds assignment translate) :
    ∀ clause ∈ clauseClauses source,
      clause.Holds (extendAssignment assignment) translate := by
  rcases source with _ | ⟨first, rest⟩
  · simpa [PeriodicClause.Holds] using source_holds
  · cases rest with
    | nil =>
        intro clause clause_mem
        simp only [clauseClauses, List.mem_singleton] at clause_mem
        subst clause
        rcases source_holds with ⟨literal, literal_mem, literal_holds⟩
        simp only [List.mem_singleton] at literal_mem
        subst literal
        exact ⟨liftLiteral first, by simp,
          (liftLiteral_holds_extend assignment translate first).2 literal_holds⟩
    | cons second rest =>
        cases rest with
        | nil =>
            intro clause clause_mem
            simp only [clauseClauses, List.mem_singleton] at clause_mem
            subst clause
            rcases source_holds with ⟨literal, literal_mem, literal_holds⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
            refine ⟨liftLiteral literal, ?_,
              (liftLiteral_holds_extend assignment translate literal).2
                literal_holds⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rcases literal_mem with first_eq | second_eq
            · exact Or.inl (congrArg liftLiteral first_eq)
            · exact Or.inr (congrArg liftLiteral second_eq)
        | cons third rest =>
            cases rest with
            | nil =>
                intro clause clause_mem
                simp only [clauseClauses, List.mem_singleton] at clause_mem
                subst clause
                rcases source_holds with ⟨literal, literal_mem, literal_holds⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                refine ⟨liftLiteral literal, ?_,
                  (liftLiteral_holds_extend assignment translate literal).2
                    literal_holds⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                rcases literal_mem with first_eq | second_eq | third_eq
                · exact Or.inl (congrArg liftLiteral first_eq)
                · exact Or.inr (Or.inl (congrArg liftLiteral second_eq))
                · exact Or.inr (Or.inr (congrArg liftLiteral third_eq))
            | cons fourth rest =>
                intro clause clause_mem
                simp only [clauseClauses, List.mem_cons] at clause_mem
                rcases clause_mem with rfl | clause_mem
                · rcases source_holds with
                    ⟨literal, literal_mem, literal_holds⟩
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                  rcases literal_mem with first_eq | second_eq | literal_mem
                  · exact ⟨liftLiteral first, by simp,
                      (liftLiteral_holds_extend assignment translate first).2
                        (by simpa [first_eq] using literal_holds)⟩
                  · exact ⟨liftLiteral second, by simp,
                      (liftLiteral_holds_extend assignment translate second).2
                        (by simpa [second_eq] using literal_holds)⟩
                  · refine ⟨auxiliary
                        (first :: second :: third :: fourth :: rest) 0 true,
                      by simp, ?_⟩
                    rw [auxiliary_true_holds_extend]
                    exact ⟨literal, by simpa using literal_mem, literal_holds⟩
                · exact continuation_complete assignment translate
                    (first :: second :: third :: fourth :: rest) 0
                    (third :: fourth :: rest) (by simp)
                    clause clause_mem

theorem auxiliary_false_not_holds_of_true {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable) (index : Nat)
    (incoming : (auxiliary source index true).Holds assignment translate) :
    ¬ (auxiliary source index false).Holds assignment translate := by
  intro outgoing
  simp only [PeriodicLiteral.Holds, auxiliary] at incoming outgoing
  rw [incoming] at outgoing
  contradiction

/-- If the incoming chain bit is true, satisfying the continuation forces some
remaining original literal to hold. -/
theorem continuation_sound {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (index : Nat) (remaining : PeriodicClause Variable)
    (satisfies :
      ∀ clause ∈ continuation source index remaining,
        clause.Holds assignment translate)
    (incoming : (auxiliary source index true).Holds assignment translate) :
    ∃ literal ∈ remaining, (liftLiteral literal).Holds assignment translate := by
  induction remaining generalizing index with
  | nil =>
      have clause_holds := satisfies [auxiliary source index false] (by
        simp [continuation])
      rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
      simp only [List.mem_singleton] at literal_mem
      subst literal
      exact (auxiliary_false_not_holds_of_true assignment translate source index
        incoming literal_holds).elim
  | cons first rest ih =>
      cases rest with
      | nil =>
          have clause_holds := satisfies
            [auxiliary source index false, liftLiteral first] (by
              simp [continuation])
          rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
          rcases literal_mem with rfl | rfl
          · exact (auxiliary_false_not_holds_of_true assignment translate
              source index incoming literal_holds).elim
          · exact ⟨first, by simp, literal_holds⟩
      | cons second rest =>
          cases rest with
          | nil =>
              have clause_holds := satisfies
                [auxiliary source index false, liftLiteral first,
                  liftLiteral second] (by simp [continuation])
              rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
              rcases literal_mem with rfl | rfl | rfl
              · exact (auxiliary_false_not_holds_of_true assignment translate
                  source index incoming literal_holds).elim
              · exact ⟨first, by simp, literal_holds⟩
              · exact ⟨second, by simp, literal_holds⟩
          | cons third rest =>
              have head_holds := satisfies
                [auxiliary source index false, liftLiteral first,
                  auxiliary source (index + 1) true] (by
                    simp [continuation])
              rcases head_holds with ⟨literal, literal_mem, literal_holds⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
              rcases literal_mem with rfl | rfl | rfl
              · exact (auxiliary_false_not_holds_of_true assignment translate
                  source index incoming literal_holds).elim
              · exact ⟨first, by simp, literal_holds⟩
              · rcases ih (index + 1)
                    (fun clause clause_mem =>
                      satisfies clause (by
                        simp only [continuation, List.mem_cons]
                        exact Or.inr clause_mem))
                    literal_holds with
                  ⟨remainingLiteral, remaining_mem, remaining_holds⟩
                exact ⟨remainingLiteral, by simp [remaining_mem], remaining_holds⟩

/-- Soundness of the clause split under an arbitrary enlarged assignment. -/
theorem clauseClauses_sound {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (satisfies :
      ∀ clause ∈ clauseClauses source, clause.Holds assignment translate) :
    ∃ literal ∈ source, (liftLiteral literal).Holds assignment translate := by
  rcases source with _ | ⟨first, rest⟩
  · have empty_holds := satisfies [] (by simp [clauseClauses])
    simpa [PeriodicClause.Holds] using empty_holds
  · cases rest with
    | nil =>
        simpa [clauseClauses, PeriodicClause.Holds] using
          satisfies [liftLiteral first] (by simp [clauseClauses])
    | cons second rest =>
        cases rest with
        | nil =>
            simpa [clauseClauses, PeriodicClause.Holds] using
              satisfies [liftLiteral first, liftLiteral second] (by
                simp [clauseClauses])
        | cons third rest =>
            cases rest with
            | nil =>
                simpa [clauseClauses, PeriodicClause.Holds] using
                  satisfies [liftLiteral first, liftLiteral second,
                    liftLiteral third] (by simp [clauseClauses])
            | cons fourth rest =>
                have head_holds := satisfies
                  [liftLiteral first, liftLiteral second,
                    auxiliary
                      (first :: second :: third :: fourth :: rest) 0 true] (by
                        simp [clauseClauses])
                rcases head_holds with ⟨literal, literal_mem, literal_holds⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                rcases literal_mem with rfl | rfl | rfl
                · exact ⟨first, by simp, literal_holds⟩
                · exact ⟨second, by simp, literal_holds⟩
                · rcases continuation_sound assignment translate
                      (first :: second :: third :: fourth :: rest) 0
                      (third :: fourth :: rest)
                      (fun clause clause_mem =>
                        satisfies clause (by
                          simp only [clauseClauses, List.mem_cons]
                          exact Or.inr clause_mem))
                      literal_holds with
                    ⟨remainingLiteral, remaining_mem, remaining_holds⟩
                  exact ⟨remainingLiteral, by simp [remaining_mem],
                    remaining_holds⟩

/-- Restricting a satisfying width-three assignment satisfies the original
periodic CNF formula. -/
theorem satisfies_of_threeCNF_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (satisfies : (formula source).Satisfies assignment) :
    source.Satisfies (restrictAssignment assignment) := by
  intro translate sourceClause source_mem
  rcases clauseClauses_sound assignment translate sourceClause
      (fun clause clause_mem =>
        satisfies translate clause (by
          simp only [formula, List.mem_flatMap]
          exact ⟨sourceClause, source_mem, clause_mem⟩)) with
    ⟨literal, literal_mem, literal_holds⟩
  exact ⟨literal, literal_mem,
    (liftLiteral_holds_restrict assignment translate literal).1 literal_holds⟩

/-- The canonical suffix assignment satisfies the split formula whenever the
original assignment satisfies its source. -/
theorem threeCNF_satisfies_of_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (satisfies : source.Satisfies assignment) :
    (formula source).Satisfies (extendAssignment assignment) := by
  intro translate clause clause_mem
  simp only [formula, List.mem_flatMap] at clause_mem
  rcases clause_mem with ⟨sourceClause, source_mem, clause_mem⟩
  exact clauseClauses_complete assignment translate sourceClause
    (satisfies translate sourceClause source_mem) clause clause_mem

/-- The standard periodic clause split preserves satisfiability exactly. -/
theorem satisfiable_iff {Variable : Type*} (source : PeriodicCNF Variable) :
    source.Satisfiable ↔ (formula source).Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment,
      threeCNF_satisfies_of_satisfies source assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨restrictAssignment assignment,
      satisfies_of_threeCNF_satisfies source assignment satisfies⟩

end PeriodicThreeCNF
end LeanTrominoes
