/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNF

/-!
# Correctness of periodic CNF clause splitting

The syntactic construction in `PeriodicThreeCNF` is equisatisfiable with its
source formula.  This file separates the propositional chain argument from the
locality and width invariants.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- Extend an original assignment by making a chain bit true exactly when
some literal in the suffix naming that bit is true. -/
noncomputable def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    ThreeCNFVariable Variable → Cell → Bool := by
  classical
  intro atomOrAux cell
  rcases atomOrAux with atom | data
  · exact assignment atom cell
  · rcases data with ⟨source, suffix⟩
    exact decide (∃ literal ∈ suffix,
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
    (translate : Cell) (source suffix : PeriodicClause Variable) :
    (auxiliary source suffix true).Holds (extendAssignment assignment) translate ↔
      ∃ literal ∈ suffix, literal.Holds assignment translate := by
  simp [PeriodicLiteral.Holds, auxiliary, extendAssignment, Cell.add, Cell.sub]

@[simp]
theorem auxiliary_false_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source suffix : PeriodicClause Variable) :
    (auxiliary source suffix false).Holds (extendAssignment assignment) translate ↔
      ¬ ∃ literal ∈ suffix, literal.Holds assignment translate := by
  simp [PeriodicLiteral.Holds, auxiliary, extendAssignment, Cell.add, Cell.sub]

/-- The suffix-based auxiliary assignment satisfies every continuation
clause. -/
theorem continuation_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (remaining : PeriodicClause Variable) :
    ∀ clause ∈ continuation source remaining,
      clause.Holds (extendAssignment assignment) translate := by
  induction remaining with
  | nil =>
      intro clause clause_mem
      simp only [continuation, List.mem_singleton] at clause_mem
      subst clause
      refine ⟨auxiliary source [] false, by simp, ?_⟩
      rw [auxiliary_false_holds_extend]
      simp
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro clause clause_mem
          simp only [continuation, List.mem_singleton] at clause_mem
          subst clause
          by_cases first_holds : first.Holds assignment translate
          · exact ⟨liftLiteral first, by simp,
              (liftLiteral_holds_extend assignment translate first).2 first_holds⟩
          · refine ⟨auxiliary source [first] false, by simp, ?_⟩
            rw [auxiliary_false_holds_extend]
            simpa [first_holds]
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
                · refine ⟨auxiliary source [first, second] false, by simp, ?_⟩
                  rw [auxiliary_false_holds_extend]
                  simpa [first_holds, second_holds]
          | cons third rest =>
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
                  · refine ⟨auxiliary source (second :: third :: rest) true,
                      by simp, ?_⟩
                    rw [auxiliary_true_holds_extend]
                    exact tail_holds
                  · refine ⟨auxiliary source
                        (first :: second :: third :: rest) false, by simp, ?_⟩
                    rw [auxiliary_false_holds_extend]
                    simpa [first_holds] using tail_holds
              · exact ih clause clause_mem

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
                        (first :: second :: third :: fourth :: rest)
                        (third :: fourth :: rest) true,
                      by simp, ?_⟩
                    rw [auxiliary_true_holds_extend]
                    exact ⟨literal, by simpa using literal_mem, literal_holds⟩
                · exact continuation_complete assignment translate
                    (first :: second :: third :: fourth :: rest)
                    (third :: fourth :: rest)
                    clause clause_mem

theorem auxiliary_false_not_holds_of_true {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (source suffix : PeriodicClause Variable)
    (incoming : (auxiliary source suffix true).Holds assignment translate) :
    ¬ (auxiliary source suffix false).Holds assignment translate := by
  intro outgoing
  simp only [PeriodicLiteral.Holds, auxiliary] at incoming outgoing
  rw [incoming] at outgoing
  contradiction

/-- If the incoming chain bit is true, satisfying the continuation forces some
remaining original literal to hold. -/
theorem continuation_sound {Variable : Type*}
    (assignment : ThreeCNFVariable Variable → Cell → Bool)
    (translate : Cell) (source : PeriodicClause Variable)
    (remaining : PeriodicClause Variable)
    (satisfies :
      ∀ clause ∈ continuation source remaining,
        clause.Holds assignment translate)
    (incoming : (auxiliary source remaining true).Holds assignment translate) :
    ∃ literal ∈ remaining, (liftLiteral literal).Holds assignment translate := by
  induction remaining with
  | nil =>
      have clause_holds := satisfies [auxiliary source [] false] (by
        simp [continuation])
      rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
      simp only [List.mem_singleton] at literal_mem
      subst literal
      exact (auxiliary_false_not_holds_of_true assignment translate source []
        incoming literal_holds).elim
  | cons first rest ih =>
      cases rest with
      | nil =>
          have clause_holds := satisfies
            [auxiliary source [first] false, liftLiteral first] (by
              simp [continuation])
          rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
          rcases literal_mem with rfl | rfl
          · exact (auxiliary_false_not_holds_of_true assignment translate
              source [first] incoming literal_holds).elim
          · exact ⟨first, by simp, literal_holds⟩
      | cons second rest =>
          cases rest with
          | nil =>
              have clause_holds := satisfies
                [auxiliary source [first, second] false, liftLiteral first,
                  liftLiteral second] (by simp [continuation])
              rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
              rcases literal_mem with rfl | rfl | rfl
              · exact (auxiliary_false_not_holds_of_true assignment translate
                  source [first, second] incoming literal_holds).elim
              · exact ⟨first, by simp, literal_holds⟩
              · exact ⟨second, by simp, literal_holds⟩
          | cons third rest =>
              have head_holds := satisfies
                [auxiliary source (first :: second :: third :: rest) false,
                  liftLiteral first,
                  auxiliary source (second :: third :: rest) true] (by
                    simp [continuation])
              rcases head_holds with ⟨literal, literal_mem, literal_holds⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
              rcases literal_mem with rfl | rfl | rfl
              · exact (auxiliary_false_not_holds_of_true assignment translate
                  source (first :: second :: third :: rest)
                  incoming literal_holds).elim
              · exact ⟨first, by simp, literal_holds⟩
              · rcases ih
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
                      (first :: second :: third :: fourth :: rest)
                      (third :: fourth :: rest) true] (by
                        simp [clauseClauses])
                rcases head_holds with ⟨literal, literal_mem, literal_holds⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                rcases literal_mem with rfl | rfl | rfl
                · exact ⟨first, by simp, literal_holds⟩
                · exact ⟨second, by simp, literal_holds⟩
                · rcases continuation_sound assignment translate
                      (first :: second :: third :: fourth :: rest)
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
