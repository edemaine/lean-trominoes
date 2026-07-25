import LeanTrominoes.PeriodicCNF
import Mathlib.Data.List.Count

/-!
# Variable-occurrence bounds for periodic CNF

Occurrence bounds refer to the finite periodic presentation: every literal in
every protoclauses contributes one occurrence of its protovariable.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- The protovariable named by every literal occurrence in the finite
presentation, preserving clause and literal order. -/
def variableOccurrences {Variable : Type*}
    (formula : PeriodicCNF Variable) : List Variable :=
  formula.clauses.flatMap fun clause =>
    clause.map PeriodicLiteral.atom

/-- Every protovariable has at most `bound` literal occurrences in the finite
periodic presentation. -/
def OccurrencesAtMost {Variable : Type*} [BEq Variable] [LawfulBEq Variable]
    (bound : Nat) (formula : PeriodicCNF Variable) : Prop :=
  ∀ atom, (variableOccurrences formula).count atom ≤ bound

/-- Occurrence bounds do not depend on the choice of lawful Boolean equality
implementation. -/
theorem occurrencesAtMost_congr_beq {Variable : Type*}
    (first second : BEq Variable)
    (firstLawful : @LawfulBEq Variable first)
    (secondLawful : @LawfulBEq Variable second)
    (bound : Nat) (formula : PeriodicCNF Variable)
    (occurrences :
      @OccurrencesAtMost Variable first firstLawful bound formula) :
    @OccurrencesAtMost Variable second secondLawful bound formula := by
  intro atom
  have beq_eq (left right : Variable) :
      @BEq.beq Variable first left right =
        @BEq.beq Variable second left right := by
    rw [Bool.eq_iff_iff]
    constructor
    · intro equal
      have : left = right :=
        @eq_of_beq Variable first firstLawful left right equal
      subst right
      exact secondLawful.rfl
    · intro equal
      have : left = right :=
        @eq_of_beq Variable second secondLawful left right equal
      subst right
      exact firstLawful.rfl
  have count_eq (values : List Variable) :
      @List.count Variable first atom values =
        @List.count Variable second atom values := by
    induction values with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.count_cons]
        rw [beq_eq head atom, induction]
  rw [← count_eq]
  exact occurrences atom

end PeriodicCNF
end LeanTrominoes
