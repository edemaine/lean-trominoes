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

end PeriodicCNF
end LeanTrominoes
