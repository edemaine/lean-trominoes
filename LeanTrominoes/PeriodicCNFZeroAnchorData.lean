/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph

/-! # Zero-anchored periodic CNF presentations -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Every clause in a finite clause stream has its first literal at the
current horizontal slice. -/
def ClausesZeroAnchored {Variable : Type*}
    (clauses : List (PeriodicClause Variable)) : Prop :=
  ∀ clause ∈ clauses, clauseAnchor clause = (0, 0)

/-- Every presented clause of a periodic CNF is anchored at the origin. -/
def IsZeroAnchored {Variable : Type*}
    (formula : PeriodicCNF Variable) : Prop :=
  ClausesZeroAnchored formula.clauses

theorem clausesZeroAnchored_append
    {Variable : Type*}
    {first second : List (PeriodicClause Variable)}
    (firstAnchored : ClausesZeroAnchored first)
    (secondAnchored : ClausesZeroAnchored second) :
    ClausesZeroAnchored (first ++ second) := by
  intro clause clauseMember
  rcases List.mem_append.mp clauseMember with inFirst | inSecond
  · exact firstAnchored clause inFirst
  · exact secondAnchored clause inSecond

end PeriodicCNF
end LeanTrominoes
