/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleData

/-! # Expanding final copied-clause queries to occurrence roles -/

noncomputable section

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering

/-- Number of represented literal occurrences in one query.  A variable token
is not a copied-clause descriptor and therefore contributes none. -/
def retainedFinalCopiedClauseQueryArity :
    RetainedFinalCopiedClauseQuery → Nat
  | .precomputed (.clause (.unary _ _)) => 1
  | .precomputed (.clause (.binary _ _ _ _)) => 2
  | .precomputed (.clause (.ternary _ _ _ _ _ _)) => 3
  | .precomputed .variable => 0
  | .unary _ _ => 1
  | .binary _ _ _ _ => 2
  | .ternary _ _ _ _ _ _ => 3

/-- Expand one query to one role per represented clause literal. -/
def retainedFinalCopiedClauseOccurrenceRolesOfQuery :
    RetainedFinalCopiedClauseQuery →
      List RetainedFinalCopiedClauseOccurrenceRole
  | query =>
      (List.finRange 3).take
        (retainedFinalCopiedClauseQueryArity query) |>.map
          fun literalIndex => (query, literalIndex)

/-- Occurrence roles of a whole final copied-clause query stream. -/
def retainedFinalCopiedClauseOccurrenceRoles
    (queries : List RetainedFinalCopiedClauseQuery) :
    List RetainedFinalCopiedClauseOccurrenceRole :=
  queries.flatMap retainedFinalCopiedClauseOccurrenceRolesOfQuery

/-- Query-to-occurrence expansion is a fixed finite block transduction. -/
noncomputable def
    retainedFinalCopiedClauseOccurrenceRolesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedFinalCopiedClauseOccurrenceRoles :=
  FiniteBlockTransducer.computableInPolyTime
    retainedFinalCopiedClauseOccurrenceRolesOfQuery

end LeanTrominoes.PeriodicEightOccurrenceSplit

end
