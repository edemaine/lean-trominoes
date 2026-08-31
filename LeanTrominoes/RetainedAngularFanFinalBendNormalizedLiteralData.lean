/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendClauseDescriptorLookup

/-! # The two literals of a normalized final bend clause -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A normalized bend implication's literal at presentation index zero or
one, expressed directly from its wrapped normalized physical link. -/
def finalBendNormalizedLiteralAt
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (literalIndex : Fin 2) :
    PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) :=
  let link := wrappedNormalizedRouteBendLink formula taggedBend.1
  if literalIndex = 0 then
    ⟨link.first, (0, 0), taggedBend.2⟩
  else
    ⟨link.second, link.relativeOffset, !taggedBend.2⟩

/-- The normalized bend implication is exactly its two named literals. -/
theorem normalizedBendClauseAt_eq_literal_pair
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool) :
    normalizedBendClauseAt formula taggedBend =
      [finalBendNormalizedLiteralAt formula taggedBend 0,
        finalBendNormalizedLiteralAt formula taggedBend 1] := by
  rcases taggedBend with ⟨routeBend, forward⟩
  cases forward <;>
    simp [normalizedBendClauseAt, PeriodicEquality.normalizedClause,
      finalBendNormalizedLiteralAt, wrappedNormalizedRouteBendLink]

/-- Consequently its indexed literal presentation is the corresponding
zero/one pair. -/
theorem normalizedBendClauseAt_zipIdx_eq_literal_pair
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool) :
    (normalizedBendClauseAt formula taggedBend).zipIdx =
      [(finalBendNormalizedLiteralAt formula taggedBend 0, 0),
        (finalBendNormalizedLiteralAt formula taggedBend 1, 1)] := by
  rw [normalizedBendClauseAt_eq_literal_pair]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
