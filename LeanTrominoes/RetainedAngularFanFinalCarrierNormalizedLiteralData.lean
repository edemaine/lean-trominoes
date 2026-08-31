/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup

/-! # The two literals of a normalized final carrier clause -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- A normalized carrier implication's literal at presentation index zero or
one, expressed directly from its normalized physical link. -/
def finalCarrierNormalizedLiteralAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2) :
    PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) :=
  let link := PeriodicEquality.normalizeLink
    (carrierWrappedVariableNormalization source) taggedLink.1
  if literalIndex = 0 then
    ⟨link.first, (0, 0), taggedLink.2⟩
  else
    ⟨link.second, link.relativeOffset, !taggedLink.2⟩

/-- The normalized carrier implication is exactly its two named literals. -/
theorem normalizedCarrierClauseAt_eq_literal_pair
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool) :
    normalizedCarrierClauseAt source taggedLink =
      [finalCarrierNormalizedLiteralAt source taggedLink 0,
        finalCarrierNormalizedLiteralAt source taggedLink 1] := by
  rcases taggedLink with ⟨link, forward⟩
  cases forward <;>
    simp [normalizedCarrierClauseAt, PeriodicEquality.normalizedClause,
      finalCarrierNormalizedLiteralAt]

/-- Consequently its indexed literal presentation is the corresponding
zero/one pair. -/
theorem normalizedCarrierClauseAt_zipIdx_eq_literal_pair
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool) :
    (normalizedCarrierClauseAt source taggedLink).zipIdx =
      [(finalCarrierNormalizedLiteralAt source taggedLink 0, 0),
        (finalCarrierNormalizedLiteralAt source taggedLink 1, 1)] := by
  rw [normalizedCarrierClauseAt_eq_literal_pair]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
