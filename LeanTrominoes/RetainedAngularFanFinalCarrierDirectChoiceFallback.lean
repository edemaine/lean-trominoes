/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final direct-choice rejection for retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierDirectChoiceThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Every literal of an indexed final retained-carrier clause rejects the
direct Figure 7 atlas and therefore takes the fallback router. -/
theorem finalCoordinatedSourceCarrierRouteChoice_eq_none
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    (literalIndex : Nat) :
    let retained := PeriodicThreeSATThree.formula source
    retainedFinalDirectSourceRouteChoice?
        retained clauseIndex literalIndex = none := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedCarrierClauseAt retained taggedLink
  let metadata := carrierClauseMetadataAt
    (Variable := ThreeOccurrenceVariable Variable)
      taggedLink.1 taggedLink.2
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed
  have metadataLookup :
      retainedFinalDirectSourceMetadata? retained clauseIndex =
        some metadata :=
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      retained clauseIndex clause metadata lookups.1 lookups.2
  apply retainedFinalDirectSourceRouteChoice_eq_none_of_fallbackMetadata
    retained clauseIndex literalIndex metadata metadataLookup
  left
  exact ⟨taggedLink.1, if taggedLink.2 then 0 else 1, rfl⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
