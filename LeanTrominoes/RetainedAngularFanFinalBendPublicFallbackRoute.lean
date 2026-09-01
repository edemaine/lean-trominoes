/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-! # Public fallback-route selection for indexed final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- At an indexed final bend, the public coordinated route is the fallback
occurrence route. -/
theorem FinalBendIndexedOccurrence.publicCoordinatedRoute_eq_fallback
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        occurrence.retained occurrence.clauseIndex occurrence.literalIndex =
      retainedFinalFallbackOccurrenceRoute occurrence.retained
        occurrence.clause occurrence.literal occurrence.clauseIndex
          occurrence.literalIndex := by
  have retainedLocal :=
    PeriodicThreeSATThree.formula_isLocal occurrence.sourceLocal
  have retainedWidth :=
    PeriodicThreeSATThree.formula_widthAtMostThree occurrence.sourceWidth
  have retainedOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq
      occurrence.source
  have retainedClausesNonempty :
      ∀ retainedClause ∈ occurrence.retained.clauses,
        retainedClause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty occurrence.source
      occurrence.sourceClausesNonempty
  exact
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      occurrence.retained retainedLocal retainedWidth retainedOccurrences
      retainedClausesNonempty occurrence.clauseMember occurrence.literalMember
      occurrence.routeChoice_eq_none

end PeriodicEightOccurrenceSplit
end LeanTrominoes
