/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation

/-! # Scaled orthogonality of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The scaled source route of every indexed final retained bend is
orthogonal. -/
theorem FinalBendIndexedOccurrence.scaledRoute_orthogonal
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    OrthogonalPolyline occurrence.scaledRoute := by
  exact finalCoordinatedScaledFallbackSourceRoute_orthogonal
    occurrence.retained
    (PeriodicThreeSATThree.formula_isLocal occurrence.sourceLocal)
    (PeriodicThreeSATThree.formula_widthAtMostThree occurrence.sourceWidth)
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq
      occurrence.source)
    (PeriodicThreeSATThree.formula_clausesNonempty
      occurrence.source occurrence.sourceClausesNonempty)
    occurrence.clauseMember occurrence.literalMember
    occurrence.routeChoice_eq_none

end PeriodicEightOccurrenceSplit
end LeanTrominoes
