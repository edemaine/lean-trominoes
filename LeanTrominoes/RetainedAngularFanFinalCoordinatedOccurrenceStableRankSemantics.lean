/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.RetainedAngularOccurrenceBoundedStableRank

/-! # Semantics of final coordinated occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 200000

/-- On a genuine final-source occurrence, the final coordinated Figure 7
slot is exactly its bounded stable numeric terminal rank. -/
theorem
    retainedFinalCoordinatedOccurrenceSlot_eq_boundedStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula))
    (taggedMember :
      (literal, clauseIndex, literalIndex) ∈
        taggedLiterals
          (retainedFinalCoordinatedScaledSource formula).erase) :
    retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex =
      boundedRetainedTerminalSlot
        (retainedFinalCoordinatedOccurrenceStableTerminalRank
          formula literal clauseIndex literalIndex) := by
  unfold retainedFinalCoordinatedOccurrenceSlot
    retainedFinalCoordinatedOccurrenceStableTerminalRank
    retainedFinalCoordinatedScaledSource
    retainedFinalCoordinatedScaledSourceRoutes
  dsimp only
  exact
    boundedAngularOccurrenceIndex_eq_boundedStableTerminalRank
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula))
      certificate literal clauseIndex literalIndex taggedMember

end PeriodicOrthocrossing
end LeanTrominoes
