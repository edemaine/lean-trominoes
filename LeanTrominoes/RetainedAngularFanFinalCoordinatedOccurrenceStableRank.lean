/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes
import LeanTrominoes.RetainedAngularOccurrenceStableRank

/-! # Stable numeric ranks of final coordinated occurrence slots -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Source-scaled retained formula used by the final coordinated occurrence
slot. -/
def retainedFinalCoordinatedScaledSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF (WrappedPeriodicPlanarSATVariable Variable) :=
  (finalCoordinatedSource formula).scale
    retainedAngularFanSourceClearanceFactor

/-- Source-scaled retained routes used by the final coordinated occurrence
slot. -/
def retainedFinalCoordinatedScaledSourceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.scaleIncidenceRoutes
    retainedAngularFanSourceClearanceFactor
    (finalCoordinatedSourceRoutes formula)

/-- Stable numeric terminal rank underlying one final coordinated Figure 7
slot. -/
def retainedFinalCoordinatedOccurrenceStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) : Nat :=
  retainedOccurrenceStableTerminalRank
    (retainedFinalCoordinatedScaledSource formula).erase
    (retainedFinalCoordinatedScaledSourceRoutes formula)
    literal.atom (literal.atom, clauseIndex, literalIndex)

end PeriodicOrthocrossing
end LeanTrominoes
