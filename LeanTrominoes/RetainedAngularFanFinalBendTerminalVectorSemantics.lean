/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteTerminalSemantics
import LeanTrominoes.RetainedAngularFanFinalBendRawTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Final quotient terminal vectors of retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendVectorThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Actual unscaled terminal vector at one globally indexed final bend
incidence. -/
def finalBendActualTerminalVectorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  routeTerminalVector
    (finalCoordinatedSourceRoutes
      (PeriodicThreeSATThree.formula source) clauseIndex literalIndex)

/-- Clause deduplication and anchor normalization preserve the raw first
metadata representative's terminal vector at every final bend index. -/
theorem finalBendActualTerminalVector_eq_rawRepresentative
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    finalBendActualTerminalVectorAt source clauseIndex literalIndex =
      finalBendRawRepresentativeTerminalVectorAt
        source clauseIndex literalIndex := by
  unfold finalBendActualTerminalVectorAt
    finalBendRawRepresentativeTerminalVectorAt
  change routeTerminalVector
      (FormulaShapeRetainedPlanarDirection.incidenceRoutes
        (PeriodicThreeSATThree.formula source)
          clauseIndex literalIndex) = _
  exact incidenceRoutes_routeTerminalVector_eq_rawRepresentativeRoute
    (PeriodicThreeSATThree.formula source) clauseIndex literalIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
