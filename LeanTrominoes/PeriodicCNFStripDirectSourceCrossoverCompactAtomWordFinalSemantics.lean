/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCanonicalCrossingFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordExpandedInputSemantics

/-! # Final semantics of direct-source crossover compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverCompactFinalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverCompactFinalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The graph-free canonical expansion is exactly the crossover block used by
the final five-family compact occurrence presentation. -/
theorem directSourceCanonicalCrossoverCompactAtomWords_eq_final
    (symbols : List encoding.Γ) :
    directSourceCanonicalCrossoverCompactAtomWords decider symbols =
      directSourceFinalCompactCrossoverAtomWords decider symbols := by
  let formula := directSourceFormula decider symbols
  have occurrencesEq :
      routeDescriptorNeighborOccurrences
          (numericRouteDescriptors formula) =
        neighborOccurrences formula.incidenceGraph :=
    routeDescriptorNeighborOccurrences_numericRouteDescriptors formula
  have expanded :=
    CanonicalCrossingCompactAtomWordSources.expandedInputAtPeriod_eq
      formula.incidenceGraph (numericRouteDescriptors formula)
      occurrencesEq
      (DirectSourceFinalIndexedAtomWords.sourceVariableWord formula)
  unfold directSourceCanonicalCrossoverCompactAtomWords
    directSourceFinalCompactCrossoverAtomWords
  exact expanded

end PeriodicCNFStripReduction
end LeanTrominoes

end
