/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCrossoverCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree

/-! # Semantics of direct-source canonical crossover compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverCompactWordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverCompactWordSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct descriptor compiler reconstructs the exact graph-free
canonical crossing expansion. -/
theorem directSourceCrossoverCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceCrossoverCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceCanonicalCrossoverCompactAtomWords decider symbols) := by
  let formula := directSourceFormula decider symbols
  have wellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed formula
  have degree : formula.incidenceGraph.DegreeAtMost 3 :=
    directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  have forward : formula.IsForwardLocal :=
    directSourceFormula_isForwardLocal decider symbols
  have exact :=
    PeriodicCNF.numericRouteDescriptors_canonicalCrossoverExpandedWords
      formula wellFormed degree isLocal forward
  unfold directSourceCrossoverCompactAtomWordTokens
    directSourceCanonicalCrossoverCompactAtomWords
  exact exact

end PeriodicCNFStripReduction
end LeanTrominoes

end
