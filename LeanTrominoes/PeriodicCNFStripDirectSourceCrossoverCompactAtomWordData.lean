/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordExpandedData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingRepresentativeCompactAtomWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalizedCrossingHalo

/-! # Direct-source canonical crossover compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverCompactWordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverCompactWordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical canonical-crossover expansion of the direct source's exact
numeric route-descriptor stream. -/
def directSourceCrossoverCompactAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  CanonicalCrossingRepresentativeCompactAtomWordStream.emittedTokens
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- Delimited target carrying exactly the final crossover-family compact
atom-word block. -/
def directSourceCanonicalCrossoverCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  let formula := directSourceFormula decider symbols
  ⟨CanonicalCrossingCompactAtomWordSources.expandedWordsAtPeriod
    (drawingGridSize formula.incidenceGraph)
    (numericRouteDescriptors formula)⟩

/-- Semantic Figure 8(b) target used by the final five-family compact
occurrence column. -/
def directSourceFinalCompactCrossoverAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  let formula := directSourceFormula decider symbols
  let word := RetainedCompactAtomWords.word
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord formula)
  ⟨(canonicalizedCrossingHalo formula.incidenceGraph).flatMap fun crossing =>
    PlanarThreeSAT.crossoverFormula.flatMap fun clause =>
      clause.literals.map fun literal =>
        word ⟨normalizedCrossoverAtom crossing literal.1⟩⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
