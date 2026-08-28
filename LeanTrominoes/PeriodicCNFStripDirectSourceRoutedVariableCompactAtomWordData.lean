/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordStreamCompiler

/-! # Direct-source routed-variable compact atom-word data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedVariableCompactDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedVariableCompactDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical delimiter tokens produced from the direct descriptor-pair
stream. -/
def directSourceRoutedVariableCompactAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  RoutedVariableCompactAtomWordStream.emittedStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- Semantic route-shape-independent scan over the direct numeric descriptor
square. -/
def directSourceRoutedVariableCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  ⟨RouteDescriptorPairAffine.routedVariableCompactAtomWordPairScan
    descriptors⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
