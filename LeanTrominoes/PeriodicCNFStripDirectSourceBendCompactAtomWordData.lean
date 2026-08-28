/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordStreamCompiler

/-! # Direct-source compact retained-bend atom-word data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceBendCompactDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceBendCompactDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical delimiter tokens produced from the direct descriptor-pair
stream. -/
def directSourceBendCompactAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  BendCompactAtomWordStream.emittedStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- Semantic compact occurrence-word stream of every untranslated direct
bend, in route-major and bend-major order. -/
def directSourceBendCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ⟨(numericRouteDescriptors
      (directSourceFormula decider symbols)).flatMap fun descriptor =>
    (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
      RouteBend.compactAtomWords⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
