/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordTokenData

/-! # Semantic binary route-descriptor words for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorBinaryWordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceRouteDescriptorBinaryWordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- One canonical binary word for each numeric incidence-route descriptor of
the direct source formula. -/
def directSourceRouteDescriptorBinaryWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  RouteDescriptorBinaryWords.words
    (numericRouteDescriptors (directSourceFormula decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes

end
