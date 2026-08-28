/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorOpaqueCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingRepresentativeCompactAtomWordStreamClosure

/-! # Physical compiler for direct-source crossover compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverCompactWordTokenCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverCompactWordTokenCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct source symbols compile to the physical canonical-crossover word
stream in polynomial time. -/
opaque
    directSourceCrossoverCompactAtomWordRawTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token id id
      (fun symbols =>
        CanonicalCrossingRepresentativeCompactAtomWordStream.emittedTokens
          (PeriodicCNF.numericRouteDescriptors
            (directSourceFormula decider symbols))) := by
  exact
    CanonicalCrossingRepresentativeCompactAtomWordStream.emittedTokensComputableInPolyTimeAfterOfEncodingEq
    id
    CarrierRankOrderedPairs.InputEncoding
    (fun symbols => PeriodicCNF.numericRouteDescriptors
      (directSourceFormula decider symbols))
    (fun _ => rfl)
    (directSourceNumericRouteDescriptorsOpaqueComputableInPolyTime decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
