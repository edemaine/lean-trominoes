/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierGlobalRankCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldLength
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRepresentativeFieldCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryPermutationRankBlockLookupFiniteAlphabetCompiler

/-! # Compiler for direct-source normalized rank-ordered carrier fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedCarrierRankOrderedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

private noncomputable abbrev
    directSourceCarrierNormalizedSourceKeyRankOrderedFieldsPreparedComputableInPolyTime :=
  UnaryPermutationRankBlockLookup.valuesComputableInPolyTimeOnSymbolLists
    CarrierSourceKeyRepresentativeFieldLookup.fieldCount
    (fun symbols => CarrierRankGlobal.ranks
      (numericRouteDescriptors (directSourceFormula decider symbols)))
    (fun symbols =>
      CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
        (routeDescriptorStreamGridSize
          (numericRouteDescriptors (directSourceFormula decider symbols)))
        (numericRouteDescriptors (directSourceFormula decider symbols)))
    (directSourceCarrierNormalizedSourceKeySelectedFields_length decider)
    (directSourceCarrierGlobalRanksComputableInPolyTime decider)
    (directSourceCarrierNormalizedSourceKeySelectedFieldsComputableInPolyTime
      decider)

/-- Direct source symbols compile to all normalized carrier source-key fields
in global stable carrier-rank order in polynomial time. -/
noncomputable abbrev
    directSourceCarrierNormalizedSourceKeyRankOrderedFieldsComputableInPolyTime :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceCarrierNormalizedSourceKeyRankOrderedFieldsPreparedComputableInPolyTime
      decider)
    (directSourceCarrierNormalizedSourceKeyRankOrderedFields_encoded_eq decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
