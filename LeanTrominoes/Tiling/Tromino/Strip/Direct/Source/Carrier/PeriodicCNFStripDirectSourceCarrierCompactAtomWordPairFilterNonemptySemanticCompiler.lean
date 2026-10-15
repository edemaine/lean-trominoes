/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairFilterNonemptyCompiler
import LeanTrominoes.Computation.TM2.TM2PolyTimeFunctionTransport

/-! # Semantic wrapper for nonempty-alphabet carrier-pair filtering -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfInhabitedSemantic
    [Inhabited encoding.Γ] :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.encode
      (directSourceCarrierSelectedCompactAtomWordPairs decider) :=
  TM2PolyTimeFunctionTransport.of_output_eq
    (directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfInhabited
      decider)
    fun symbols =>
      (directSourceCarrierSelectedCompactAtomWordPairs_eq_selected
        decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
