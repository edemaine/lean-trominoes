/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareCompiler
import LeanTrominoes.DelimitedBinaryWordsDropLastTime
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeySentinelCompiler

/-! # Representative rows for carrier order-coordinate candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeRows

open Computability Turing

def rows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordsDropLastMachine.dropLast
    (DelimitedBinaryWordRepresentativeSquare.rows
      (CarrierOrderCandidateKeyStream.wordsWithSentinel descriptors))

def rowsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode rows := by
  let selectedWithSentinel :=
    DelimitedBinaryWordRepresentativeSquare.rowsComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      CarrierOrderCandidateKeyStream.wordsWithSentinel
      CarrierOrderCandidateKeyStream.wordsWithSentinelComputableInPolyTime
  let dropped := TM2CompositionMachine.computableInPolyTime
    selectedWithSentinel
    DelimitedBinaryWordsDropLastMachine.computableInPolyTime
  unfold rows
  exact dropped

end CarrierOrderRepresentativeRows
end LeanTrominoes.PeriodicOrthocrossing

end
