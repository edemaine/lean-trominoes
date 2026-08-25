/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldData

/-! # Compiler for selected signed carrier order-coordinate fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderField

open Computability Turing

/-- Either signed order-coordinate magnitude is emitted in unary in
polynomial time. -/
noncomputable def valuesComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values keepPositive) :=
  CarrierOrderRepresentativeLookup.valuesComputableInPolyTime keepPositive

end CarrierRankOrderField
end LeanTrominoes.PeriodicOrthocrossing

end
