/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorData

/-! # Compiler for delayed carrier constructor classification -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

open Computability Turing

/-- Constructor classification and payload selection are a linear-time
finite-state pass. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime
    (.between : Control) transition finish

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing

end
