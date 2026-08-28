/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrailingBitPrefixCompiler
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for exact compact carrier atom words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairCompactAtomWords

open Computability Turing

/-- Exact carrier compacting is a composition of three finite-state passes
and two linear reversals. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (A := List DelimitedBinaryWords.Token)
    (B := List DelimitedBinaryWords.Token)
    (C := List DelimitedBinaryWords.Token)
    (encodeA := id) (encodeB := id) (encodeC := id)
    (f := GuardedCarrierSourcePairTrailingConstructor.tokens)
    (g := DelimitedBinaryWordTrailingBitPrefix.tokens)
    GuardedCarrierSourcePairTrailingConstructor.tokensComputableInPolyTime
    DelimitedBinaryWordTrailingBitPrefix.tokensComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun source => DelimitedBinaryWordTrailingBitPrefix.tokens
      (GuardedCarrierSourcePairTrailingConstructor.tokens source))
  exact composed

end GuardedCarrierSourcePairCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing

end
