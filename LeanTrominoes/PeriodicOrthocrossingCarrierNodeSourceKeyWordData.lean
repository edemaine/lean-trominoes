/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyData

/-! # Binary words for compact carrier-node source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys

/-- The extra `true` is the retained active guard of the second component
after adjacent guarded carrier-key words are merged. -/
def word (keys : SourceKeyPair) : List Bool :=
  CarrierKeyWords.word keys.1 ++
    true :: CarrierKeyWords.word keys.2

def decode (bits : List Bool) : Option (SourceKeyPair × List Bool) := do
  let (first, bits) ← CarrierKeyWords.decode bits
  match bits with
  | true :: bits => do
      let (second, bits) ← CarrierKeyWords.decode bits
      pure ((first, second), bits)
  | _ => none

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys
