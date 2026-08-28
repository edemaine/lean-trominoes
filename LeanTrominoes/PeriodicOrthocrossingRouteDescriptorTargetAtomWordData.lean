/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Target-vertex atom words from numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorTargetAtomWords

open RouteDescriptorScanTokens

/-- Final indexed source-atom word named by one route descriptor.  The first
three bits are the routed-atom, source-atom, and on-formula-member tags. -/
def word (descriptor : RouteDescriptor) : List Bool :=
  [true, false, false] ++
    CarrierKeyWords.natField descriptor.targetVertexIndex

/-- Semantic target word list in descriptor presentation order. -/
def words (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨descriptors.map word⟩

/-- Current field of the fixed eleven-field descriptor record. -/
abbrev Control := Fin 11

def nextControl (control : Control) : Control :=
  ⟨(control.val + 1) % 11, Nat.mod_lt _ (by omega)⟩

/-- Retain only field four (`targetVertexIndex`) and wrap it as one final
source-atom word. -/
def transition : Control → RouteDescriptorScanTokens.Token →
    Control × List DelimitedBinaryWords.Token
  | _, .recordStart =>
      (0, [.wordStart, .bit true, .bit false, .bit false])
  | control, .unit =>
      (control, if control.val = 4 then [.bit false] else [])
  | control, .fieldEnd =>
      (nextControl control,
        if control.val = 4 then [.bit true, .wordEnd] else [])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

/-- Physical target-word projection from normalized descriptor tokens. -/
def tokens (source : List RouteDescriptorScanTokens.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output 0 transition finish source

end RouteDescriptorTargetAtomWords
end PeriodicOrthocrossing
end LeanTrominoes
