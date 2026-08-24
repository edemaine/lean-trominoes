/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterOutputSemantics

/-! # Physical output of terminal source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeEmitter

/-- The compiled physical stream is exactly the delimiter encoding of the
semantic terminal source-key guarded words. -/
@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.terminalSourceKeyGuardedWords tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens) (preparedInput_activationBits tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end TerminalSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
