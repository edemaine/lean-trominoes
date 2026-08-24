/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyGuardedWordData

/-! # Semantic terminal source-key guarded-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeStream

def guardedWords (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.terminalSourceKeyGuardedWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

end TerminalSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
