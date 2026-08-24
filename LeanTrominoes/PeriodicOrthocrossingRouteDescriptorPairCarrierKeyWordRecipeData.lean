/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValues

/-! # Fixed recipes for guarded carrier-key words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open RouteDescriptorPairFieldTags

/-- A fixed carrier-key output recipe.  Only its route index is read from the
unbounded descriptor-pair input; every other component belongs to finite
control. -/
structure Recipe where
  side : Side
  segmentIndex : Nat
  translate : Cell
  supported : Bool
  deriving DecidableEq

/-- Interpret a recipe on one tagged descriptor-pair block. -/
def Recipe.key (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipe : Recipe) : CarrierKeyWords.CarrierKey :=
  (tokenFieldValue tokens recipe.side 2,
    recipe.segmentIndex, recipe.translate)

/-- Emit the guarded word of one aligned activation/recipe pair. -/
def Recipe.word (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipe : Recipe) : List Bool :=
  if active && recipe.supported then
    true :: CarrierKeyWords.word (recipe.key tokens)
  else
    PaddedSupportedCandidateWords.sentinelWord

/-- Emit all recipes of aligned activation blocks, stopping at the shorter
list on malformed unequal-length inputs. -/
def words (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Bool → List (List Recipe) → List (List Bool)
  | active :: actives, block :: blocks =>
      block.map (Recipe.word tokens active) ++ words tokens actives blocks
  | _, _ => []

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
