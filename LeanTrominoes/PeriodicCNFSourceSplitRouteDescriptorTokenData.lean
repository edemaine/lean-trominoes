/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Split route-descriptor tokens from a flat natural-variable CNF -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceSplitRouteDescriptorTokens

open Computability Turing PeriodicOrthocrossing

/-- Exact counted unary route records obtained by occurrence-splitting one
flat source CNF. -/
def tokens (source : PeriodicCNF Nat) :
    List UnaryProgramTokens.Token :=
  routeDescriptorTokens
    (PeriodicThreeSATThree.splitRouteDescriptors source)

/-- Generic machine boundary, independent of the source PSPACE decider. -/
abbrev Compiler :=
  @TM2ComputableInPolyTime
    (PeriodicCNF Nat)
    (List UnaryProgramTokens.Token)
    PeriodicCNFFlatEncoding.Symbol UnaryProgramTokens.Token
    PeriodicCNFFlatEncoding.finEncoding.encode id tokens

end SourceSplitRouteDescriptorTokens
end PeriodicCNF
end LeanTrominoes
