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

/-- Promised source presentations at the generic route-emitter boundary.
Local one-dimensional offsets keep every emitted relative offset constant
size, while width three makes the finite clause parser uniform. -/
structure Source where
  formula : PeriodicCNF Nat
  oneDimensional : formula.IsOneDimensional
  isLocal : formula.IsLocal
  widthAtMostThree : formula.WidthAtMost 3

/-- The promised source uses exactly its underlying flat formula word as its
physical encoding.  Decoding rejects formulas outside the promise. -/
noncomputable def finEncoding :
    _root_.Computability.FinEncoding Source := by
  classical
  exact
   { toEncoding :=
    { Γ := PeriodicCNFFlatEncoding.Symbol
      encode source :=
        PeriodicCNFFlatEncoding.finEncoding.encode source.formula
      decode symbols := do
        let formula ← PeriodicCNFFlatEncoding.finEncoding.decode symbols
        if oneDimensional : formula.IsOneDimensional then
          if isLocal : formula.IsLocal then
            if widthAtMostThree : formula.WidthAtMost 3 then
              some ⟨formula, oneDimensional, isLocal, widthAtMostThree⟩
            else none
          else none
        else none
      decode_encode source := by
        rcases source with
          ⟨formula, oneDimensional, isLocal, widthAtMostThree⟩
        simp [oneDimensional, isLocal, widthAtMostThree] }
     ΓFin := inferInstance }

@[simp] theorem finEncoding_encode (source : Source) :
    finEncoding.encode source =
      PeriodicCNFFlatEncoding.finEncoding.encode source.formula := by
  rfl

/-- Exact counted unary route records obtained by occurrence-splitting one
flat source CNF. -/
def tokens (source : Source) :
    List UnaryProgramTokens.Token :=
  routeDescriptorTokens
    (PeriodicThreeSATThree.splitRouteDescriptors source.formula)

/-- Generic machine boundary, independent of the source PSPACE decider. -/
abbrev Compiler :=
  @TM2ComputableInPolyTime
    Source
    (List UnaryProgramTokens.Token)
    PeriodicCNFFlatEncoding.Symbol UnaryProgramTokens.Token
    finEncoding.encode id tokens

end SourceSplitRouteDescriptorTokens
end PeriodicCNF
end LeanTrominoes
