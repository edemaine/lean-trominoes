/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceUnaryPreparedLayout
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline

/-!
# Unary fresh-boundary request prefix

Emit one `freshUnit` per prepared fresh marker, followed by `freshEnd` and the
extra forced-root clause marker.  This is exactly the prefix of the normalized
finite-token compact request.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceFreshPrefixEmitter

open AffineEmitterPipeline
open AffineTemplateEmitterMachine
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev Workspace := AffineEmitterPipeline.Workspace
  (Symbol (encoding := encoding))

local instance symbolInhabited : Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedFresh⟩

def phase : Phase (Symbol (encoding := encoding)) where
  selected := PolySpaceUnaryPreparedLayout.isFresh
  recipes := [.fixed .freshUnit]
  ending := [.freshEnd, .clauseMarker]

def emitted (word : List (Symbol (encoding := encoding))) : List Token :=
  freshTokens (PolySpaceUnaryPreparedLayout.fresh word) ++ [.clauseMarker]

def run : List (Workspace (encoding := encoding)) →
    List (Workspace (encoding := encoding)) :=
  (phase (encoding := encoding)).run

theorem positionRangeTokens_freshUnit (first count : Nat) :
    positionRangeTokens [.fixed .freshUnit] first count =
      List.replicate count .freshUnit := by
  induction count generalizing first with
  | zero => rfl
  | succ count induction =>
      rw [positionRangeTokens_succ, induction]
      simp [positionTokens, Recipe.tokens, List.replicate_succ]

theorem phase_emitted (word : List (Symbol (encoding := encoding))) :
    (phase (encoding := encoding)).emitted word = emitted word := by
  unfold phase Phase.emitted emitted PolySpaceUnaryPreparedLayout.fresh
  rw [positionRangeTokens_freshUnit]
  simp [freshTokens, List.append_assoc]

@[simp]
theorem run_embedData (word : List (Symbol (encoding := encoding))) :
    run (encoding := encoding) (embedData word) =
      embedData word ++ (emitted word).map fun token =>
        (Sum.inr token : Workspace (encoding := encoding)) := by
  simpa [run, phase_emitted] using
    (Phase.run_embed_append_tokens (phase (encoding := encoding)) word [])

@[simp]
theorem emitted_preparedSources (symbols : List encoding.Γ) :
    emitted
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      freshTokens (PolySpaceProgramSpec.fresh decider symbols) ++
        [.clauseMarker] := by
  unfold emitted
  rw [PolySpaceUnaryPreparedLayout.fresh_preparedSources]

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (run (encoding := encoding)) :=
  (phase (encoding := encoding)).computableInPolyTime

end PolySpaceFreshPrefixEmitter
end PeriodicCNF
end LeanTrominoes
