/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Complete direct final canonical incidence direction stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalIncidenceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete incidence directions in the planar 3DM presentation's stable
order: all grouped variable-module triples first, followed by every
clause-core triple, with RGB minor order in both families. -/
noncomputable def directSourceFinalCanonicalIncidenceDirectionTokens
    (symbols : List encoding.Γ) : List VariableIncidenceDirectionToken :=
  directSourceFinalGroupedVariableIncidenceDirectionTokens decider symbols ++
    directSourceFinalClauseIncidenceDirectionTokens decider symbols

/-- The full canonical incidence direction stream compiles in polynomial
time by appending its independently verified variable and clause families. -/
noncomputable def
    directSourceFinalCanonicalIncidenceDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCanonicalIncidenceDirectionTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCanonicalIncidenceDirectionTokens
    exact TM2ListAppend.computableInPolyTime
      (directSourceFinalGroupedVariableIncidenceDirectionTokensComputableInPolyTime
        decider)
      (directSourceFinalClauseIncidenceDirectionTokensComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
