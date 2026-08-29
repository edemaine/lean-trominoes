/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyCompiler
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for final copied-clause occurrence roles -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceRoleStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The final five-family query compiler followed by finite arity expansion
emits one query-and-position role per final copied occurrence. -/
noncomputable def
    directSourceFinalClauseOccurrenceRolesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List RetainedFinalCopiedClauseOccurrenceRole)
      encoding.Γ RetainedFinalCopiedClauseOccurrenceRole id id
      (fun symbols =>
        retainedFinalCopiedClauseOccurrenceRoles
          (directRetainedFinalClauseQueryAssembly decider symbols)) :=
  TM2CompositionMachine.computableInPolyTime
    (directRetainedFinalClauseQueryAssemblyComputableInPolyTime decider)
    retainedFinalCopiedClauseOccurrenceRolesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
