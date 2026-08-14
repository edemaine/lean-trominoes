/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineWellFormedEmitterSpec
import LeanTrominoes.PeriodicCNFMarkedAffineEmitterPipeline
import LeanTrominoes.PeriodicCNFPolySpaceUnaryPreparedLayout
import LeanTrominoes.TM2CompositionMachine

/-!
# Polynomial-time bounded well-formedness emission

A one-symbol capped prefix tag is enough to distinguish the terminal stack
boundary from all later unary space markers.  Composing that marker with the
verified well-formedness phase schedule emits the normalized one-hot and
occupied-prefix constraints in polynomial time.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace PolySpaceWellFormedEmitter

open AffineEmitterPipeline
open BoundedMachineWellFormedEmitter
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding

abbrev Workspace :=
  AffineEmitterPipeline.Workspace (Symbol (encoding := encoding))

local instance symbolInhabited :
    Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

def workspaceSpace : Workspace (encoding := encoding) → Bool :=
  AffineTemplateEmitterMachine.dataSelected
    PolySpaceUnaryPreparedLayout.isSpace

def workspacePhases :
    List (Phase
      (BoundedMachineWellFormedEmitter.Marked 1
        (Workspace (encoding := encoding)))) :=
  BoundedMachineWellFormedEmitter.phases
    (tm := decider.tm) (cutoff := 1)
    (workspaceSpace (encoding := encoding))

/-- Input-preserving structural well-formedness pass on the shared token
workspace. -/
def runWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  MarkedAffineEmitterPipeline.run
    (workspaceSpace (encoding := encoding)) 1
    (workspacePhases decider) workspace

noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (runWorkspace decider) :=
  MarkedAffineEmitterPipeline.computableInPolyTime
    (workspaceSpace (encoding := encoding)) 1 (workspacePhases decider)

theorem workspaceSpace_count
    (data : List (Symbol (encoding := encoding))) (tokens : List Token) :
    UnaryPolynomialPaddingMachine.selectedCount
        (workspaceSpace (encoding := encoding))
        (embedData data ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      UnaryPolynomialPaddingMachine.selectedCount
        PolySpaceUnaryPreparedLayout.isSpace data := by
  exact selectedCount_embed_append_tokens
    PolySpaceUnaryPreparedLayout.isSpace data tokens

/-- Mark the first space boundary and emit all bounded well-formedness
constraints. -/
def emitted (data : List (Symbol (encoding := encoding))) : List Token :=
  emittedAll
    (BoundedMachineWellFormedEmitter.phases
      (tm := decider.tm) (cutoff := 1)
      PolySpaceUnaryPreparedLayout.isSpace)
    (mark PolySpaceUnaryPreparedLayout.isSpace 1 data)

/-- Prefix marking followed by the fixed affine schedule is polynomial-time. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Symbol (encoding := encoding))) (List Token)
      (Symbol (encoding := encoding)) Token id id (emitted decider) := by
  let marker := SelectedPrefixMarkerMachine.computableInPolyTime
    (Data := Symbol (encoding := encoding))
    PolySpaceUnaryPreparedLayout.isSpace 1
  let printer := AffineEmitterPipeline.emittedAllComputableInPolyTime
    (Data := BoundedMachineWellFormedEmitter.Marked 1
      (Symbol (encoding := encoding)))
    (BoundedMachineWellFormedEmitter.phases
      (Data := Symbol (encoding := encoding))
      (tm := decider.tm) (cutoff := 1)
      (PolySpaceUnaryPreparedLayout.isSpace (encoding := encoding)))
  let combined := TM2CompositionMachine.computableInPolyTime marker printer
  change @TM2ComputableInPolyTime
    (List (Symbol (encoding := encoding))) (List Token)
    (Symbol (encoding := encoding)) Token id id
    (fun data => emittedAll
      (BoundedMachineWellFormedEmitter.phases
        (tm := decider.tm) (cutoff := 1)
        PolySpaceUnaryPreparedLayout.isSpace)
      (mark PolySpaceUnaryPreparedLayout.isSpace 1 data))
  exact combined

theorem configurationSpace_haltList (tm : FinTM2)
    (symbols : List (tm.Γ tm.k₁)) :
    Complexity.configurationSpace tm (haltList tm symbols) =
      symbols.length := by
  classical
  unfold Complexity.configurationSpace
  rw [Fintype.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro stack stackNe
    simp [haltList, stackNe]

theorem spaceOfSymbols_positive (symbols : List encoding.Γ) :
    0 < PolySpaceCompiler.spaceOfSymbols decider symbols := by
  unfold PolySpaceCompiler.spaceOfSymbols
  have acceptingPositive :
      0 < Complexity.configurationSpace decider.tm
        (PolySpaceReduction.acceptingConfiguration decider) := by
    unfold PolySpaceReduction.acceptingConfiguration
    rw [configurationSpace_haltList, List.length_map]
    change 0 < (Turing.PartrecToTM2.trList
      [Encodable.encode true]).length
    simp [Turing.PartrecToTM2.trList]
  omega

/-- Exact input-preserving behavior on a genuine prepared word with any
previous token prefix. -/
theorem runWorkspace_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    runWorkspace decider
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        (tokens ++
          ofProgram
            (BoundedMachineProgram.wellFormedFields (tm := decider.tm)
              (space :=
                PolySpaceCompiler.spaceOfSymbols decider symbols))).map
          fun token =>
            (Sum.inr token : Workspace (encoding := encoding)) := by
  unfold runWorkspace
  rw [MarkedAffineEmitterPipeline.run_eq_append]
  simp only [List.map_append, ← List.append_assoc]
  congr 1
  apply congrArg (List.map fun token =>
    (Sum.inr token : Workspace (encoding := encoding)))
  apply BoundedMachineWellFormedEmitter.emittedAll_phases
  · omega
  · exact spaceOfSymbols_positive decider symbols
  · rw [workspaceSpace_count]
    change PolySpaceUnaryPreparedLayout.space
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) = _
    exact PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

/-- The actual prepared source word emits exactly the normalized structural
well-formedness prefix at its runtime stack width. -/
@[simp]
theorem emitted_preparedSources (symbols : List encoding.Γ) :
    emitted decider
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineProgram.wellFormedFields (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)) := by
  unfold emitted
  apply BoundedMachineWellFormedEmitter.emittedAll_phases
  · omega
  · exact spaceOfSymbols_positive decider symbols
  · exact PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

end PolySpaceWellFormedEmitter
end PeriodicCNF
end LeanTrominoes
