/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFixedMarkerThreshold
import LeanTrominoes.PeriodicCNFMarkedBivariateEmitterPipeline

/-!
# Fixed-threshold conditional bivariate emission

Pad a stable workspace with one sentinel, prefix-mark it at a fixed cutoff,
and use either complementary sentinel selector as a zero-or-one position
counter.  The first bivariate counter is the selected width beyond the
cutoff.  Both wrappers remove the sentinel after emission.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FixedMarkerThresholdEmitter

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

abbrev Recipe := BivariateProgramTemplates.Recipe
abbrev Workspace (Data : Type) := FixedMarkerPadding.Workspace Data
abbrev ExpandedWorkspace (Data : Type) :=
  FixedMarkerPadding.MarkedWorkspace Data

def emittedBelow (recipes : List Recipe) (cutoff space : Nat) : List Token :=
  BivariateTemplateEmitterMachine.positionRangeTokens recipes
    (space - cutoff) 0 (if space < cutoff then 1 else 0)

def emittedAt (recipes : List Recipe) (cutoff space : Nat) : List Token :=
  BivariateTemplateEmitterMachine.positionRangeTokens recipes
    (space - cutoff) 0 (if cutoff ≤ space then 1 else 0)

def runBranch {Data : Type} (selected : Data → Bool) (cutoff : Nat)
    (secondSelected :
      FixedMarkerThreshold.TaggedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    List (Workspace Data) :=
  FixedMarkerPadding.unpad
    (MarkedBivariateEmitterPipeline.run
      (FixedMarkerThreshold.workspaceSelected selected) cutoff
      (afterPrefix (FixedMarkerThreshold.workspaceSelected selected) cutoff)
      secondSelected recipes []
      (FixedMarkerPadding.padded 1 workspace))

theorem runBranch_eq_append {Data : Type} (selected : Data → Bool)
    (cutoff : Nat)
    (secondSelected :
      FixedMarkerThreshold.TaggedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    runBranch selected cutoff secondSelected recipes workspace =
      workspace ++
        (BivariateTemplateEmitterMachine.positionRangeTokens recipes
          (AffineTemplateEmitterMachine.selectedCount selected workspace -
            cutoff) 0
          (UnaryPolynomialPaddingMachine.selectedCount secondSelected
            (mark (FixedMarkerThreshold.workspaceSelected selected) cutoff
              (FixedMarkerPadding.padded 1 workspace)))).map fun token =>
                (Sum.inr token : Workspace Data) := by
  unfold runBranch
  rw [MarkedBivariateEmitterPipeline.run_eq_append,
    FixedMarkerPadding.unpad_append,
    FixedMarkerPadding.unpad_padded,
    FixedMarkerPadding.unpad_map_tokens]
  unfold MarkedBivariateEmitterPipeline.emitted
  rw [selectedCount_afterPrefix_mark
      (FixedMarkerThreshold.workspaceSelected selected)
      (Nat.le_refl cutoff),
    FixedMarkerThreshold.selectedCount_workspaceSelected_padded]
  simp

def runBelow {Data : Type} (selected : Data → Bool) (cutoff : Nat)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    List (Workspace Data) :=
  runBranch selected cutoff FixedMarkerThreshold.sentinelBelow
    recipes workspace

def runAt {Data : Type} (selected : Data → Bool) (cutoff : Nat)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    List (Workspace Data) :=
  runBranch selected cutoff FixedMarkerThreshold.sentinelAt
    recipes workspace

theorem runBelow_eq_append {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    runBelow selected cutoff recipes workspace =
      workspace ++
        (emittedBelow recipes cutoff
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold runBelow emittedBelow
  rw [runBranch_eq_append,
    FixedMarkerThreshold.selectedCount_sentinelBelow_mark_padded]

theorem runAt_eq_append {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    runAt selected cutoff recipes workspace =
      workspace ++
        (emittedAt recipes cutoff
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold runAt emittedAt
  rw [runBranch_eq_append,
    FixedMarkerThreshold.selectedCount_sentinelAt_mark_padded]

noncomputable def runBranchComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (cutoff : Nat)
    (secondSelected :
      FixedMarkerThreshold.TaggedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runBranch selected cutoff secondSelected recipes) := by
  let padded := FixedMarkerPadding.paddedComputableInPolyTime
    (Data := Data) 1
  let emitted := MarkedBivariateEmitterPipeline.computableInPolyTime
    (FixedMarkerThreshold.workspaceSelected selected) cutoff
    (afterPrefix (FixedMarkerThreshold.workspaceSelected selected) cutoff)
    secondSelected recipes []
  let throughEmission := TM2CompositionMachine.computableInPolyTime
    padded emitted
  let complete := TM2CompositionMachine.computableInPolyTime throughEmission
    (FixedMarkerPadding.unpadComputableInPolyTime (Data := Data))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      FixedMarkerPadding.unpad
        (MarkedBivariateEmitterPipeline.run
          (FixedMarkerThreshold.workspaceSelected selected) cutoff
          (afterPrefix
            (FixedMarkerThreshold.workspaceSelected selected) cutoff)
          secondSelected recipes []
          (FixedMarkerPadding.padded 1 workspace)))
  exact complete

noncomputable def runBelowComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (cutoff : Nat) (recipes : List Recipe) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runBelow selected cutoff recipes) :=
  runBranchComputableInPolyTime selected cutoff
    FixedMarkerThreshold.sentinelBelow recipes

noncomputable def runAtComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (cutoff : Nat) (recipes : List Recipe) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runAt selected cutoff recipes) :=
  runBranchComputableInPolyTime selected cutoff
    FixedMarkerThreshold.sentinelAt recipes

end FixedMarkerThresholdEmitter
end PeriodicCNF
end LeanTrominoes
