/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SelectedPrefixMarkerIntervals
import LeanTrominoes.PeriodicCNFMarkedAffineEmitterPipeline
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterTime

/-!
# Prefix-marked bivariate emitter pipelines

Mark a stable shared workspace by capped selected-prefix count, embed the
tagged word for the verified bivariate emitter, then erase the tags while
retaining every original item and emitted token.  The two bivariate counters
may select arbitrary fixed predicates of the tagged data.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace MarkedBivariateEmitterPipeline

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

abbrev Recipe := BivariateProgramTemplates.Recipe
abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data
abbrev MarkedWorkspace (cutoff : Nat) (Data : Type) :=
  Tagged cutoff (Workspace Data)
abbrev NestedWorkspace (cutoff : Nat) (Data : Type) :=
  Workspace (MarkedWorkspace cutoff Data)

def emitted {Data : Type} (selected : Workspace Data → Bool)
    (cutoff : Nat)
    (firstSelected secondSelected : MarkedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List Token :=
  BivariateTemplateEmitterMachine.positionRangeTokens recipes
      (UnaryPolynomialPaddingMachine.selectedCount firstSelected
        (mark selected cutoff workspace)) 0
      (UnaryPolynomialPaddingMachine.selectedCount secondSelected
        (mark selected cutoff workspace)) ++
    ending

def run {Data : Type} (selected : Workspace Data → Bool)
    (cutoff : Nat)
    (firstSelected secondSelected : MarkedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  MarkedAffineEmitterPipeline.flatten
    (BivariateTemplateEmitterMachine.appendedOutput
      firstSelected secondSelected recipes ending
      (embedData (mark selected cutoff workspace)))

@[simp]
theorem selectedCount_embedData {Data : Type} (selected : Data → Bool)
    (data : List Data) :
    BivariateTemplateEmitterMachine.selectedCount selected (embedData data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  unfold BivariateTemplateEmitterMachine.selectedCount embedData
  induction data with
  | nil => rfl
  | cons item data induction =>
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        BivariateTemplateEmitterMachine.dataSelected, induction]

/-- Exact input-preserving behavior on an arbitrary existing workspace. -/
theorem run_eq_append {Data : Type} (selected : Workspace Data → Bool)
    (cutoff : Nat)
    (firstSelected secondSelected : MarkedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    run selected cutoff firstSelected secondSelected recipes ending workspace =
      workspace ++
        (emitted selected cutoff firstSelected secondSelected recipes ending
          workspace).map fun token => (Sum.inr token : Workspace Data) := by
  unfold run emitted BivariateTemplateEmitterMachine.appendedOutput
  rw [selectedCount_embedData, selectedCount_embedData]
  rw [show MarkedAffineEmitterPipeline.flatten
        (embedData (mark selected cutoff workspace) ++
          (BivariateTemplateEmitterMachine.positionRangeTokens recipes
              (UnaryPolynomialPaddingMachine.selectedCount firstSelected
                (mark selected cutoff workspace)) 0
              (UnaryPolynomialPaddingMachine.selectedCount secondSelected
                (mark selected cutoff workspace)) ++
            ending).map fun token =>
              (Sum.inr token : NestedWorkspace cutoff Data)) =
      MarkedAffineEmitterPipeline.flatten
          (embedData (mark selected cutoff workspace)) ++
        MarkedAffineEmitterPipeline.flatten
          ((BivariateTemplateEmitterMachine.positionRangeTokens recipes
                (UnaryPolynomialPaddingMachine.selectedCount firstSelected
                  (mark selected cutoff workspace)) 0
                (UnaryPolynomialPaddingMachine.selectedCount secondSelected
                  (mark selected cutoff workspace)) ++
              ending).map fun token =>
                (Sum.inr token : NestedWorkspace cutoff Data)) by
      simp [MarkedAffineEmitterPipeline.flatten, List.flatMap_append]]
  rw [MarkedAffineEmitterPipeline.flatten_embedData_mark,
    MarkedAffineEmitterPipeline.flatten_map_tokens]

/-- Prefix marking, bivariate emission, and tag removal are polynomial time
for every fixed cutoff and fixed templates. -/
noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Workspace Data → Bool) (cutoff : Nat)
    (firstSelected secondSelected : MarkedWorkspace cutoff Data → Bool)
    (recipes : List Recipe) (ending : List Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run selected cutoff firstSelected secondSelected recipes ending) := by
  let marker := SelectedPrefixMarkerMachine.computableInPolyTime
    (Data := Workspace Data) selected cutoff
  let embed := AffineEmitterPipeline.embedDataComputableInPolyTime
    (Data := MarkedWorkspace cutoff Data)
  let markedAndEmbedded :=
    TM2CompositionMachine.computableInPolyTime marker embed
  let printer := BivariateTemplateEmitterMachine.computableInPolyTime
    firstSelected secondSelected recipes ending
  let printed :=
    TM2CompositionMachine.computableInPolyTime markedAndEmbedded printer
  let untag := FiniteBlockTransducer.computableInPolyTime
    (fun item : NestedWorkspace cutoff Data =>
      match item with
      | .inl (workspaceItem, _) => [workspaceItem]
      | .inr token => [(Sum.inr token : Workspace Data)])
  let complete := TM2CompositionMachine.computableInPolyTime printed untag
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      MarkedAffineEmitterPipeline.flatten
        (BivariateTemplateEmitterMachine.appendedOutput
          firstSelected secondSelected recipes ending
          (embedData (mark selected cutoff workspace))))
  exact complete

end MarkedBivariateEmitterPipeline
end PeriodicCNF
end LeanTrominoes
