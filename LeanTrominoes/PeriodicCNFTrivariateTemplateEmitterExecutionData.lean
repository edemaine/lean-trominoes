/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterCleanup
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterPositionRange

/-! # Named configurations for trivariate-emitter execution -/

namespace LeanTrominoes

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens
open TrivariateTemplateEmitter

def firstCountOf {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) : Nat :=
  selectedCount selected workspace

def secondCountOf {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) : Nat :=
  selectedCount selected workspace

def positionCountOf {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) : Nat :=
  selectedCount selected workspace

def emittedOf {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    List Token :=
  positionRangeTokens recipes
    (firstCountOf firstSelected workspace)
    (secondCountOf secondSelected workspace) 0
    (positionCountOf positionSelected workspace)

def initialData {Data : Type}
    (workspace : List (Workspace Data)) : TapeData Data :=
  ⟨workspace, [], [], [], [], [], [], []⟩

def scannedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (workspace : List (Workspace Data)) : TapeData Data :=
  ⟨[], List.replicate (firstCountOf firstSelected workspace) (),
    List.replicate (secondCountOf secondSelected workspace) (),
    List.replicate (positionCountOf positionSelected workspace) (),
    [], [], workspace.reverse, []⟩

def positionedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    TapeData Data :=
  ⟨[], List.replicate (firstCountOf firstSelected workspace) (),
    List.replicate (secondCountOf secondSelected workspace) (), [],
    List.replicate (positionCountOf positionSelected workspace) (), [],
    (emittedOf firstSelected secondSelected positionSelected recipes workspace |>.map
      fun token => (Sum.inr token : Workspace Data)).reverse ++
      workspace.reverse,
    []⟩

def endedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : TapeData Data :=
  { positionedData firstSelected secondSelected positionSelected recipes
      workspace with
    outputReverse :=
      (ending.map fun token => (Sum.inr token : Workspace Data)).reverse ++
      (emittedOf firstSelected secondSelected positionSelected recipes
        workspace |>.map
          fun token => (Sum.inr token : Workspace Data)).reverse ++
      workspace.reverse }

def firstClearedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : TapeData Data :=
  { endedData firstSelected secondSelected positionSelected recipes ending
      workspace with first := [] }

def secondClearedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : TapeData Data :=
  { firstClearedData firstSelected secondSelected positionSelected recipes
      ending workspace with second := [] }

def clearedData {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : TapeData Data :=
  { secondClearedData firstSelected secondSelected positionSelected recipes
      ending workspace with processed := [] }

def emittedOutput {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  appendedOutput firstSelected secondSelected positionSelected recipes ending
    workspace

def prefixTime {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) : Nat :=
  workspace.length + 1 +
    positionRangeTime recipes
      (firstCountOf firstSelected workspace)
      (secondCountOf secondSelected workspace) 0
      (positionCountOf positionSelected workspace) + 1

def cleanupTime {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (workspace : List (Workspace Data)) : Nat :=
  (firstCountOf firstSelected workspace + 1) +
    (secondCountOf secondSelected workspace + 1) +
    (positionCountOf positionSelected workspace + 1)

def totalTime {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : Nat :=
  prefixTime firstSelected secondSelected positionSelected recipes workspace +
    cleanupTime firstSelected secondSelected positionSelected workspace +
    (emittedOutput firstSelected secondSelected positionSelected recipes ending
      workspace).length + 1

theorem endedData_outputReverse {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    (endedData firstSelected secondSelected positionSelected recipes ending
      workspace).outputReverse =
      (emittedOutput firstSelected secondSelected positionSelected recipes
        ending workspace).reverse := by
  unfold endedData positionedData emittedOutput emittedOf
    firstCountOf secondCountOf positionCountOf selectedCount appendedOutput
    dataSelected
  simp [List.map_append, List.reverse_append, List.append_assoc]
  congr 1

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
