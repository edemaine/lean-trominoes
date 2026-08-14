/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerPosition

/-!
# Complete higher-position range of the triangular emitter

The verified one-position loop is lifted over every remaining higher marker.
The theorem records the exact consecutive bivariate position range, transfers
all markers from `remaining` to `innerProcessed`, and preserves every other
invariant stack with an explicit recursive runtime.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

/-- Runtime for consecutive inner positions beginning at `innerCount`. -/
def innerPositionRangeTime {Data : Type} (parameters : Parameters Data)
    (first outer innerCount : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      innerTemplateTime parameters first outer innerCount + 2 +
        innerPositionRangeTime parameters first outer (innerCount + 1) count

/-- Execute all remaining higher positions and collect them in
`innerProcessed`. -/
def innerPositions_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (first outer innerCount count : Nat)
    (data : TapeData Data)
    (remainingEq : data.remaining = List.replicate count ())
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate outer ())
    (innerEq : data.innerProcessed = List.replicate innerCount ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.beginInnerCfg data)
      (some (parameters.beginInnerCfg
        { data with
          first := List.replicate first ()
          remaining := []
          processed := List.replicate outer ()
          innerProcessed := List.replicate (innerCount + count) ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateTemplateEmitterMachine.positionRangeTokens
                parameters.inner first (outer + 1 + innerCount) count).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (innerPositionRangeTime parameters first outer innerCount count) := by
  induction count generalizing innerCount data with
  | zero =>
      have run := EvalsToInTime.refl parameters.transition
        (parameters.beginInnerCfg data)
      convert run using 1
      · congr 1
        cases data
        simp_all [BivariateTemplateEmitterMachine.positionRangeTokens]
      · rfl
  | succ count induction =>
      let tail := List.replicate count ()
      have remainingCons : data.remaining = () :: tail := by
        simpa [tail, List.replicate_succ] using remainingEq
      have firstPosition := innerPosition_evalsInTime parameters first outer
        innerCount tail data remainingCons firstEq processedEq innerEq
          firstScratchEq positionScratchEq
      let emittedData : TapeData Data :=
        { data with
          first := List.replicate first ()
          remaining := tail
          processed := List.replicate outer ()
          innerProcessed := List.replicate (innerCount + 1) ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateProgramTemplates.positionTokens parameters.inner first
                (outer + 1 + innerCount)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }
      have rest := induction (innerCount + 1) emittedData
        (by simp [emittedData, tail]) rfl rfl rfl rfl rfl
      have composed := EvalsToInTime.trans parameters.transition
        (innerTemplateTime parameters first outer innerCount + 2)
        (innerPositionRangeTime parameters first outer (innerCount + 1) count)
        (parameters.beginInnerCfg data)
        (parameters.beginInnerCfg emittedData)
        (some (parameters.beginInnerCfg
          { emittedData with
            first := List.replicate first ()
            remaining := []
            processed := List.replicate outer ()
            innerProcessed := List.replicate (innerCount + 1 + count) ()
            firstScratch := []
            positionScratch := []
            outputReverse :=
              ((BivariateTemplateEmitterMachine.positionRangeTokens
                  parameters.inner first (outer + 1 + (innerCount + 1))
                    count).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  emittedData.outputReverse }))
        (by simpa [emittedData] using firstPosition) rest
      convert composed using 1
      · simp [emittedData,
          BivariateTemplateEmitterMachine.positionRangeTokens_succ,
          BivariateTemplateEmitterMachine.positionTokens,
          List.map_append, List.reverse_append, List.append_assoc]
        have totalEq : innerCount + (count + 1) =
            innerCount + 1 + count := by omega
        have positionEq : outer + 1 + innerCount + 1 =
            outer + 1 + (innerCount + 1) := by omega
        rw [totalEq, positionEq]
      · simp [innerPositionRangeTime]
        omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
