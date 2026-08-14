/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterFrame

/-!
# Complete outer-frame range of the triangular emitter

The verified frame theorem is lifted over every selected outer marker.  The
machine emits the consecutive triangular frame blocks, empties `remaining`,
accumulates the completed positions in `processed`, and stops at `beginOuter`
before the final base and unwind suffix.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

/-- Consecutive semantic frame blocks before the final base/unwind suffix. -/
def frameRangeTokens {Data : Type} (parameters : Parameters Data)
    (first position : Nat) : Nat → List Token
  | 0 => []
  | count + 1 =>
      frameTokens parameters.outerFirst parameters.inner
          parameters.outerSecond parameters.innerBase parameters.innerCloser
          parameters.frameCloser first position count ++
        frameRangeTokens parameters first (position + 1) count

/-- Runtime of all consecutive outer frames. -/
def outerFrameRangeTime {Data : Type} (parameters : Parameters Data)
    (first position : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      outerFrameTime parameters first position count +
        outerFrameRangeTime parameters first (position + 1) count

/-- Execute all remaining outer frames. -/
def outerFrames_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (first position count : Nat)
    (data : TapeData Data)
    (remainingEq : data.remaining = List.replicate count ())
    (firstEq : data.first = List.replicate first ())
    (currentEq : data.current = [])
    (processedEq : data.processed = List.replicate position ())
    (innerEq : data.innerProcessed = [])
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.beginOuterCfg data)
      (some (parameters.beginOuterCfg
        { data with
          first := List.replicate first ()
          remaining := []
          current := []
          processed := List.replicate (position + count) ()
          innerProcessed := []
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((frameRangeTokens parameters first position count).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (outerFrameRangeTime parameters first position count) := by
  induction count generalizing position data with
  | zero =>
      have run := EvalsToInTime.refl parameters.transition
        (parameters.beginOuterCfg data)
      convert run using 1
      · congr 1
        cases data
        simp_all [frameRangeTokens]
      · rfl
  | succ count induction =>
      have firstFrame := outerFrame_evalsInTime parameters first position count
        data remainingEq firstEq currentEq processedEq innerEq firstScratchEq
          positionScratchEq
      let framedData : TapeData Data :=
        { data with
          first := List.replicate first ()
          remaining := List.replicate count ()
          current := []
          processed := List.replicate (position + 1) ()
          innerProcessed := []
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((frameTokens parameters.outerFirst parameters.inner
                parameters.outerSecond parameters.innerBase
                parameters.innerCloser parameters.frameCloser first position
                count).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }
      have rest := induction (position + 1) framedData rfl rfl rfl rfl rfl
        rfl rfl
      have composed := EvalsToInTime.trans parameters.transition
        (outerFrameTime parameters first position count)
        (outerFrameRangeTime parameters first (position + 1) count)
        (parameters.beginOuterCfg data)
        (parameters.beginOuterCfg framedData)
        (some (parameters.beginOuterCfg
          { framedData with
            first := List.replicate first ()
            remaining := []
            current := []
            processed := List.replicate (position + 1 + count) ()
            innerProcessed := []
            firstScratch := []
            positionScratch := []
            outputReverse :=
              ((frameRangeTokens parameters first (position + 1) count).map
                fun token => (Sum.inr token : Workspace Data)).reverse ++
                  framedData.outputReverse }))
        (by simpa [framedData] using firstFrame) rest
      convert composed using 1
      · simp [framedData, frameRangeTokens, List.map_append,
          List.reverse_append, List.append_assoc]
        have totalEq : position + (count + 1) =
            position + 1 + count := by omega
        rw [totalEq]
      · simp [outerFrameRangeTime]
        omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
