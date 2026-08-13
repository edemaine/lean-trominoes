/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedSavitchDFS

/-!
# Correctness of depth-first indexed Savitch evaluation

The explicit evaluator checks every midpoint, so a query at a fixed depth has
an exact running time independent of the relation.  The main theorem below
uses that schedule to compose the two recursive child calls at each midpoint
and proves that the final answer is the recursive `divideReachIndexBool`
specification.
-/

namespace LeanTrominoes.FiniteState

private theorem iterate_trans {α : Type*} (function : α → α)
    {first middle last : α} {firstSteps lastSteps : Nat}
    (firstRun : (function^[firstSteps]) first = middle)
    (lastRun : (function^[lastSteps]) middle = last) :
    (function^[lastSteps + firstSteps]) first = last := by
  rw [Function.iterate_add_apply, firstRun, lastRun]

theorem divideEvalQuery_correct
    (stateCount : Nat) (relation : Nat → Nat → Bool) :
    ∀ depth first last stack,
      ∃ finalQuery,
        ((divideEvalStep stateCount relation)^[
            divideEvalFuel stateCount depth])
            { query := ⟨depth, first, last⟩
              stack
              answer := none } =
          { query := finalQuery
            stack
            answer :=
              some (divideReachIndexBool stateCount relation
                depth first last) } := by
  intro depth
  induction depth with
  | zero =>
      intro first last stack
      exact ⟨⟨0, first, last⟩, by
        simp [divideEvalFuel, divideEvalStep, divideReachIndexBool]⟩
  | succ depth depthInduction =>
      intro first last stack
      cases count : stateCount with
      | zero =>
          exact ⟨⟨depth + 1, first, last⟩, by
            simp [divideEvalFuel, divideEvalStep,
              divideReachIndexBool, boundedAny]⟩
      | succ lastMiddle =>
          let childSteps := divideEvalFuel stateCount depth
          let chunkSteps := 2 * childSteps + 2
          let predicate : Nat → Bool := fun middle =>
            divideReachIndexBool stateCount relation depth first middle &&
              divideReachIndexBool stateCount relation depth middle last
          have loop :
              ∀ middle accumulated,
                ∃ finalQuery,
                  ((divideEvalStep stateCount relation)^[
                      (middle + 1) * chunkSteps])
                      { query := ⟨depth, first, middle⟩
                        stack :=
                          { depth
                            first
                            last
                            middle
                            accumulated
                            leftAnswer := none } :: stack
                        answer := none } =
                    { query := finalQuery
                      stack
                      answer :=
                        some (accumulated ||
                          boundedAny predicate (middle + 1)) } := by
            intro middle
            induction middle with
            | zero =>
                intro accumulated
                obtain ⟨leftQuery, leftRun⟩ :=
                  depthInduction first 0
                    ({ depth
                       first
                       last
                       middle := 0
                       accumulated
                       leftAnswer := none } :: stack)
                have deliverLeft :
                    divideEvalStep stateCount relation
                        { query := leftQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := 0
                              accumulated
                              leftAnswer := none } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth first 0) } =
                      { query := ⟨depth, 0, last⟩
                        stack :=
                          { depth
                            first
                            last
                            middle := 0
                            accumulated
                            leftAnswer :=
                              some (divideReachIndexBool stateCount relation
                                depth first 0) } :: stack
                        answer := none } := by
                  simp [divideEvalStep]
                obtain ⟨rightQuery, rightRun⟩ :=
                  depthInduction 0 last
                    ({ depth
                       first
                       last
                       middle := 0
                       accumulated
                       leftAnswer :=
                         some (divideReachIndexBool stateCount relation
                           depth first 0) } :: stack)
                have deliverRight :
                    divideEvalStep stateCount relation
                        { query := rightQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := 0
                              accumulated
                              leftAnswer :=
                                some (divideReachIndexBool stateCount relation
                                  depth first 0) } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth 0 last) } =
                      { query := rightQuery
                        stack
                        answer :=
                          some (accumulated || predicate 0) } := by
                  simp [divideEvalStep, predicate]
                refine ⟨rightQuery, ?_⟩
                have firstPart := iterate_trans
                  (divideEvalStep stateCount relation)
                  leftRun
                  (show
                    ((divideEvalStep stateCount relation)^[1])
                        { query := leftQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := 0
                              accumulated
                              leftAnswer := none } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth first 0) } =
                      { query := ⟨depth, 0, last⟩
                        stack :=
                          { depth
                            first
                            last
                            middle := 0
                            accumulated
                            leftAnswer :=
                              some (divideReachIndexBool stateCount relation
                                depth first 0) } :: stack
                        answer := none } by
                    simpa using deliverLeft)
                have secondPart := iterate_trans
                  (divideEvalStep stateCount relation)
                  firstPart rightRun
                have whole := iterate_trans
                  (divideEvalStep stateCount relation)
                  secondPart
                  (show
                    ((divideEvalStep stateCount relation)^[1])
                        { query := rightQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := 0
                              accumulated
                              leftAnswer :=
                                some (divideReachIndexBool stateCount relation
                                  depth first 0) } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth 0 last) } =
                      { query := rightQuery
                        stack
                        answer :=
                          some (accumulated || predicate 0) } by
                    simpa using deliverRight)
                have stepsEqual :
                    (0 + 1) * chunkSteps =
                      1 + (divideEvalFuel stateCount depth +
                        (1 + divideEvalFuel stateCount depth)) := by
                  simp [childSteps, chunkSteps]
                  omega
                rw [stepsEqual]
                simpa [boundedAny] using whole
            | succ middle middleInduction =>
                intro accumulated
                obtain ⟨leftQuery, leftRun⟩ :=
                  depthInduction first (middle + 1)
                    ({ depth
                       first
                       last
                       middle := middle + 1
                       accumulated
                       leftAnswer := none } :: stack)
                have deliverLeft :
                    divideEvalStep stateCount relation
                        { query := leftQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := middle + 1
                              accumulated
                              leftAnswer := none } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth first (middle + 1)) } =
                      { query := ⟨depth, middle + 1, last⟩
                        stack :=
                          { depth
                            first
                            last
                            middle := middle + 1
                            accumulated
                            leftAnswer :=
                              some (divideReachIndexBool stateCount relation
                                depth first (middle + 1)) } :: stack
                        answer := none } := by
                  simp [divideEvalStep]
                obtain ⟨rightQuery, rightRun⟩ :=
                  depthInduction (middle + 1) last
                    ({ depth
                       first
                       last
                       middle := middle + 1
                       accumulated
                       leftAnswer :=
                         some (divideReachIndexBool stateCount relation
                           depth first (middle + 1)) } :: stack)
                let nextAccumulated := accumulated || predicate (middle + 1)
                have deliverRight :
                    divideEvalStep stateCount relation
                        { query := rightQuery
                          stack :=
                            { depth
                              first
                              last
                              middle := middle + 1
                              accumulated
                              leftAnswer :=
                                some (divideReachIndexBool stateCount relation
                                  depth first (middle + 1)) } :: stack
                          answer :=
                            some (divideReachIndexBool stateCount relation
                              depth (middle + 1) last) } =
                      { query := ⟨depth, first, middle⟩
                        stack :=
                          { depth
                            first
                            last
                            middle
                            accumulated := nextAccumulated
                            leftAnswer := none } :: stack
                        answer := none } := by
                  simp [divideEvalStep, predicate, nextAccumulated]
                obtain ⟨finalQuery, remainingRun⟩ :=
                  middleInduction nextAccumulated
                refine ⟨finalQuery, ?_⟩
                have firstPart := iterate_trans
                  (divideEvalStep stateCount relation)
                  leftRun
                  (show
                    ((divideEvalStep stateCount relation)^[1]) _ = _ by
                      simpa using deliverLeft)
                have secondPart := iterate_trans
                  (divideEvalStep stateCount relation)
                  firstPart rightRun
                have chunkRun := iterate_trans
                  (divideEvalStep stateCount relation)
                  secondPart
                  (show
                    ((divideEvalStep stateCount relation)^[1]) _ = _ by
                      simpa using deliverRight)
                have whole := iterate_trans
                  (divideEvalStep stateCount relation)
                  chunkRun remainingRun
                have stepsEqual :
                    (middle + 1 + 1) * chunkSteps =
                      (middle + 1) * chunkSteps +
                        (1 + (divideEvalFuel stateCount depth +
                          (1 + divideEvalFuel stateCount depth))) := by
                  simp [childSteps, chunkSteps]
                  ring
                rw [stepsEqual]
                simpa [nextAccumulated, boundedAny, Bool.or_assoc] using whole
          obtain ⟨finalQuery, loopRun⟩ := loop lastMiddle false
          refine ⟨finalQuery, ?_⟩
          have initialStep :
              ((divideEvalStep stateCount relation)^[1])
                  { query := ⟨depth + 1, first, last⟩
                    stack
                    answer := none } =
                { query := ⟨depth, first, lastMiddle⟩
                  stack :=
                    { depth
                      first
                      last
                      middle := lastMiddle
                      accumulated := false
                      leftAnswer := none } :: stack
                  answer := none } := by
            simp [divideEvalStep, count]
          have whole := iterate_trans
            (divideEvalStep stateCount relation)
            initialStep loopRun
          have stepsEqual :
              divideEvalFuel stateCount (depth + 1) =
                (lastMiddle + 1) * chunkSteps + 1 := by
            simp [divideEvalFuel, chunkSteps, childSteps, count]
            omega
          have stepsEqual' :
              divideEvalFuel (lastMiddle + 1) (depth + 1) =
                (lastMiddle + 1) * chunkSteps + 1 := by
            simpa [count] using stepsEqual
          rw [stepsEqual']
          simpa [divideReachIndexBool, predicate, count] using whole

theorem divideReachIndexDFSBool_eq
    (stateCount : Nat) (relation : Nat → Nat → Bool)
    (depth first last : Nat) :
    divideReachIndexDFSBool stateCount relation depth first last =
      divideReachIndexBool stateCount relation depth first last := by
  obtain ⟨finalQuery, evaluation⟩ :=
    divideEvalQuery_correct stateCount relation depth first last []
  unfold divideReachIndexDFSBool divideEvalInitial
  rw [evaluation]
  rfl

theorem cycleSearchIndexDFSBoolAtDepth_eq
    (stateCount depth : Nat) (relation : Nat → Nat → Bool) :
    cycleSearchIndexDFSBoolAtDepth stateCount depth relation =
      cycleSearchIndexBoolAtDepth stateCount depth relation := by
  unfold cycleSearchIndexDFSBoolAtDepth cycleSearchIndexBoolAtDepth
  congr 1
  funext first
  congr 1
  funext second
  rw [divideReachIndexDFSBool_eq]

end LeanTrominoes.FiniteState
