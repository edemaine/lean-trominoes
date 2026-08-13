import LeanTrominoes.PartrecFlatStripReach
import LeanTrominoes.StripFrontierCyclePartrec

/-!
# Native-flat strip cycle search

This module scans all ordered pairs of indexed frontier states while
preserving the native periodic-strip fields as an arbitrary suffix.  Each
candidate tests one raw frontier edge and one reverse Savitch-reachability
query, so a successful candidate lies on a directed cycle.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState
namespace FlatStripCyclePartrec

open LeanTrominoes.Computability
open LeanTrominoes.FiniteState
open Turing ToPartrec
open Turing.PartrecToTM2

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

private theorem boolToNat_eq_divideBoolTag (value : Bool) :
    value.toNat = divideBoolTag value := by
  cases value <;> rfl

/-- Predecessor of the current second-endpoint countdown in
`[stateCount, depth, first, secondRemaining, found] ++ stripFields`. -/
def candidateSecond : Code :=
  Code.pred.comp (Code.get 3)

/-- Build the canonical depth-zero DFS header used to ask whether the current
ordered pair is a raw frontier edge. -/
def candidateEdgeInputCode : Code :=
  Code.prepend Code.zero <|
    Code.prepend (Code.get 0) <|
      Code.prepend Code.zero <|
        Code.prepend Code.zero <|
          Code.prepend Code.zero <|
            Code.prepend (Code.get 2) <|
              Code.prepend candidateSecond (Code.drop 5)

@[simp]
theorem candidateEdgeInputCode_eval
    (stateCount depth first secondRemaining : Nat) (found : Bool)
    (suffix : List Nat) :
    candidateEdgeInputCode.eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++ suffix) =
      pure (divideEvalProgramList 0 stateCount
        (divideEvalInitial 0 first secondRemaining.pred) ++ suffix) := by
  simp [candidateEdgeInputCode, candidateSecond, divideEvalProgramList,
    divideEvalInitial, DivideEvalState.toNatList, divideOptionBoolTag,
    divideStackToNatList]

/-- Raw edge test for one ordered-pair candidate. -/
def candidateEdgeCode (tromino : Tromino) : Code :=
  (FlatStripEdgePartrec.transitionCode tromino).comp
    candidateEdgeInputCode

@[simp]
theorem candidateEdgeCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateEdgeCode tromino).eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (indexedTransitionRawBool tromino periodicStrip first
          secondRemaining.pred)] := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputRun := candidateEdgeInputCode_eval
    stateCount depth first secondRemaining found suffix
  calc
    _ = (FlatStripEdgePartrec.transitionCode tromino).eval
        (divideEvalProgramList 0 stateCount
          (divideEvalInitial 0 first secondRemaining.pred) ++ suffix) :=
      comp_eval_pure _ _ _ _ inputRun
    _ = _ := by
      have transition :=
        FlatStripEdgePartrec.transitionCode_eval tromino 0 stateCount
          (divideEvalInitial 0 first secondRemaining.pred)
          periodicStrip wellFormed
      simpa [suffix, divideEvalInitial, boolToNat_eq_divideBoolTag] using
        transition

/-- Build the reverse-reachability request for the current ordered pair. -/
def candidateReachInputCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend candidateSecond <|
        Code.prepend (Code.get 2) (Code.drop 5)

@[simp]
theorem candidateReachInputCode_eval
    (stateCount depth first secondRemaining : Nat) (found : Bool)
    (suffix : List Nat) :
    candidateReachInputCode.eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++ suffix) =
      pure ([stateCount, depth, secondRemaining.pred, first] ++ suffix) := by
  simp [candidateReachInputCode, candidateSecond]

/-- Reverse Savitch-reachability test for one ordered-pair candidate. -/
def candidateReachCode (tromino : Tromino) : Code :=
  (flatStripReachBoolCode tromino).comp candidateReachInputCode

@[simp]
theorem candidateReachCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateReachCode tromino).eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth secondRemaining.pred first)] := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputRun := candidateReachInputCode_eval
    stateCount depth first secondRemaining found suffix
  calc
    _ = (flatStripReachBoolCode tromino).eval
        ([stateCount, depth, secondRemaining.pred, first] ++ suffix) :=
      comp_eval_pure _ _ _ _ inputRun
    _ = _ := flatStripReachBoolCode_eval tromino periodicStrip wellFormed
      stateCount depth secondRemaining.pred first

/-- Accumulate the result of the current directed-cycle candidate. -/
def candidateFoundCode (tromino : Tromino) : Code :=
  Code.boolOr (Code.get 4)
    (Code.boolAnd (candidateEdgeCode tromino)
      (candidateReachCode tromino))

private theorem normalizedAndTag (left right : Bool) :
    (if divideBoolTag left = 0 ∨ divideBoolTag right = 0
      then 0 else 1) = divideBoolTag (left && right) := by
  cases left <;> cases right <;> rfl

private theorem normalizedOrTag (left right : Bool) :
    (if divideBoolTag left = 0 ∧ divideBoolTag right = 0
      then 0 else 1) = divideBoolTag (left || right) := by
  cases left <;> cases right <;> rfl

@[simp]
theorem candidateFoundCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateFoundCode tromino).eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (found || cycleCandidateBool tromino periodicStrip stateCount
          depth first secondRemaining.pred)] := by
  let values := [stateCount, depth, first, secondRemaining,
    divideBoolTag found] ++
      PeriodicStripFlatEncoding.stripFields periodicStrip
  let edge := indexedTransitionRawBool tromino periodicStrip first
    secondRemaining.pred
  let reach := divideReachIndexDFSBool stateCount
    (indexedTransitionRawBool tromino periodicStrip)
    depth secondRemaining.pred first
  have edgeRun : (candidateEdgeCode tromino).eval values =
      pure [divideBoolTag edge] := by
    exact candidateEdgeCode_eval tromino periodicStrip wellFormed
      stateCount depth first secondRemaining found
  have reachRun : (candidateReachCode tromino).eval values =
      pure [divideBoolTag reach] := by
    exact candidateReachCode_eval tromino periodicStrip wellFormed
      stateCount depth first secondRemaining found
  have bothRaw := Code.boolAnd_eval_at
    (candidateEdgeCode tromino) (candidateReachCode tromino)
    values (divideBoolTag edge) (divideBoolTag reach) edgeRun reachRun
  have bothRun :
      (Code.boolAnd (candidateEdgeCode tromino)
        (candidateReachCode tromino)).eval values =
          pure [divideBoolTag (edge && reach)] := by
    rw [normalizedAndTag] at bothRaw
    exact bothRaw
  have foundRun : (Code.get 4).eval values =
      pure [divideBoolTag found] := by
    simp [values]
  have resultRaw := Code.boolOr_eval_at (Code.get 4)
    (Code.boolAnd (candidateEdgeCode tromino)
      (candidateReachCode tromino)) values
    (divideBoolTag found) (divideBoolTag (edge && reach))
    foundRun bothRun
  rw [normalizedOrTag] at resultRaw
  simpa only [candidateFoundCode, values, edge, reach,
    cycleCandidateBool] using resultRaw

/-- One inner-loop update, preserving the native strip suffix. -/
def candidateStepCode (tromino : Tromino) : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend (Code.get 2) <|
        Code.prepend candidateSecond <|
          Code.prepend (candidateFoundCode tromino) (Code.drop 5)

@[simp]
theorem candidateStepCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateStepCode tromino).eval
        ([stateCount, depth, first, secondRemaining,
          divideBoolTag found] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure ([stateCount, depth, first, secondRemaining.pred,
        divideBoolTag
          (found || cycleCandidateBool tromino periodicStrip stateCount
            depth first secondRemaining.pred)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  have foundRun := candidateFoundCode_eval tromino periodicStrip wellFormed
    stateCount depth first secondRemaining found
  simp only [candidateStepCode, Code.prepend_eval_eq]
  rw [foundRun]
  simp [candidateSecond]

/-- The inner countdown scans exactly the second-state indices below
`remaining`, in descending order, while preserving the strip suffix. -/
theorem candidateCountdownCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first remaining : Nat) (found : Bool) :
    (Code.flatIterate (candidateStepCode tromino)).eval
        (remaining ::
          ([stateCount, depth, first, remaining, divideBoolTag found] ++
            PeriodicStripFlatEncoding.stripFields periodicStrip)) =
      pure ([stateCount, depth, first, 0,
        divideBoolTag
          (found || boundedAny
            (cycleCandidateBool tromino periodicStrip stateCount depth first)
            remaining)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  rw [Code.flatIterate, Code.fix_eval]
  apply Part.eq_some_iff.mpr
  induction remaining generalizing found with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [Code.flatCountdownBody_zero_eval, boundedAny]
  | succ remaining induction =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨remaining ::
        ([stateCount, depth, first, remaining,
          divideBoolTag
            (found || cycleCandidateBool tromino periodicStrip stateCount
              depth first remaining)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip), ?_, ?_⟩
      · have stepRun := candidateStepCode_eval tromino periodicStrip wellFormed
          stateCount depth first (remaining + 1) found
        have bodyRun :
            (Code.flatCountdownBody (candidateStepCode tromino)).eval
              ((remaining + 1) ::
                ([stateCount, depth, first, remaining + 1,
                  divideBoolTag found] ++
                  PeriodicStripFlatEncoding.stripFields periodicStrip)) =
              pure (1 :: remaining ::
                ([stateCount, depth, first, remaining,
                  divideBoolTag
                    (found || cycleCandidateBool tromino periodicStrip
                      stateCount depth first remaining)] ++
                  PeriodicStripFlatEncoding.stripFields periodicStrip)) := by
          change (candidateStepCode tromino).eval
              (stateCount :: depth :: first :: (remaining + 1) ::
                divideBoolTag found ::
                  PeriodicStripFlatEncoding.stripFields periodicStrip) = _
            at stepRun
          simp [Code.flatCountdownBody, stepRun]
        rw [bodyRun]
        simp
      · simpa [boundedAny, Bool.or_assoc] using
          induction
            (found || cycleCandidateBool tromino periodicStrip stateCount
              depth first remaining)

/-- Predecessor of the current first-endpoint countdown in
`[stateCount, depth, firstRemaining, found] ++ stripFields`. -/
def previousFirst : Code :=
  Code.pred.comp (Code.get 2)

/-- Build the complete second-endpoint countdown for one first endpoint. -/
def innerScanInputCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 0) <|
      Code.prepend (Code.get 1) <|
        Code.prepend previousFirst <|
          Code.prepend (Code.get 0) <|
            Code.prepend (Code.get 3) (Code.drop 4)

@[simp]
theorem innerScanInputCode_eval
    (stateCount depth firstRemaining : Nat) (found : Bool)
    (suffix : List Nat) :
    innerScanInputCode.eval
        ([stateCount, depth, firstRemaining, divideBoolTag found] ++ suffix) =
      pure (stateCount ::
        ([stateCount, depth, firstRemaining.pred, stateCount,
          divideBoolTag found] ++ suffix)) := by
  simp [innerScanInputCode, previousFirst]

/-- Remove the exhausted second-endpoint counter from an inner-scan result. -/
def innerScanOutputCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend (Code.get 2) <|
        Code.prepend (Code.get 4) (Code.drop 5)

/-- One outer-loop step: scan every second endpoint, decrement the current
first endpoint, and preserve the strip suffix. -/
def innerScanCode (tromino : Tromino) : Code :=
  innerScanOutputCode.comp <|
    (Code.flatIterate (candidateStepCode tromino)).comp innerScanInputCode

@[simp]
theorem innerScanCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth firstRemaining : Nat) (found : Bool) :
    (innerScanCode tromino).eval
        ([stateCount, depth, firstRemaining, divideBoolTag found] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure ([stateCount, depth, firstRemaining.pred,
        divideBoolTag
          (found || boundedAny
            (cycleCandidateBool tromino periodicStrip stateCount
              depth firstRemaining.pred) stateCount)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputRun := innerScanInputCode_eval
    stateCount depth firstRemaining found suffix
  have innerRun :
      ((Code.flatIterate (candidateStepCode tromino)).comp
        innerScanInputCode).eval
          ([stateCount, depth, firstRemaining, divideBoolTag found] ++ suffix) =
        pure ([stateCount, depth, firstRemaining.pred, 0,
          divideBoolTag
            (found || boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth firstRemaining.pred) stateCount)] ++ suffix) := by
    calc
      _ = (Code.flatIterate (candidateStepCode tromino)).eval
          (stateCount ::
            ([stateCount, depth, firstRemaining.pred, stateCount,
              divideBoolTag found] ++ suffix)) :=
        comp_eval_pure _ _ _ _ inputRun
      _ = _ := candidateCountdownCode_eval tromino periodicStrip wellFormed
        stateCount depth firstRemaining.pred stateCount found
  unfold innerScanCode
  calc
    _ = innerScanOutputCode.eval
        ([stateCount, depth, firstRemaining.pred, 0,
          divideBoolTag
            (found || boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth firstRemaining.pred) stateCount)] ++ suffix) :=
      comp_eval_pure _ _ _ _ innerRun
    _ = _ := by simp [innerScanOutputCode, suffix]

/-- The outer countdown scans every first endpoint below `remaining`. -/
theorem outerCountdownCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth remaining : Nat) (found : Bool) :
    (Code.flatIterate (innerScanCode tromino)).eval
        (remaining ::
          ([stateCount, depth, remaining, divideBoolTag found] ++
            PeriodicStripFlatEncoding.stripFields periodicStrip)) =
      pure ([stateCount, depth, 0,
        divideBoolTag
          (found || boundedAny
            (fun first => boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount depth first)
              stateCount) remaining)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  rw [Code.flatIterate, Code.fix_eval]
  apply Part.eq_some_iff.mpr
  induction remaining generalizing found with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [Code.flatCountdownBody_zero_eval, boundedAny]
  | succ remaining induction =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨remaining ::
        ([stateCount, depth, remaining,
          divideBoolTag
            (found || boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth remaining) stateCount)] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip), ?_, ?_⟩
      · have stepRun := innerScanCode_eval tromino periodicStrip wellFormed
          stateCount depth (remaining + 1) found
        have bodyRun :
            (Code.flatCountdownBody (innerScanCode tromino)).eval
              ((remaining + 1) ::
                ([stateCount, depth, remaining + 1, divideBoolTag found] ++
                  PeriodicStripFlatEncoding.stripFields periodicStrip)) =
              pure (1 :: remaining ::
                ([stateCount, depth, remaining,
                  divideBoolTag
                    (found || boundedAny
                      (cycleCandidateBool tromino periodicStrip stateCount
                        depth remaining) stateCount)] ++
                  PeriodicStripFlatEncoding.stripFields periodicStrip)) := by
          change (innerScanCode tromino).eval
              (stateCount :: depth :: (remaining + 1) ::
                divideBoolTag found ::
                  PeriodicStripFlatEncoding.stripFields periodicStrip) = _
            at stepRun
          simp [Code.flatCountdownBody, stepRun]
        rw [bodyRun]
        simp
      · simpa [boundedAny, Bool.or_assoc] using
          induction
            (found || boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth remaining) stateCount)

/-- Initialize both endpoint countdowns from
`[stateCount, depth] ++ stripFields`. -/
def cycleScanInputCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 0) <|
      Code.prepend (Code.get 1) <|
        Code.prepend (Code.get 0) <|
          Code.prepend Code.zero (Code.drop 2)

@[simp]
theorem cycleScanInputCode_eval
    (stateCount depth : Nat) (suffix : List Nat) :
    cycleScanInputCode.eval ([stateCount, depth] ++ suffix) =
      pure (stateCount ::
        ([stateCount, depth, stateCount, divideBoolTag false] ++ suffix)) := by
  simp [cycleScanInputCode, divideBoolTag]

/-- Complete native-flat parameterized cycle search.  Its input is
`[stateCount, depth] ++ stripFields`, and it returns one normalized Boolean
tag. -/
def flatStripCycleSearchCode (tromino : Tromino) : Code :=
  (Code.get 3).comp <|
    (Code.flatIterate (innerScanCode tromino)).comp cycleScanInputCode

@[simp]
theorem flatStripCycleSearchCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth : Nat) :
    (flatStripCycleSearchCode tromino).eval
        ([stateCount, depth] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (cycleSearchIndexDFSBoolAtDepth stateCount depth
          (indexedTransitionRawBool tromino periodicStrip))] := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputRun := cycleScanInputCode_eval stateCount depth suffix
  have scanRun :
      ((Code.flatIterate (innerScanCode tromino)).comp
        cycleScanInputCode).eval ([stateCount, depth] ++ suffix) =
        pure ([stateCount, depth, 0,
          divideBoolTag
            (boundedAny
              (fun first => boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth first) stateCount) stateCount)] ++ suffix) := by
    calc
      _ = (Code.flatIterate (innerScanCode tromino)).eval
          (stateCount ::
            ([stateCount, depth, stateCount, divideBoolTag false] ++ suffix)) :=
        comp_eval_pure _ _ _ _ inputRun
      _ = _ := by
        simpa using outerCountdownCode_eval tromino periodicStrip wellFormed
          stateCount depth stateCount false
  unfold flatStripCycleSearchCode
  calc
    _ = (Code.get 3).eval
        ([stateCount, depth, 0,
          divideBoolTag
            (boundedAny
              (fun first => boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth first) stateCount) stateCount)] ++ suffix) :=
      comp_eval_pure _ _ _ _ scanRun
    _ = _ := by
      simp [cycleSearchIndexDFSBoolAtDepth]
      rfl

end FlatStripCyclePartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
