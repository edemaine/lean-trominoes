import LeanTrominoes.PartrecFlatStripTransition
import LeanTrominoes.PartrecFuel

/-!
# Native-flat indexed strip reachability

This module wraps the suffix-preserving Savitch evaluator as one indexed
reachability query.  The request consists of four search fields followed by
the native periodic-strip fields; initialization computes exact fuel and
inserts the flat DFS header without packing or discarding that suffix.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

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

/-- Project state count and recursion depth from
`[stateCount, depth, first, last] ++ stripFields`. -/
def flatStripReachFuelArgumentsCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) Code.nil

/-- Compute exact fuel while retaining the original request as the caller's
input. -/
def flatStripReachFuelCode : Code :=
  Code.divideEvalFuelCode.comp flatStripReachFuelArgumentsCode

@[simp]
theorem flatStripReachFuelCode_eval
    (stateCount depth first last : Nat) (suffix : List Nat) :
    flatStripReachFuelCode.eval
        ([stateCount, depth, first, last] ++ suffix) =
      pure [divideEvalFuel stateCount depth] := by
  simp [flatStripReachFuelCode, flatStripReachFuelArgumentsCode]

/-- Convert the four fixed reachability fields plus an arbitrary native suffix
into exact fuel followed by the canonical flat DFS state and the same suffix.
-/
def flatStripReachInputCode : Code :=
  Code.prepend flatStripReachFuelCode <|
    Code.prepend Code.zero <|
      Code.prepend (Code.get 0) <|
        Code.prepend Code.zero <|
          Code.prepend Code.zero <|
            Code.prepend (Code.get 1) <|
              Code.prepend (Code.get 2) <|
                Code.prepend (Code.get 3) (Code.drop 4)

@[simp]
theorem flatStripReachInputCode_eval
    (stateCount depth first last : Nat) (suffix : List Nat) :
    flatStripReachInputCode.eval
        ([stateCount, depth, first, last] ++ suffix) =
      pure (divideEvalFuel stateCount depth ::
        (divideEvalProgramList 0 stateCount
          (divideEvalInitial depth first last) ++ suffix)) := by
  have fuelRun : flatStripReachFuelCode.eval
      ([stateCount, depth, first, last] ++ suffix) =
      pure [divideEvalFuel stateCount depth] :=
    flatStripReachFuelCode_eval stateCount depth first last suffix
  have fuelRun' : flatStripReachFuelCode.eval
      (stateCount :: depth :: first :: last :: suffix) =
      pure [divideEvalFuel stateCount depth] := by
    simpa using fuelRun
  simp [flatStripReachInputCode, fuelRun',
    divideEvalProgramList, divideEvalInitial, DivideEvalState.toNatList,
    divideOptionBoolTag, divideStackToNatList]

/-- Decide one native-flat indexed reachability query and return a normalized
natural Boolean tag. -/
def flatStripReachBoolCode (tromino : Tromino) : Code :=
  Code.pred.comp <|
    (Code.get 3).comp <|
      (Code.flatIterate
        (DivideEvalPartrec.stepCode
          (FlatStripEdgePartrec.baseCode tromino))).comp
        flatStripReachInputCode

/-- Final semantic state of one native-flat reachability query. -/
def flatStripReachFinalState
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount depth first last : Nat) : DivideEvalState :=
  ((divideEvalStep stateCount
      (indexedTransitionRawBool tromino periodicStrip))^[
        divideEvalFuel stateCount depth])
    (divideEvalInitial depth first last)

@[simp]
theorem flatStripReachBoolCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount depth first last : Nat) :
    (flatStripReachBoolCode tromino).eval
        ([stateCount, depth, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth first last)] := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  let finalState := flatStripReachFinalState tromino periodicStrip
    stateCount depth first last
  have inputRun := flatStripReachInputCode_eval
    stateCount depth first last suffix
  have loopRun := DivideEvalPartrec.flatIterate_stepCode_eval_suffix
    (FlatStripEdgePartrec.baseCode tromino) 0 stateCount
    (indexedTransitionRawBool tromino periodicStrip) suffix
    (fun state => FlatStripEdgePartrec.baseCode_eval
      tromino 0 stateCount state periodicStrip wellFormed)
    (divideEvalFuel stateCount depth)
    (divideEvalInitial depth first last)
  have flatRun :
      ((Code.flatIterate
          (DivideEvalPartrec.stepCode
            (FlatStripEdgePartrec.baseCode tromino))).comp
        flatStripReachInputCode).eval
          ([stateCount, depth, first, last] ++ suffix) =
        pure (divideEvalProgramList 0 stateCount finalState ++ suffix) := by
    calc
      _ = (Code.flatIterate
          (DivideEvalPartrec.stepCode
            (FlatStripEdgePartrec.baseCode tromino))).eval
          (divideEvalFuel stateCount depth ::
            (divideEvalProgramList 0 stateCount
              (divideEvalInitial depth first last) ++ suffix)) :=
        comp_eval_pure _ _ _ _ inputRun
      _ = _ := by
        simpa [finalState, flatStripReachFinalState] using loopRun
  have answerRun :
      ((Code.get 3).comp
        ((Code.flatIterate
          (DivideEvalPartrec.stepCode
            (FlatStripEdgePartrec.baseCode tromino))).comp
          flatStripReachInputCode)).eval
          ([stateCount, depth, first, last] ++ suffix) =
        pure [divideOptionBoolTag finalState.answer] := by
    calc
      _ = (Code.get 3).eval
          (divideEvalProgramList 0 stateCount finalState ++ suffix) :=
        comp_eval_pure _ _ _ _ flatRun
      _ = _ := by
        simp [divideEvalProgramList, DivideEvalState.toNatList]
  have answerTag :
      (divideOptionBoolTag finalState.answer).pred =
        divideBoolTag (finalState.answer.getD false) := by
    cases finalState.answer with
    | none => rfl
    | some answerValue => cases answerValue <;> rfl
  calc
    _ = Code.pred.eval [divideOptionBoolTag finalState.answer] :=
      comp_eval_pure _ _ _ _ answerRun
    _ = pure [(divideOptionBoolTag finalState.answer).pred] := by simp
    _ = pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth first last)] := by
      rw [answerTag]
      rfl

end RawWindowState
end PeriodicStrip
end LeanTrominoes
