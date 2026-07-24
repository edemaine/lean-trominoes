import LeanTrominoes.StripFrontierPartrec

/-!
# Flat partial-recursive strip cycle search

This module builds the outer driver around the compiled Savitch small step.
Each reachability query is initialized as a flat evaluator state and run for
its verified exact fuel.  Subsequent layers scan candidate graph edges while
retaining only counters, one Boolean accumulator, and one DFS stack.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open LeanTrominoes.Computability
open LeanTrominoes.FiniteState
open Turing ToPartrec
open Turing.PartrecToTM2

attribute [local simp] Part.bind_eq_bind

private local instance : Inhabited PeriodicStrip :=
  ⟨{ width := 0, period := 0, motif := [] }⟩

private theorem comp_eval_pure (outer inner : Code)
    (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

private def divideEvalFuelVector (values : List.Vector Nat 2) : Nat :=
  divideEvalFuel values.head values.tail.head

private theorem divideEvalFuelVector_primrec :
    Primrec divideEvalFuelVector := by
  unfold divideEvalFuelVector
  exact divideEvalFuel_primrec.comp
    Primrec.vector_head
    (Primrec.vector_head.comp Primrec.vector_tail)

private noncomputable def divideEvalFuelCode : Code :=
  codeOfVectorPrimrec divideEvalFuelVector
    divideEvalFuelVector_primrec

private theorem divideEvalFuelCode_eval (stateCount depth : Nat) :
    divideEvalFuelCode.eval [stateCount, depth] =
      pure [divideEvalFuel stateCount depth] := by
  let input : List.Vector Nat 2 :=
    ⟨[stateCount, depth], rfl⟩
  have correctness :=
    codeOfVectorPrimrec_eval divideEvalFuelVector
      divideEvalFuelVector_primrec input
  change divideEvalFuelCode.eval [stateCount, depth] =
    pure [divideEvalFuel stateCount depth] at correctness
  exact correctness

private def fuelArguments : Code :=
  Code.prepend (Code.get 1) <|
    Code.prepend (Code.get 2) Code.nil

private noncomputable def fuelOnReachInput : Code :=
  divideEvalFuelCode.comp fuelArguments

/-- Convert `[context, stateCount, depth, first, last]` into the countdown
input for the flat evaluator. -/
private noncomputable def reachInputCode : Code :=
  Code.prepend fuelOnReachInput <|
    Code.prepend (Code.get 0) <|
      Code.prepend (Code.get 1) <|
        Code.prepend Code.zero <|
          Code.prepend Code.zero <|
            Code.prepend (Code.get 2) <|
              Code.prepend (Code.get 3) <|
                Code.prepend (Code.get 4) Code.nil

private theorem reachInputCode_eval
    (context stateCount depth first last : Nat) :
    reachInputCode.eval [context, stateCount, depth, first, last] =
      pure (divideEvalFuel stateCount depth ::
        divideEvalProgramList context stateCount
          (divideEvalInitial depth first last)) := by
  simp [reachInputCode, fuelOnReachInput, fuelArguments,
    divideEvalFuelCode_eval, divideEvalProgramList,
    divideEvalInitial, DivideEvalState.toNatList,
    divideOptionBoolTag, divideStackToNatList]

/-- Decide one indexed reachability query, returning a normalized natural
Boolean tag. -/
noncomputable def stripReachBoolCode (tromino : Tromino) : Code :=
  Code.pred.comp <|
    (Code.get 3).comp <|
      (Code.flatIterate
        (FiniteState.DivideEvalPartrec.stepCode
          (stripBaseBoolCode tromino))).comp reachInputCode

theorem stripReachBoolCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first last : Nat) :
    (stripReachBoolCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth, first, last] =
      pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth first last)] := by
  let finalState :=
    ((divideEvalStep stateCount
      (indexedTransitionRawBool tromino periodicStrip))^[
        divideEvalFuel stateCount depth])
      (divideEvalInitial depth first last)
  have run :=
    stripFlatIterate_eval tromino periodicStrip stateCount
      (divideEvalFuel stateCount depth)
      (divideEvalInitial depth first last)
  have flatRun :
      ((Code.flatIterate
        (FiniteState.DivideEvalPartrec.stepCode
          (stripBaseBoolCode tromino))).comp reachInputCode).eval
          [Encodable.encode periodicStrip, stateCount, depth, first, last] =
        pure (divideEvalProgramList (Encodable.encode periodicStrip)
          stateCount finalState) := by
    calc
      _ = (Code.flatIterate
          (FiniteState.DivideEvalPartrec.stepCode
            (stripBaseBoolCode tromino))).eval
          (divideEvalFuel stateCount depth ::
            divideEvalProgramList (Encodable.encode periodicStrip)
              stateCount (divideEvalInitial depth first last)) :=
        comp_eval_pure _ _ _ _
          (reachInputCode_eval _ _ _ _ _)
      _ = _ := run
  have answerRun :
      ((Code.get 3).comp
        ((Code.flatIterate
          (FiniteState.DivideEvalPartrec.stepCode
            (stripBaseBoolCode tromino))).comp reachInputCode)).eval
          [Encodable.encode periodicStrip, stateCount, depth, first, last] =
        pure [divideOptionBoolTag finalState.answer] := by
    calc
      _ = (Code.get 3).eval
          (divideEvalProgramList (Encodable.encode periodicStrip)
            stateCount finalState) :=
        comp_eval_pure _ _ _ _ flatRun
      _ = _ := by
        simp [divideEvalProgramList, DivideEvalState.toNatList]
  have answerTag :
      (divideOptionBoolTag finalState.answer).pred =
        divideBoolTag (finalState.answer.getD false) := by
    cases finalState.answer with
    | none => rfl
    | some answerValue =>
        cases answerValue <;> rfl
  calc
    _ = Code.pred.eval [divideOptionBoolTag finalState.answer] :=
      comp_eval_pure _ _ _ _ answerRun
    _ = pure [(divideOptionBoolTag finalState.answer).pred] := by
      simp
    _ = pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth first last)] := by
      rw [answerTag]
      rfl

private def candidateSecond : Code :=
  Code.pred.comp (Code.get 4)

private def candidateEdgeArguments : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 3) <|
      Code.prepend candidateSecond Code.nil

private noncomputable def candidateEdgeCode
    (tromino : Tromino) : Code :=
  (stripEdgeVectorCode tromino).comp candidateEdgeArguments

private theorem candidateEdgeCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateEdgeCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth, first,
          secondRemaining, divideBoolTag found] =
      pure [divideBoolTag
        (indexedTransitionRawBool tromino periodicStrip first
          secondRemaining.pred)] := by
  have arguments :
      candidateEdgeArguments.eval
          [Encodable.encode periodicStrip, stateCount, depth, first,
            secondRemaining, divideBoolTag found] =
        pure [Encodable.encode periodicStrip, first,
          secondRemaining.pred] := by
    simp [candidateEdgeArguments, candidateSecond]
  calc
    _ = (stripEdgeVectorCode tromino).eval
        [Encodable.encode periodicStrip, first, secondRemaining.pred] :=
      comp_eval_pure _ _ _ _ arguments
    _ = _ := stripEdgeVectorCode_eval _ _ _ _

private def candidateReachArguments : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend (Code.get 2) <|
        Code.prepend candidateSecond <|
          Code.prepend (Code.get 3) Code.nil

private noncomputable def candidateReachCode
    (tromino : Tromino) : Code :=
  (stripReachBoolCode tromino).comp candidateReachArguments

private theorem candidateReachCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateReachCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth, first,
          secondRemaining, divideBoolTag found] =
      pure [divideBoolTag
        (divideReachIndexDFSBool stateCount
          (indexedTransitionRawBool tromino periodicStrip)
          depth secondRemaining.pred first)] := by
  have arguments :
      candidateReachArguments.eval
          [Encodable.encode periodicStrip, stateCount, depth, first,
            secondRemaining, divideBoolTag found] =
        pure [Encodable.encode periodicStrip, stateCount, depth,
          secondRemaining.pred, first] := by
    simp [candidateReachArguments, candidateSecond]
  calc
    _ = (stripReachBoolCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth,
          secondRemaining.pred, first] :=
      comp_eval_pure _ _ _ _ arguments
    _ = _ := stripReachBoolCode_eval _ _ _ _ _ _

/-- Predicate tested for one directed-cycle candidate edge. -/
private def cycleCandidateBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (stateCount depth first last : Nat) :
    Bool :=
  indexedTransitionRawBool tromino periodicStrip first last &&
    divideReachIndexDFSBool stateCount
      (indexedTransitionRawBool tromino periodicStrip)
      depth last first

private noncomputable def candidateFoundCode
    (tromino : Tromino) : Code :=
  Code.boolOr (Code.get 5)
    (Code.boolAnd (candidateEdgeCode tromino)
      (candidateReachCode tromino))

private theorem normalizedAndTag (left right : Bool) :
    (if divideBoolTag left = 0 ∨ divideBoolTag right = 0
      then 0 else 1) =
        divideBoolTag (left && right) := by
  cases left <;> cases right <;> rfl

private theorem normalizedOrTag (left right : Bool) :
    (if divideBoolTag left = 0 ∧ divideBoolTag right = 0
      then 0 else 1) =
        divideBoolTag (left || right) := by
  cases left <;> cases right <;> rfl

private theorem candidateFoundCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateFoundCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth, first,
          secondRemaining, divideBoolTag found] =
      pure [divideBoolTag
        (found || cycleCandidateBool tromino periodicStrip stateCount
          depth first secondRemaining.pred)] := by
  let values :=
    [Encodable.encode periodicStrip, stateCount, depth, first,
      secondRemaining, divideBoolTag found]
  let edge :=
    indexedTransitionRawBool tromino periodicStrip first
      secondRemaining.pred
  let reach :=
    divideReachIndexDFSBool stateCount
      (indexedTransitionRawBool tromino periodicStrip)
      depth secondRemaining.pred first
  have edgeRun :
      (candidateEdgeCode tromino).eval values =
        pure [divideBoolTag edge] := by
    exact candidateEdgeCode_eval tromino periodicStrip stateCount depth
      first secondRemaining found
  have reachRun :
      (candidateReachCode tromino).eval values =
        pure [divideBoolTag reach] := by
    exact candidateReachCode_eval tromino periodicStrip stateCount depth
      first secondRemaining found
  have bothRaw :=
    Code.boolAnd_eval_at
      (candidateEdgeCode tromino) (candidateReachCode tromino)
      values (divideBoolTag edge) (divideBoolTag reach)
      edgeRun reachRun
  have bothRun :
      (Code.boolAnd (candidateEdgeCode tromino)
        (candidateReachCode tromino)).eval values =
          pure [divideBoolTag (edge && reach)] := by
    rw [normalizedAndTag] at bothRaw
    exact bothRaw
  have foundRun :
      (Code.get 5).eval values = pure [divideBoolTag found] := by
    simp [values]
  have resultRaw :=
    Code.boolOr_eval_at (Code.get 5)
      (Code.boolAnd (candidateEdgeCode tromino)
        (candidateReachCode tromino))
      values (divideBoolTag found) (divideBoolTag (edge && reach))
      foundRun bothRun
  rw [normalizedOrTag] at resultRaw
  simpa only [candidateFoundCode, values, edge, reach,
    cycleCandidateBool] using resultRaw

/-- One inner-loop update.  The second-state countdown is decremented and
the candidate result is accumulated in a normalized Boolean field. -/
private noncomputable def candidateStepCode
    (tromino : Tromino) : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend (Code.get 2) <|
        Code.prepend (Code.get 3) <|
          Code.prepend candidateSecond <|
            Code.prepend (candidateFoundCode tromino) Code.nil

private theorem candidateStepCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first secondRemaining : Nat) (found : Bool) :
    (candidateStepCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth, first,
          secondRemaining, divideBoolTag found] =
      pure [Encodable.encode periodicStrip, stateCount, depth, first,
        secondRemaining.pred,
        divideBoolTag
          (found || cycleCandidateBool tromino periodicStrip stateCount
            depth first secondRemaining.pred)] := by
  simp [candidateStepCode, candidateSecond,
    candidateFoundCode_eval]

/-- Running the inner countdown checks exactly the second-state indices below
`remaining`, in descending order. -/
private theorem candidateCountdownCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth first remaining : Nat) (found : Bool) :
    (Code.flatIterate (candidateStepCode tromino)).eval
        (remaining ::
          [Encodable.encode periodicStrip, stateCount, depth, first,
            remaining, divideBoolTag found]) =
      pure [Encodable.encode periodicStrip, stateCount, depth, first, 0,
        divideBoolTag
          (found ||
            boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth first)
              remaining)] := by
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
        [Encodable.encode periodicStrip, stateCount, depth, first,
          remaining,
          divideBoolTag
            (found ||
              cycleCandidateBool tromino periodicStrip stateCount
                depth first remaining)], ?_, ?_⟩
      · simp [Code.flatCountdownBody,
          candidateStepCode_eval]
      · simpa [boundedAny, Bool.or_assoc] using
          induction
            (found ||
              cycleCandidateBool tromino periodicStrip stateCount
                depth first remaining)

private def previousFirst : Code :=
  Code.pred.comp (Code.get 3)

/-- Build the inner countdown from an outer-loop payload
`[context, count, depth, firstRemaining, found]`. -/
private def innerScanInputCode : Code :=
  Code.prepend (Code.get 1) <|
    Code.prepend (Code.get 0) <|
      Code.prepend (Code.get 1) <|
        Code.prepend (Code.get 2) <|
          Code.prepend previousFirst <|
            Code.prepend (Code.get 1) <|
              Code.prepend (Code.get 4) Code.nil

private theorem innerScanInputCode_eval
    (context stateCount depth firstRemaining : Nat) (found : Bool) :
    innerScanInputCode.eval
        [context, stateCount, depth, firstRemaining,
          divideBoolTag found] =
      pure (stateCount ::
        [context, stateCount, depth, firstRemaining.pred,
          stateCount, divideBoolTag found]) := by
  simp [innerScanInputCode, previousFirst]

private def innerScanOutputCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 1) <|
      Code.prepend (Code.get 2) <|
        Code.prepend (Code.get 3) <|
          Code.prepend (Code.get 5) Code.nil

/-- One outer-loop step: scan every possible second endpoint for the current
first endpoint, then decrement the first-state countdown. -/
private noncomputable def innerScanCode (tromino : Tromino) : Code :=
  innerScanOutputCode.comp <|
    (Code.flatIterate (candidateStepCode tromino)).comp
      innerScanInputCode

private theorem innerScanCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth firstRemaining : Nat) (found : Bool) :
    (innerScanCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth,
          firstRemaining, divideBoolTag found] =
      pure [Encodable.encode periodicStrip, stateCount, depth,
        firstRemaining.pred,
        divideBoolTag
          (found ||
            boundedAny
              (cycleCandidateBool tromino periodicStrip stateCount
                depth firstRemaining.pred)
              stateCount)] := by
  have innerRun :
      ((Code.flatIterate (candidateStepCode tromino)).comp
        innerScanInputCode).eval
          [Encodable.encode periodicStrip, stateCount, depth,
            firstRemaining, divideBoolTag found] =
        pure [Encodable.encode periodicStrip, stateCount, depth,
          firstRemaining.pred, 0,
          divideBoolTag
            (found ||
              boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth firstRemaining.pred)
                stateCount)] := by
    calc
      _ = (Code.flatIterate (candidateStepCode tromino)).eval
          (stateCount ::
            [Encodable.encode periodicStrip, stateCount, depth,
              firstRemaining.pred, stateCount, divideBoolTag found]) :=
        comp_eval_pure _ _ _ _
          (innerScanInputCode_eval _ _ _ _ _)
      _ = _ :=
        candidateCountdownCode_eval tromino periodicStrip stateCount
          depth firstRemaining.pred stateCount found
  unfold innerScanCode
  calc
    _ = innerScanOutputCode.eval
        [Encodable.encode periodicStrip, stateCount, depth,
          firstRemaining.pred, 0,
          divideBoolTag
            (found ||
              boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth firstRemaining.pred)
                stateCount)] :=
      comp_eval_pure _ _ _ _ innerRun
    _ = _ := by
      simp [innerScanOutputCode]

/-- The outer countdown checks exactly the first-state indices below
`remaining`; each step invokes the complete inner countdown. -/
private theorem outerCountdownCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (stateCount depth remaining : Nat) (found : Bool) :
    (Code.flatIterate (innerScanCode tromino)).eval
        (remaining ::
          [Encodable.encode periodicStrip, stateCount, depth,
            remaining, divideBoolTag found]) =
      pure [Encodable.encode periodicStrip, stateCount, depth, 0,
        divideBoolTag
          (found ||
            boundedAny
              (fun first =>
                boundedAny
                  (cycleCandidateBool tromino periodicStrip stateCount
                    depth first)
                  stateCount)
              remaining)] := by
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
        [Encodable.encode periodicStrip, stateCount, depth, remaining,
          divideBoolTag
            (found ||
              boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth remaining)
                stateCount)], ?_, ?_⟩
      · simp [Code.flatCountdownBody,
          innerScanCode_eval]
      · simpa [boundedAny, Bool.or_assoc] using
          induction
            (found ||
              boundedAny
                (cycleCandidateBool tromino periodicStrip stateCount
                  depth remaining)
                stateCount)

private def cycleScanInputCode : Code :=
  Code.prepend (Code.get 1) <|
    Code.prepend (Code.get 0) <|
      Code.prepend (Code.get 1) <|
        Code.prepend (Code.get 2) <|
          Code.prepend (Code.get 1) <|
            Code.prepend Code.zero Code.nil

private theorem cycleScanInputCode_eval
    (context stateCount depth : Nat) :
    cycleScanInputCode.eval [context, stateCount, depth] =
      pure (stateCount ::
        [context, stateCount, depth, stateCount, divideBoolTag false]) := by
  simp [cycleScanInputCode, divideBoolTag]

/-- Complete parameterized strip cycle-search code.  Its input is
`[encodedStrip, stateCount, depth]`, and its output is one normalized Boolean
tag. -/
noncomputable def stripCycleSearchCode (tromino : Tromino) : Code :=
  (Code.get 4).comp <|
    (Code.flatIterate (innerScanCode tromino)).comp cycleScanInputCode

theorem stripCycleSearchCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (stateCount depth : Nat) :
    (stripCycleSearchCode tromino).eval
        [Encodable.encode periodicStrip, stateCount, depth] =
      pure [divideBoolTag
        (cycleSearchIndexDFSBoolAtDepth stateCount depth
          (indexedTransitionRawBool tromino periodicStrip))] := by
  have scanRun :
      ((Code.flatIterate (innerScanCode tromino)).comp
        cycleScanInputCode).eval
          [Encodable.encode periodicStrip, stateCount, depth] =
        pure [Encodable.encode periodicStrip, stateCount, depth, 0,
          divideBoolTag
            (boundedAny
              (fun first =>
                boundedAny
                  (cycleCandidateBool tromino periodicStrip stateCount
                    depth first)
                  stateCount)
              stateCount)] := by
    calc
      _ = (Code.flatIterate (innerScanCode tromino)).eval
          (stateCount ::
            [Encodable.encode periodicStrip, stateCount, depth,
              stateCount, divideBoolTag false]) :=
        comp_eval_pure _ _ _ _
          (cycleScanInputCode_eval _ _ _)
      _ = _ := by
        simpa using
          outerCountdownCode_eval tromino periodicStrip stateCount
            depth stateCount false
  unfold stripCycleSearchCode
  calc
    _ = (Code.get 4).eval
        [Encodable.encode periodicStrip, stateCount, depth, 0,
          divideBoolTag
            (boundedAny
              (fun first =>
                boundedAny
                  (cycleCandidateBool tromino periodicStrip stateCount
                    depth first)
                  stateCount)
              stateCount)] :=
      comp_eval_pure _ _ _ _ scanRun
    _ = _ := by
      simp [cycleSearchIndexDFSBoolAtDepth]
      rfl

/-- Unary code computing the exact sparse-frontier state count. -/
noncomputable def stripIndexCountCode : Code :=
  codeOfPrimrec indexCount indexCount_primrec

theorem stripIndexCountCode_eval
    (periodicStrip : PeriodicStrip) :
    stripIndexCountCode.eval [Encodable.encode periodicStrip] =
      pure [indexCount periodicStrip] := by
  apply Part.eq_some_iff.mpr
  simpa [stripIndexCountCode] using
    codeOfPrimrec_eval indexCount indexCount_primrec periodicStrip

/-- Unary code computing the certified Savitch search depth. -/
noncomputable def stripSearchDepthCode : Code :=
  codeOfPrimrec stripSearchDepth stripSearchDepth_primrec

theorem stripSearchDepthCode_eval
    (periodicStrip : PeriodicStrip) :
    stripSearchDepthCode.eval [Encodable.encode periodicStrip] =
      pure [stripSearchDepth periodicStrip] := by
  apply Part.eq_some_iff.mpr
  simpa [stripSearchDepthCode] using
    codeOfPrimrec_eval stripSearchDepth stripSearchDepth_primrec
      periodicStrip

private theorem encodeBool_eq_divideBoolTag (value : Bool) :
    Encodable.encode value = divideBoolTag value := by
  cases value <;> rfl

/-- Unary code deciding whether a strip presentation is well formed. -/
noncomputable def stripWellFormedCode : Code :=
  codeOfPrimrec PeriodicStrip.wellFormed
    periodicStrip_wellFormed_primrec

theorem stripWellFormedCode_eval
    (periodicStrip : PeriodicStrip) :
    stripWellFormedCode.eval [Encodable.encode periodicStrip] =
      pure [divideBoolTag periodicStrip.wellFormed] := by
  apply Part.eq_some_iff.mpr
  simpa [stripWellFormedCode, encodeBool_eq_divideBoolTag] using
    codeOfPrimrec_eval PeriodicStrip.wellFormed
      periodicStrip_wellFormed_primrec periodicStrip

/-- Assemble the encoded strip, state count, and search depth consumed by the
parameterized cycle search. -/
noncomputable def stripCycleParametersCode : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend stripIndexCountCode <|
      Code.prepend stripSearchDepthCode Code.nil

theorem stripCycleParametersCode_eval
    (periodicStrip : PeriodicStrip) :
    stripCycleParametersCode.eval [Encodable.encode periodicStrip] =
      pure [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip] := by
  simp [stripCycleParametersCode, stripIndexCountCode_eval,
    stripSearchDepthCode_eval]

/-- Guard the parameterized cycle search by strip well-formedness. -/
noncomputable def guardedStripCycleCode (tromino : Tromino) : Code :=
  Code.boolAnd stripWellFormedCode <|
    (stripCycleSearchCode tromino).comp stripCycleParametersCode

private theorem periodicStripTrominoTilingIndexBool_eq_and
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    periodicStripTrominoTilingIndexBool tromino periodicStrip =
      (periodicStrip.wellFormed &&
        cycleSearchIndexDFSBoolAtDepth
          (indexCount periodicStrip)
          (stripSearchDepth periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)) := by
  by_cases wellFormed : periodicStrip.IsWellFormed
  · have wellFormedBool : periodicStrip.wellFormed = true :=
      (periodicStrip.wellFormed_eq_true_iff).mpr wellFormed
    simp [periodicStripTrominoTilingIndexBool, wellFormed,
      wellFormedBool]
    rfl
  · have wellFormedBool : periodicStrip.wellFormed = false := by
      apply Bool.eq_false_iff.mpr
      intro true
      exact wellFormed
        ((periodicStrip.wellFormed_eq_true_iff).mp true)
    simp [periodicStripTrominoTilingIndexBool, wellFormed,
      wellFormedBool]

/-- Unary evaluator code for the executable strip-tiling decider.  The input
is the standard natural encoding of `PeriodicStrip`; malformed presentations
return false before their cycle result can affect the answer. -/
noncomputable def periodicStripTrominoTilingCode
    (tromino : Tromino) : Code :=
  guardedStripCycleCode tromino

theorem periodicStripTrominoTilingCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    (periodicStripTrominoTilingCode tromino).eval
        [Encodable.encode periodicStrip] =
      pure [Encodable.encode
        (periodicStripTrominoTilingIndexBool tromino periodicStrip)] := by
  let cycleResult :=
    cycleSearchIndexDFSBoolAtDepth
      (indexCount periodicStrip)
      (stripSearchDepth periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip)
  have cycleArguments :=
    stripCycleParametersCode_eval periodicStrip
  have cycleRun :
      ((stripCycleSearchCode tromino).comp
        stripCycleParametersCode).eval
          [Encodable.encode periodicStrip] =
        pure [divideBoolTag cycleResult] := by
    calc
      _ = (stripCycleSearchCode tromino).eval
          [Encodable.encode periodicStrip, indexCount periodicStrip,
            stripSearchDepth periodicStrip] :=
        comp_eval_pure _ _ _ _ cycleArguments
      _ = _ :=
        stripCycleSearchCode_eval tromino periodicStrip
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)
  have guardedRun :=
    Code.boolAnd_eval_at stripWellFormedCode
      ((stripCycleSearchCode tromino).comp
        stripCycleParametersCode)
      [Encodable.encode periodicStrip]
      (divideBoolTag periodicStrip.wellFormed)
      (divideBoolTag cycleResult)
      (stripWellFormedCode_eval periodicStrip) cycleRun
  rw [normalizedAndTag] at guardedRun
  unfold periodicStripTrominoTilingCode guardedStripCycleCode
  rw [periodicStripTrominoTilingIndexBool_eq_and,
    encodeBool_eq_divideBoolTag]
  exact guardedRun

end RawWindowState
end PeriodicStrip
end LeanTrominoes
