import LeanTrominoes.IndexedSavitchDFSListEncoding
import LeanTrominoes.PartrecListCode

/-!
# Direct partial-recursive code for one flat Savitch DFS step

The program payload contains an immutable context natural, the graph-state
count, an explicit frame count, and the flat DFS state.  The frame count lets
`ToPartrec.Code.case` distinguish an empty stack even when a first frame field
is zero.  One externally supplied code computes the base-depth Boolean; all
continuation manipulation is compiled directly here.
-/

namespace LeanTrominoes.FiniteState

open Turing ToPartrec

/-- Machine-facing serialization: immutable context, graph-state count,
explicit frame count, then the flat semantic evaluator state. -/
def divideEvalProgramList (context stateCount : Nat)
    (state : DivideEvalState) : List Nat :=
  context :: stateCount :: state.stack.length :: state.toNatList

namespace DivideEvalPartrec

open Code

attribute [local simp] Part.bind_eq_bind

@[simp]
private theorem natRec_two
    {motive : Nat → Sort u} (zero : motive 0)
    (succ : (n : Nat) → motive n → motive (n + 1)) :
    Nat.rec (motive := motive) zero succ 2 =
      succ 1 (succ 0 zero) := rfl

def field (index : Nat) : Code :=
  Code.get index

def predecessorField (index : Nat) : Code :=
  Code.pred.comp (field index)

def fields (codes : List Code) (rest : Code) : Code :=
  codes.foldr Code.prepend rest

def noneDepthZero (baseBoolCode : Code) : Code :=
  fields
    [field 0, field 1, field 2, Code.someBoolTag baseBoolCode,
      field 4, field 5, field 6]
    (Code.drop 7)

def noneCountZero : Code :=
  fields
    [field 0, field 1, field 2, Code.one, field 4, field 5, field 6]
    (Code.drop 7)

def noneCountSucc : Code :=
  fields
    [field 0, field 1, Code.succ.comp (field 2), Code.zero,
      predecessorField 4, field 5, predecessorField 1,
      predecessorField 4, field 5, field 6, predecessorField 1,
      Code.zero, Code.zero]
    (Code.drop 7)

def noneDepthSucc : Code :=
  Code.branchZero (field 1) noneCountZero noneCountSucc

def answerNone (baseBoolCode : Code) : Code :=
  Code.branchZero (field 4) (noneDepthZero baseBoolCode) noneDepthSucc

def someLeftNone : Code :=
  fields
    [field 0, field 1, field 2, Code.zero,
      field 7, field 10, field 9,
      field 7, field 8, field 9, field 10, field 11, field 3]
    (Code.drop 13)

def accumulatedCode : Code :=
  Code.boolOr (field 11)
    (Code.boolAnd (predecessorField 12) (predecessorField 3))

def someLeftSomeMiddleZero : Code :=
  fields
    [field 0, field 1, predecessorField 2,
      Code.someBoolTag accumulatedCode, field 4, field 5, field 6]
    (Code.drop 13)

def someLeftSomeMiddleSucc : Code :=
  fields
    [field 0, field 1, field 2, Code.zero,
      field 7, field 8, predecessorField 10,
      field 7, field 8, field 9, predecessorField 10,
      accumulatedCode, Code.zero]
    (Code.drop 13)

def someLeftSome : Code :=
  Code.branchZero (field 10) someLeftSomeMiddleZero
    someLeftSomeMiddleSucc

def someFrame : Code :=
  Code.branchZero (field 12) someLeftNone someLeftSome

def answerSome : Code :=
  Code.branchZero (field 2) Code.id someFrame

/-- Direct code for one structural DFS transition.  `baseBoolCode` is called
only for a depth-zero query and must return a singleton natural truth tag for
the equality-or-edge test. -/
def stepCode (baseBoolCode : Code) : Code :=
  Code.branchZero (field 3) (answerNone baseBoolCode) answerSome

private theorem field_eval (index : Nat) (values : List Nat) :
    (field index).eval values = pure [values[index]?.getD 0] :=
  Code.get_eval index values

@[simp]
private theorem predecessorField_eval (index : Nat) (values : List Nat) :
    (predecessorField index).eval values =
      pure [(values[index]?.getD 0).pred] := by
  simp [predecessorField, field_eval, Part.bind_eq_bind]

set_option maxHeartbeats 1000000 in
theorem stepCode_eval
    (baseBoolCode : Code) (context stateCount : Nat)
    (relation : Nat → Nat → Bool) (state : DivideEvalState)
    (baseCorrect :
      baseBoolCode.eval (divideEvalProgramList context stateCount state) =
        pure [divideBoolTag
          (decide (state.query.first = state.query.last) ||
            relation state.query.first state.query.last)]) :
    (stepCode baseBoolCode).eval
        (divideEvalProgramList context stateCount state) =
      pure (divideEvalProgramList context stateCount
        (divideEvalStep stateCount relation state)) := by
  cases state with
  | mk query stack answer =>
      cases query with
      | mk depth first last =>
          cases answer with
          | none =>
              cases depth with
              | zero =>
                  cases baseValue :
                      (decide (first = last) ||
                        relation first last)
                  all_goals
                    simp [divideEvalProgramList,
                      DivideEvalState.toNatList, divideBoolTag,
                      divideOptionBoolTag, baseValue] at baseCorrect
                    have baseTag :
                        (Code.someBoolTag baseBoolCode).eval
                            (context :: stateCount :: stack.length ::
                              0 :: 0 :: first :: last ::
                                divideStackToNatList stack) =
                          pure [if divideBoolTag
                              (decide (first = last) ||
                                relation first last) = 0
                            then 1 else 2] := by
                      simp [Code.someBoolTag, Code.normalizeBool,
                        Code.branchZero, baseCorrect, baseValue,
                        divideBoolTag, Part.bind_eq_bind]
                    simp [stepCode, answerNone, noneDepthZero,
                      divideEvalProgramList, DivideEvalState.toNatList,
                      fields, field, Code.branchZero, divideEvalStep,
                      baseTag, baseValue, divideBoolTag,
                      divideOptionBoolTag, Part.bind_eq_bind]
              | succ depth =>
                  cases stateCount with
                  | zero =>
                      simp [stepCode, answerNone, noneDepthSucc,
                        noneCountZero, divideEvalProgramList,
                        DivideEvalState.toNatList, fields, field,
                        Code.branchZero, divideEvalStep,
                        divideOptionBoolTag, Part.bind_eq_bind]
                  | succ middle =>
                      simp [stepCode, answerNone, noneDepthSucc,
                        noneCountSucc, divideEvalProgramList,
                        DivideEvalState.toNatList, divideStackToNatList,
                        DivideFrame.toNatList, fields, field,
                        predecessorField, Code.branchZero, divideEvalStep,
                        divideBoolTag, divideOptionBoolTag,
                        Part.bind_eq_bind]
          | some answer =>
              cases answer <;>
                cases stack with
                | nil =>
                    simp [stepCode, answerSome, divideEvalProgramList,
                      DivideEvalState.toNatList, field,
                      Code.branchZero, divideEvalStep,
                      divideOptionBoolTag, Part.bind_eq_bind]
                | cons frame rest =>
                    cases frame with
                    | mk frameDepth frameFirst frameLast middle accumulated
                        leftAnswer =>
                        cases leftAnswer with
                        | none =>
                            simp [stepCode, answerSome, someFrame,
                              someLeftNone, divideEvalProgramList,
                              DivideEvalState.toNatList, divideStackToNatList,
                              DivideFrame.toNatList, fields, field,
                              Code.branchZero, divideEvalStep,
                              divideOptionBoolTag, Part.bind_eq_bind]
                        | some leftAnswer =>
                            cases middle with
                            | zero =>
                                cases accumulated <;> cases leftAnswer <;>
                                  simp [stepCode, answerSome, someFrame,
                                    someLeftSome, someLeftSomeMiddleZero,
                                    accumulatedCode, divideEvalProgramList,
                                    DivideEvalState.toNatList,
                                    divideStackToNatList,
                                    DivideFrame.toNatList, fields, field,
                                    predecessorField, Code.branchZero,
                                    Code.someBoolTag, Code.normalizeBool,
                                    Code.boolOr, Code.boolAnd, divideEvalStep,
                                    divideBoolTag, divideOptionBoolTag,
                                    Part.bind_eq_bind]
                            | succ middle =>
                                cases accumulated <;> cases leftAnswer <;>
                                  simp [stepCode, answerSome, someFrame,
                                    someLeftSome, someLeftSomeMiddleSucc,
                                    accumulatedCode, divideEvalProgramList,
                                    DivideEvalState.toNatList,
                                    divideStackToNatList,
                                    DivideFrame.toNatList, fields, field,
                                    predecessorField, Code.branchZero,
                                    Code.normalizeBool, Code.boolOr,
                                    Code.boolAnd, divideEvalStep,
                                    divideBoolTag, divideOptionBoolTag,
                                    Part.bind_eq_bind]

/-- The tail-recursive flat iterator agrees with repeated semantic DFS steps
on every machine-facing serialized evaluator state. -/
theorem flatIterate_stepCode_eval
    (baseBoolCode : Code) (context stateCount : Nat)
    (relation : Nat → Nat → Bool)
    (baseCorrect : ∀ state,
      baseBoolCode.eval (divideEvalProgramList context stateCount state) =
        pure [divideBoolTag
          (decide (state.query.first = state.query.last) ||
            relation state.query.first state.query.last)])
    (steps : Nat) (state : DivideEvalState) :
    (Code.flatIterate (stepCode baseBoolCode)).eval
        (steps :: divideEvalProgramList context stateCount state) =
      pure (divideEvalProgramList context stateCount
        ((divideEvalStep stateCount relation)^[steps] state)) := by
  rw [Code.flatIterate, Code.fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing state with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [Code.flatCountdownBody_zero_eval]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨steps :: divideEvalProgramList context stateCount
        (divideEvalStep stateCount relation state), ?_, ?_⟩
      · simp [Code.flatCountdownBody, stepCode_eval _ _ _ _ _
          (baseCorrect state)]
      · simpa [Function.iterate_succ_apply] using
          induction (divideEvalStep stateCount relation state)

end DivideEvalPartrec
end LeanTrominoes.FiniteState
