import LeanTrominoes.PartrecEvaluatorSpaceRefinement

/-!
# Compositional data costs for evaluator calls

`EvaluatorCallFits` uses a common absolute budget that includes the ambient
continuation.  This module separates the finite data cost of a code call from
that ambient continuation and supplies compositional rules for the primitive
code constructors.
-/

namespace Turing
namespace PartrecToTM2

@[simp]
theorem continuationSpace_cons₁
    (rest : ToPartrec.Code) (values : List Nat)
    (continuation : ToPartrec.Cont) :
    continuationSpace (.cons₁ rest values continuation) =
      encodedListSpace values + continuationSpace continuation + 1 := by
  simp [continuationSpace, trContStack, encodedListSpace]
  omega

@[simp]
theorem continuationSpace_cons₂
    (values : List Nat) (continuation : ToPartrec.Cont) :
    continuationSpace (.cons₂ values continuation) =
      encodedListSpace values + continuationSpace continuation + 1 := by
  simp [continuationSpace, trContStack, encodedListSpace]
  omega

@[simp]
theorem continuationSpace_comp
    (code : ToPartrec.Code) (continuation : ToPartrec.Cont) :
    continuationSpace (.comp code continuation) =
      continuationSpace continuation := by
  rfl

@[simp]
theorem continuationSpace_fix
    (code : ToPartrec.Code) (continuation : ToPartrec.Cont) :
    continuationSpace (.fix code continuation) =
      continuationSpace continuation := by
  rfl

/-- A continuation-independent data cost for one successful evaluator call.
The cost bounds both endpoint lists and is sufficient to prepend the call to
any already fitted execution under an ambient continuation. -/
structure EvaluatorCodeFits
    (code : ToPartrec.Code) (values output : List Nat)
    (cost : Nat) : Prop where
  input_space : encodedListSpace values ≤ cost
  output_space : encodedListSpace output ≤ cost
  call :
    ∀ continuation bound,
      cost + continuationSpace continuation ≤ bound →
      EvaluatorExecutionFits bound (.ret continuation output) →
      EvaluatorCallFits code continuation values bound

namespace EvaluatorCodeFits

/-- Enlarge the continuation-independent cost of a fitted code call. -/
theorem mono
    {code : ToPartrec.Code} {values output : List Nat}
    {small large : Nat}
    (fits : EvaluatorCodeFits code values output small)
    (cost : small ≤ large) :
    EvaluatorCodeFits code values output large where
  input_space := fits.input_space.trans cost
  output_space := fits.output_space.trans cost
  call continuation bound budget after :=
    fits.call continuation bound
      (by omega) after

/-- Data cost for `zero'`. -/
theorem zero' (values : List Nat) :
    EvaluatorCodeFits ToPartrec.Code.zero' values (0 :: values)
      (encodedListSpace values +
        encodedListSpace (0 :: values) + 1) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after :=
    EvaluatorCallFits.zero' after

/-- Data cost for the list-tail primitive. -/
theorem tail (values : List Nat) :
    EvaluatorCodeFits ToPartrec.Code.tail values values.tail
      (encodedListSpace values +
        encodedListSpace values.tail + 1) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after := by
    apply EvaluatorCallFits.tail
    · omega
    · exact after

/-- Data cost for binary successor.  The middle singleton accounts for the
transient head-extraction footprint in its low-level implementation. -/
theorem succ (values : List Nat) :
    EvaluatorCodeFits ToPartrec.Code.succ values
      [values.headI.succ]
      (encodedListSpace values +
        encodedListSpace [values.headI] +
        encodedListSpace [values.headI.succ] + 2) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after := by
    apply EvaluatorCallFits.succ
    · omega
    · omega
    · exact after

/-- Compose two finite data-cost certificates. -/
theorem comp
    {first second : ToPartrec.Code}
    {values middle output : List Nat}
    {firstCost secondCost : Nat}
    (firstFits :
      EvaluatorCodeFits first middle output firstCost)
    (secondFits :
      EvaluatorCodeFits second values middle secondCost) :
    EvaluatorCodeFits (.comp first second) values output
      (firstCost + secondCost) where
  input_space := by
    exact secondFits.input_space.trans (Nat.le_add_left _ _)
  output_space := by
    exact firstFits.output_space.trans (Nat.le_add_right _ _)
  call continuation bound budget after := by
    have middleSpace := firstFits.input_space
    have firstCall :=
      firstFits.call continuation bound (by omega) after
    have middleReturn :
        EvaluatorExecutionFits bound
          (.ret (.comp first continuation) middle) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact firstCall
    have secondCall :=
      secondFits.call (.comp first continuation) bound
        (by
          simp only [continuationSpace_comp]
          omega)
        middleReturn
    exact EvaluatorCallFits.comp secondCall

/-- Combine two calls with `cons`, retaining the original arguments during
the first call and the first result during the second. -/
theorem cons
    {first rest : ToPartrec.Code}
    {values firstOutput restOutput : List Nat}
    {firstCost restCost : Nat}
    (firstFits :
      EvaluatorCodeFits first values firstOutput firstCost)
    (restFits :
      EvaluatorCodeFits rest values restOutput restCost) :
    EvaluatorCodeFits (.cons first rest) values
      (firstOutput.headI :: restOutput)
      (firstCost + restCost +
        encodedListSpace values +
        encodedListSpace firstOutput +
        encodedListSpace (firstOutput.headI :: restOutput) + 2) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after := by
    have firstInputSpace := firstFits.input_space
    have firstOutputSpace := firstFits.output_space
    have restInputSpace := restFits.input_space
    have restOutputSpace := restFits.output_space
    have afterRest :
        EvaluatorExecutionFits bound
          (.ret (.cons₂ firstOutput continuation) restOutput) := by
      apply EvaluatorExecutionFits.ret_cons₂
      · simp only [continuationSpace_cons₂]
        omega
      · exact after
    have restCall :=
      restFits.call (.cons₂ firstOutput continuation) bound
        (by
          simp only [continuationSpace_cons₂]
          omega)
        afterRest
    have afterFirst :
        EvaluatorExecutionFits bound
          (.ret (.cons₁ rest values continuation) firstOutput) := by
      apply EvaluatorExecutionFits.ret_cons₁
      · simp only [continuationSpace_cons₁]
        omega
      · exact restCall
    have firstCall :=
      firstFits.call (.cons₁ rest values continuation) bound
        (by
          simp only [continuationSpace_cons₁]
          omega)
        afterFirst
    exact EvaluatorCallFits.cons firstCall

/-- Select the zero branch of a `case` call. -/
theorem case_zero
    {zeroBranch successorBranch : ToPartrec.Code}
    {values output : List Nat} {branchCost : Nat}
    (zero : values.headI = 0)
    (branch :
      EvaluatorCodeFits zeroBranch values.tail output branchCost) :
    EvaluatorCodeFits (.case zeroBranch successorBranch) values output
      (branchCost + encodedListSpace values +
        encodedListSpace output + 1) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after := by
    have branchCall :=
      branch.call continuation bound (by omega) after
    apply EvaluatorCallFits.case_zero zero
    · omega
    · exact branchCall

/-- Select the successor branch of a `case` call. -/
theorem case_succ
    {zeroBranch successorBranch : ToPartrec.Code}
    {values output : List Nat} {predecessor branchCost : Nat}
    (head : values.headI = predecessor + 1)
    (branch :
      EvaluatorCodeFits successorBranch
        (predecessor :: values.tail) output branchCost) :
    EvaluatorCodeFits (.case zeroBranch successorBranch) values output
      (branchCost + encodedListSpace values +
        encodedListSpace output + 1) where
  input_space := by omega
  output_space := by omega
  call continuation bound budget after := by
    have branchCall :=
      branch.call continuation bound (by omega) after
    apply EvaluatorCallFits.case_succ predecessor head
    · omega
    · exact branchCall

end EvaluatorCodeFits

end PartrecToTM2
end Turing
