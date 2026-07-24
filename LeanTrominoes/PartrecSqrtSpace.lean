import LeanTrominoes.PartrecSqrt
import LeanTrominoes.PartrecListCodeSpace
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Evaluator-space certificate for natural square root

The explicit square-root scan keeps three naturals bounded linearly by the
input.  This module fits its branch code and flat countdown under that
invariant.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def sqrtHitCost (values : List Nat) : Nat :=
  let gap := values[0]?.getD 0
  let root := values[1]?.getD 0
  let rootCost :=
    succCost [root] + getCost 1 values
  let gapCost :=
    addConstCost 2 [gap] + getCost 0 values
  let restCost :=
    prependCost values [gap + 2] [root + 1]
      gapCost rootCost
  prependCost values [gap + 2] [gap + 2, root + 1]
    gapCost restCost

theorem sqrtHit (values : List Nat) :
    EvaluatorCodeFits Code.sqrtHitCode values
      [values[0]?.getD 0 + 2, values[0]?.getD 0 + 2,
        values[1]?.getD 0 + 1]
      (sqrtHitCost values) := by
  let gap := values[0]?.getD 0
  let root := values[1]?.getD 0
  have rootResult :=
    comp (succ_named [root]) (get 1 values)
  have gapResult :=
    comp (addConst 2 [gap]) (get 0 values)
  have rest :=
    prepend gapResult rootResult
  have result :=
    prepend gapResult rest
  simpa [Code.sqrtHitCode, sqrtHitCost,
    gap, root, prependCost] using result

def sqrtMissCost (values : List Nat) : Nat :=
  let restCost :=
    prependCost values [values[1]?.getD 0]
      [values[2]?.getD 0]
      (getCost 1 values) (getCost 2 values)
  prependCost values [values.headI + 1]
    [values[1]?.getD 0, values[2]?.getD 0]
    (succCost values) restCost

theorem sqrtMiss (values : List Nat) :
    EvaluatorCodeFits Code.sqrtMissCode values
      [values.headI + 1, values[1]?.getD 0,
        values[2]?.getD 0]
      (sqrtMissCost values) := by
  have rest := prepend (get 1 values) (get 2 values)
  have result := prepend (succ_named values) rest
  simpa [Code.sqrtMissCode, sqrtMissCost,
    prependCost] using result

def sqrtZeroCost (values : List Nat) : Nat :=
  let restCost :=
    prependCost values [values[0]?.getD 0]
      [values[1]?.getD 0]
      (getCost 0 values) (getCost 1 values)
  prependCost values [0]
    [values[0]?.getD 0, values[1]?.getD 0]
    (zeroCost values) restCost

theorem sqrtZero (values : List Nat) :
    EvaluatorCodeFits Code.sqrtZeroCode values
      [0, values[0]?.getD 0, values[1]?.getD 0]
      (sqrtZeroCost values) := by
  have rest := prepend (get 0 values) (get 1 values)
  have result := prepend (zero values) rest
  simpa [Code.sqrtZeroCode, sqrtZeroCost,
    prependCost] using result

def sqrtStepCost (values : List Nat) : Nat :=
  match values.headI with
  | 0 =>
      sqrtZeroCost values.tail +
        encodedListSpace values +
          encodedListSpace (Code.sqrtStepList values) + 1
  | predecessor + 1 =>
      let innerValues := predecessor :: values.tail
      let innerCost :=
        match predecessor with
        | 0 =>
            sqrtHitCost innerValues.tail +
              encodedListSpace innerValues +
                encodedListSpace (Code.sqrtStepList values) + 1
        | innerPredecessor + 1 =>
            sqrtMissCost (innerPredecessor :: innerValues.tail) +
              encodedListSpace innerValues +
                encodedListSpace (Code.sqrtStepList values) + 1
      innerCost + encodedListSpace values +
        encodedListSpace (Code.sqrtStepList values) + 1

theorem sqrtStep (values : List Nat) :
    EvaluatorCodeFits Code.sqrtStepCode values
      (Code.sqrtStepList values) (sqrtStepCost values) := by
  cases values with
  | nil =>
      simpa [Code.sqrtStepCode, Code.sqrtStepList,
        sqrtStepCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .case Code.sqrtHitCode Code.sqrtMissCode)
          (values := ([] : List Nat))
          rfl (sqrtZero [])
  | cons distance rest =>
      cases distance with
      | zero =>
          simpa [Code.sqrtStepCode, Code.sqrtStepList,
            sqrtStepCost] using
            EvaluatorCodeFits.case_zero
              (successorBranch :=
                .case Code.sqrtHitCode Code.sqrtMissCode)
              (values := 0 :: rest)
              rfl (sqrtZero rest)
      | succ predecessor =>
          cases predecessor with
          | zero =>
              have inner :
                  EvaluatorCodeFits
                    (.case Code.sqrtHitCode Code.sqrtMissCode)
                    (0 :: rest) (Code.sqrtStepList (1 :: rest))
                    (sqrtHitCost rest +
                      encodedListSpace (0 :: rest) +
                        encodedListSpace
                          (Code.sqrtStepList (1 :: rest)) + 1) := by
                simpa [Code.sqrtStepList] using
                  EvaluatorCodeFits.case_zero
                    (successorBranch := Code.sqrtMissCode)
                    (values := 0 :: rest)
                    rfl (sqrtHit rest)
              simpa [Code.sqrtStepCode, sqrtStepCost] using
                EvaluatorCodeFits.case_succ
                  (zeroBranch := Code.sqrtZeroCode)
                  (values := 1 :: rest) (predecessor := 0)
                  rfl inner
          | succ innerPredecessor =>
              have inner :
                  EvaluatorCodeFits
                    (.case Code.sqrtHitCode Code.sqrtMissCode)
                    ((innerPredecessor + 1) :: rest)
                    (Code.sqrtStepList
                      ((innerPredecessor + 2) :: rest))
                    (sqrtMissCost (innerPredecessor :: rest) +
                      encodedListSpace
                        ((innerPredecessor + 1) :: rest) +
                      encodedListSpace
                        (Code.sqrtStepList
                          ((innerPredecessor + 2) :: rest)) + 1) := by
                simpa [Code.sqrtStepList] using
                  EvaluatorCodeFits.case_succ
                    (zeroBranch := Code.sqrtHitCode)
                    (values := (innerPredecessor + 1) :: rest)
                    (predecessor := innerPredecessor)
                    rfl (sqrtMiss (innerPredecessor :: rest))
              simpa [Code.sqrtStepCode, sqrtStepCost] using
                EvaluatorCodeFits.case_succ
                  (zeroBranch := Code.sqrtZeroCode)
                  (values := (innerPredecessor + 2) :: rest)
                  (predecessor := innerPredecessor + 1)
                  (by simp) inner

def sqrtBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.sqrtStepList
    sqrtStepCost remaining payload

theorem sqrtBody (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.sqrtStepCode)
      (remaining :: payload)
      (flatCountdownOutput Code.sqrtStepList remaining payload)
      (sqrtBodyCost remaining payload) := by
  simpa [sqrtBodyCost] using
    flatCountdownBody sqrtStep remaining payload

def sqrtInputCost (number : Nat) : Nat :=
  let zeroResult := zeroCost [number]
  let firstOne :=
    prependCost [number] [1] [0]
      (oneCost [number]) zeroResult
  let secondOne :=
    prependCost [number] [1] [1, 0]
      (oneCost [number]) firstOne
  prependCost [number] [number] [1, 1, 0]
    (headCost [number]) secondOne

theorem sqrtInput (number : Nat) :
    EvaluatorCodeFits Code.sqrtInputCode [number]
      [number, 1, 1, 0] (sqrtInputCost number) := by
  have firstOne :=
    prepend (one [number]) (zero [number])
  have secondOne :=
    prepend (one [number]) firstOne
  have result :=
    prepend (head [number]) secondOne
  simpa [Code.sqrtInputCode, sqrtInputCost,
    prependCost] using result

def sqrtLoopCost (number : Nat) : Nat :=
  1000000 *
    (encodedListSpace
      [number, 2 * number + 3, 2 * number + 3,
        2 * number + 3] + 1)

theorem sqrtBodyCost_le_loop
    (number remaining : Nat) (payload : List Nat)
    (invariant : Code.SqrtInvariant number remaining payload) :
    sqrtBodyCost remaining payload ≤
      sqrtLoopCost number := by
  obtain ⟨processed, root, sum, lower, upper, rfl⟩ :=
    invariant
  let distance :=
    (root + 1) * (root + 1) - processed
  let gap := 2 * root + 1
  let limit := 2 * number + 3
  have distanceDef :
      distance =
        (root + 1) * (root + 1) - processed := rfl
  have limitDef : limit = 2 * number + 3 := rfl
  have processedBound : processed ≤ number := by omega
  have rootSelf : root ≤ root * root :=
    Nat.le_mul_self root
  have rootBound : root ≤ number :=
    rootSelf.trans (lower.trans processedBound)
  have gapBound : gap ≤ limit := by
    simp [gap, limit]
    omega
  have squareIdentity :
      (root + 1) * (root + 1) =
        root * root + (2 * root + 1) := by
    ring
  have distanceBound : distance ≤ gap := by
    simp only [distance, gap]
    omega
  have distanceLimit : distance ≤ limit :=
    distanceBound.trans gapBound
  have distancePositive : 0 < distance := by
    simp only [distance]
    omega
  have remainingBound : remaining ≤ number := by omega
  have numberLimit : number ≤ limit := by
    simp [limit]
    omega
  have remainingLimit : remaining ≤ limit :=
    remainingBound.trans numberLimit
  have rootLimit : root ≤ limit :=
    rootBound.trans numberLimit
  have gapPlusTwoLimit : gap + 2 ≤ limit := by
    simp [gap, limit]
    omega
  have rootPlusOneLimit : root + 1 ≤ limit := by
    simp [limit]
    omega
  have remainingBits :=
    encodeNat_length_mono remainingLimit
  have remainingSuccessorBits :=
    encodeNat_length_mono
      (show remaining + 1 ≤ limit by omega)
  have distanceBits :=
    encodeNat_length_mono distanceLimit
  have distancePredBits :=
    encodeNat_length_mono
      ((Nat.pred_le distance).trans distanceLimit)
  have distancePredPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le distance.pred).trans
        ((Nat.pred_le distance).trans distanceLimit))
  have gapBits :=
    encodeNat_length_mono gapBound
  have gapPlusTwoBits :=
    encodeNat_length_mono gapPlusTwoLimit
  have gapPlusTwoDirectBits :
      (Computability.encodeNat (gap + 1 + 1)).length =
        (Computability.encodeNat (gap + 2)).length := by
    congr 2
  have rootBits :=
    encodeNat_length_mono rootLimit
  have rootPlusOneBits :=
    encodeNat_length_mono rootPlusOneLimit
  have numberBits :=
    encodeNat_length_mono numberLimit
  have gapPlusOneBits :=
    encodeNat_length_mono
      (show gap + 1 ≤ limit by omega)
  have remainingPlusTwoBits :=
    encodeNat_length_mono
      (show remaining + 2 ≤ limit by omega)
  have limitSuccessorBits :=
    encodeNat_succ_length_le limit
  have limitDirectBits :
      (Computability.encodeNat limit).length =
        (Computability.encodeNat (2 * number + 3)).length := by
    rw [limitDef]
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  change
    sqrtBodyCost remaining [distance, gap, root] ≤
      sqrtLoopCost number
  cases remaining with
  | zero =>
      simp [sqrtBodyCost, flatCountdownBodyCost,
        sqrtLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits]
      omega
  | succ remaining =>
      have remainingCurrentBits :=
        encodeNat_length_mono
          (show remaining ≤ limit by omega)
      cases distanceEq : distance with
      | zero =>
          omega
      | succ predecessor =>
          cases predecessor with
          | zero =>
              simp [sqrtBodyCost, flatCountdownBodyCost,
                flatCountdownSuccBranchCost, sqrtStepCost,
                sqrtHitCost, sqrtLoopCost, prependCost,
                getCost, dropCost, idCost, headCost, nilCost,
                oneCost, zeroCost, zeroPrimeCost, tailCost,
                succCost, addConstCost, Code.sqrtStepList,
                encodedListSpace_cons, encodedListSpace_nil,
                limit, zeroBits, oneBits,
                gapPlusTwoDirectBits] at *
              omega
          | succ innerPredecessor =>
              have innerBits :=
                encodeNat_length_mono
                  (show innerPredecessor ≤ limit by omega)
              have innerPlusOneBits :=
                encodeNat_length_mono
                  (show innerPredecessor + 1 ≤ limit by omega)
              have innerPlusTwoBits :=
                encodeNat_length_mono
                  (show innerPredecessor + 2 ≤ limit by omega)
              have innerPlusTwoDirectBits :
                  (Computability.encodeNat
                    (innerPredecessor + 1 + 1)).length =
                    (Computability.encodeNat
                      (innerPredecessor + 2)).length := by
                congr 2
              simp [sqrtBodyCost, flatCountdownBodyCost,
                flatCountdownSuccBranchCost, sqrtStepCost,
                sqrtMissCost, sqrtLoopCost, prependCost,
                getCost, dropCost, idCost, headCost, nilCost,
                oneCost, zeroCost, zeroPrimeCost, tailCost,
                succCost, Code.sqrtStepList,
                encodedListSpace_cons, encodedListSpace_nil,
                limit, zeroBits, oneBits,
                gapPlusTwoDirectBits,
                innerPlusTwoDirectBits] at *
              omega

def sqrtCost (number : Nat) : Nat :=
  let finalPayload :=
    ((Code.sqrtStepList)^[number]) [1, 1, 0]
  sqrtInputCost number +
    sqrtLoopCost number +
      getCost 2 finalPayload

theorem sqrt (number : Nat) :
    EvaluatorCodeFits Code.sqrtCode [number]
      [Nat.sqrt number] (sqrtCost number) where
  input_space := by
    have inputSpace := (sqrtInput number).input_space
    simp only [sqrtCost]
    omega
  output_space := by
    let finalPayload :=
      ((Code.sqrtStepList)^[number]) [1, 1, 0]
    have finalEq :
        finalPayload =
          [((Nat.sqrt number + 1) *
              (Nat.sqrt number + 1) - number),
            2 * Nat.sqrt number + 1, Nat.sqrt number] := by
      simpa [finalPayload] using
        Code.sqrtStepList_iterate number
    have projected := get 2 finalPayload
    have projectedSpace := projected.output_space
    rw [finalEq] at projectedSpace
    have projectedSpace' :
        encodedListSpace [Nat.sqrt number] ≤
          getCost 2
            [((Nat.sqrt number + 1) *
                (Nat.sqrt number + 1) - number),
              2 * Nat.sqrt number + 1, Nat.sqrt number] := by
      simpa using projectedSpace
    simp only [sqrtCost]
    rw [Code.sqrtStepList_iterate]
    omega
  call continuation bound budget after := by
    let finalPayload :=
      ((Code.sqrtStepList)^[number]) [1, 1, 0]
    have budget' :
        sqrtInputCost number + sqrtLoopCost number +
              getCost 2 finalPayload +
            continuationSpace continuation ≤
          bound := by
      simpa [sqrtCost, finalPayload] using budget
    have finalEq : finalPayload =
        [((Nat.sqrt number + 1) * (Nat.sqrt number + 1) - number),
          2 * Nat.sqrt number + 1, Nat.sqrt number] := by
      exact Code.sqrtStepList_iterate number
    have getCall :
        EvaluatorCallFits (Code.get 2) continuation
          finalPayload bound :=
      (get 2 finalPayload).call continuation bound
        (by omega)
        (by
          rw [finalEq]
          simpa using after)
    let getContinuation :=
      ToPartrec.Cont.comp (Code.get 2) continuation
    have finalInvariant :
        Code.SqrtInvariant number 0 finalPayload := by
      exact Code.sqrtInvariant_iterate number
    have finalPayloadSpace :
        encodedListSpace finalPayload ≤
          sqrtLoopCost number := by
      have bodyOutput :=
        (sqrtBody 0 finalPayload).output_space
      have bodyBound :=
        sqrtBodyCost_le_loop number 0 finalPayload finalInvariant
      simp [flatCountdownOutput, encodedListSpace_cons] at bodyOutput
      omega
    have afterLoop :
        EvaluatorExecutionFits bound
          (.ret getContinuation finalPayload) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact getCall
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.sqrtStepCode)
          getContinuation [number, 1, 1, 0] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := sqrtBodyCost)
          (invariant := Code.SqrtInvariant number)
      · exact sqrtBody
      · exact Code.sqrtInvariant_initial number
      · exact Code.sqrtInvariant_preserved number
      · intro remaining payload invariant
        have bodyCost :=
          sqrtBodyCost_le_loop number remaining payload invariant
        simp only [getContinuation, continuationSpace_comp]
        omega
      · simpa [finalPayload] using afterLoop
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.sqrtStepCode)
        getContinuation
    have initialInvariant :
        Code.SqrtInvariant number number [1, 1, 0] :=
      Code.sqrtInvariant_initial number
    have initialPayloadSpace :
        encodedListSpace [number, 1, 1, 0] ≤
          sqrtLoopCost number := by
      have bodyInput :=
        (sqrtBody number [1, 1, 0]).input_space
      have bodyBound :=
        sqrtBodyCost_le_loop number number
          [1, 1, 0] initialInvariant
      exact bodyInput.trans bodyBound
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [number, 1, 1, 0]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [getContinuation,
          continuationSpace_comp]
        omega
      · exact flatCall
    have inputCall :=
      (sqrtInput number).call loopContinuation bound
        (by
          simp only [loopContinuation, getContinuation,
            continuationSpace_comp]
          omega)
        afterInput
    have loopWithInput := EvaluatorCallFits.comp inputCall
    have whole := EvaluatorCallFits.comp loopWithInput
    simpa [Code.sqrtCode, loopContinuation,
      getContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
