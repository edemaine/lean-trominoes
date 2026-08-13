import LeanTrominoes.PartrecFlatPackedNormalizationLoop

/-!
# Complete five-column packed normalization on flat fields
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

private theorem boolAnd_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftEval : leftCode.eval values = pure [left.toNat])
    (rightEval : rightCode.eval values = pure [right.toNat]) :
    (boolAnd leftCode rightCode).eval values =
      pure [(left && right).toNat] := by
  have combined := boolAnd_eval_at leftCode rightCode values
    left.toNat right.toNat leftEval rightEval
  cases left <;> cases right <;> simpa using combined

/-- Fixed conjunction of the five flat normalization passes. -/
def flatPackedNormalizationAllCode : Code :=
  boolAnd (flatPackedNormalizationColumnCode (0 : WindowColumn)) <|
    boolAnd (flatPackedNormalizationColumnCode (1 : WindowColumn)) <|
      boolAnd (flatPackedNormalizationColumnCode (2 : WindowColumn)) <|
        boolAnd (flatPackedNormalizationColumnCode (3 : WindowColumn))
          (flatPackedNormalizationColumnCode (4 : WindowColumn))

@[simp]
theorem flatPackedNormalizationAllCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationAllCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(current.isNormalizedBool periodicStrip).toNat] := by
  let values := flatPackedTransitionContext periodicStrip current next
  have column0 := flatPackedNormalizationColumnCode_eval
    (0 : WindowColumn) periodicStrip current next
  have column1 := flatPackedNormalizationColumnCode_eval
    (1 : WindowColumn) periodicStrip current next
  have column2 := flatPackedNormalizationColumnCode_eval
    (2 : WindowColumn) periodicStrip current next
  have column3 := flatPackedNormalizationColumnCode_eval
    (3 : WindowColumn) periodicStrip current next
  have column4 := flatPackedNormalizationColumnCode_eval
    (4 : WindowColumn) periodicStrip current next
  have lastTwo := boolAnd_eval_at_bool
    (flatPackedNormalizationColumnCode (3 : WindowColumn))
    (flatPackedNormalizationColumnCode (4 : WindowColumn))
    values
    (current.normalizedColumnBool periodicStrip (3 : WindowColumn))
    (current.normalizedColumnBool periodicStrip (4 : WindowColumn))
    column3 column4
  have lastThree := boolAnd_eval_at_bool
    (flatPackedNormalizationColumnCode (2 : WindowColumn))
    (boolAnd
      (flatPackedNormalizationColumnCode (3 : WindowColumn))
      (flatPackedNormalizationColumnCode (4 : WindowColumn)))
    values
    (current.normalizedColumnBool periodicStrip (2 : WindowColumn))
    (current.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
      current.normalizedColumnBool periodicStrip (4 : WindowColumn))
    column2 lastTwo
  have lastFour := boolAnd_eval_at_bool
    (flatPackedNormalizationColumnCode (1 : WindowColumn))
    (boolAnd
      (flatPackedNormalizationColumnCode (2 : WindowColumn))
      (boolAnd
        (flatPackedNormalizationColumnCode (3 : WindowColumn))
        (flatPackedNormalizationColumnCode (4 : WindowColumn))))
    values
    (current.normalizedColumnBool periodicStrip (1 : WindowColumn))
    (current.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
      (current.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        current.normalizedColumnBool periodicStrip (4 : WindowColumn)))
    column1 lastThree
  have all := boolAnd_eval_at_bool
    (flatPackedNormalizationColumnCode (0 : WindowColumn))
    (boolAnd
      (flatPackedNormalizationColumnCode (1 : WindowColumn))
      (boolAnd
        (flatPackedNormalizationColumnCode (2 : WindowColumn))
        (boolAnd
          (flatPackedNormalizationColumnCode (3 : WindowColumn))
          (flatPackedNormalizationColumnCode (4 : WindowColumn)))))
    values
    (current.normalizedColumnBool periodicStrip (0 : WindowColumn))
    (current.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
      (current.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (current.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          current.normalizedColumnBool periodicStrip (4 : WindowColumn))))
    column0 lastFour
  have columns :
      (List.finRange 5 : List (Fin 5)) = [0, 1, 2, 3, 4] := by
    native_decide
  rw [PackedWindowState.isNormalizedBool, columns]
  simpa [flatPackedNormalizationAllCode, values] using all

end Turing.ToPartrec.Code
