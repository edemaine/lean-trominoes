/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData

/-! # Injectivity of carrier rank-datum unary payloads -/

namespace LeanTrominoes.PeriodicOrthocrossing

private def indexedGridSegmentCodeOfScanUnaryFields? :
    List Nat → Option IndexedGridSegmentCode
  | [routeIndex, segmentIndex,
      startHorizontalPositive, startHorizontalNegative,
      startVerticalPositive, startVerticalNegative,
      finishHorizontalPositive, finishHorizontalNegative,
      finishVerticalPositive, finishVerticalNegative] =>
      some
        { routeIndex := routeIndex
          segmentIndex := segmentIndex
          start :=
            (signedOfUnaryFields
                startHorizontalPositive startHorizontalNegative,
              signedOfUnaryFields
                startVerticalPositive startVerticalNegative)
          finish :=
            (signedOfUnaryFields
                finishHorizontalPositive finishHorizontalNegative,
              signedOfUnaryFields
                finishVerticalPositive finishVerticalNegative) }
  | _ => none

private def crossingRecordCodeOfScanUnaryFields? :
    List Nat → Option CrossingRecordCode
  | [firstRouteIndex, firstSegmentIndex,
      firstStartHorizontalPositive, firstStartHorizontalNegative,
      firstStartVerticalPositive, firstStartVerticalNegative,
      firstFinishHorizontalPositive, firstFinishHorizontalNegative,
      firstFinishVerticalPositive, firstFinishVerticalNegative,
      firstTranslateHorizontalPositive, firstTranslateHorizontalNegative,
      firstTranslateVerticalPositive, firstTranslateVerticalNegative,
      secondRouteIndex, secondSegmentIndex,
      secondStartHorizontalPositive, secondStartHorizontalNegative,
      secondStartVerticalPositive, secondStartVerticalNegative,
      secondFinishHorizontalPositive, secondFinishHorizontalNegative,
      secondFinishVerticalPositive, secondFinishVerticalNegative,
      secondTranslateHorizontalPositive, secondTranslateHorizontalNegative,
      secondTranslateVerticalPositive, secondTranslateVerticalNegative,
      pointHorizontalPositive, pointHorizontalNegative,
      pointVerticalPositive, pointVerticalNegative] =>
      some
        { first :=
            { routeIndex := firstRouteIndex
              segmentIndex := firstSegmentIndex
              start :=
                (signedOfUnaryFields
                    firstStartHorizontalPositive
                    firstStartHorizontalNegative,
                  signedOfUnaryFields
                    firstStartVerticalPositive firstStartVerticalNegative)
              finish :=
                (signedOfUnaryFields
                    firstFinishHorizontalPositive
                    firstFinishHorizontalNegative,
                  signedOfUnaryFields
                    firstFinishVerticalPositive firstFinishVerticalNegative) }
          firstTranslate :=
            (signedOfUnaryFields
                firstTranslateHorizontalPositive
                firstTranslateHorizontalNegative,
              signedOfUnaryFields
                firstTranslateVerticalPositive firstTranslateVerticalNegative)
          second :=
            { routeIndex := secondRouteIndex
              segmentIndex := secondSegmentIndex
              start :=
                (signedOfUnaryFields
                    secondStartHorizontalPositive
                    secondStartHorizontalNegative,
                  signedOfUnaryFields
                    secondStartVerticalPositive secondStartVerticalNegative)
              finish :=
                (signedOfUnaryFields
                    secondFinishHorizontalPositive
                    secondFinishHorizontalNegative,
                  signedOfUnaryFields
                    secondFinishVerticalPositive
                    secondFinishVerticalNegative) }
          secondTranslate :=
            (signedOfUnaryFields
                secondTranslateHorizontalPositive
                secondTranslateHorizontalNegative,
              signedOfUnaryFields
                secondTranslateVerticalPositive
                secondTranslateVerticalNegative)
          point :=
            (signedOfUnaryFields
                pointHorizontalPositive pointHorizontalNegative,
              signedOfUnaryFields
                pointVerticalPositive pointVerticalNegative) }
  | _ => none

@[simp] theorem signedOfUnaryFields_magnitudes (value : Int) :
    signedOfUnaryFields value.toNat (-value).toNat = value := by
  cases value with
  | ofNat value => simp [signedOfUnaryFields]
  | negSucc value =>
      simp [signedOfUnaryFields]
      omega

private theorem indexedGridSegmentCodeOfScanUnaryFields?_scan
    (code : IndexedGridSegmentCode) :
    indexedGridSegmentCodeOfScanUnaryFields? code.scanUnaryFields =
      some code := by
  rcases code with
    ⟨routeIndex, segmentIndex,
      ⟨startHorizontal, startVertical⟩,
      ⟨finishHorizontal, finishVertical⟩⟩
  simp [IndexedGridSegmentCode.scanUnaryFields, cellUnaryFields,
    signedUnaryFields, indexedGridSegmentCodeOfScanUnaryFields?]

private theorem crossingRecordCodeOfScanUnaryFields?_scan
    (code : CrossingRecordCode) :
    crossingRecordCodeOfScanUnaryFields? code.scanUnaryFields = some code := by
  rcases code with
    ⟨⟨firstRouteIndex, firstSegmentIndex,
        ⟨firstStartHorizontal, firstStartVertical⟩,
        ⟨firstFinishHorizontal, firstFinishVertical⟩⟩,
      ⟨firstTranslateHorizontal, firstTranslateVertical⟩,
      ⟨secondRouteIndex, secondSegmentIndex,
        ⟨secondStartHorizontal, secondStartVertical⟩,
        ⟨secondFinishHorizontal, secondFinishVertical⟩⟩,
      ⟨secondTranslateHorizontal, secondTranslateVertical⟩,
      ⟨pointHorizontal, pointVertical⟩⟩
  simp [CrossingRecordCode.scanUnaryFields,
    IndexedGridSegmentCode.scanUnaryFields, cellUnaryFields,
    signedUnaryFields, crossingRecordCodeOfScanUnaryFields?]

theorem IndexedGridSegmentCode.scanUnaryFields_injective :
    Function.Injective IndexedGridSegmentCode.scanUnaryFields := by
  intro first second fieldsEq
  have decodedEq := congrArg indexedGridSegmentCodeOfScanUnaryFields? fieldsEq
  simpa [indexedGridSegmentCodeOfScanUnaryFields?_scan] using decodedEq

/-- The thirty-two unary magnitudes retain the complete proof-free crossing
identity. -/
theorem CrossingRecordCode.scanUnaryFields_injective :
    Function.Injective CrossingRecordCode.scanUnaryFields := by
  intro first second fieldsEq
  have decodedEq := congrArg crossingRecordCodeOfScanUnaryFields? fieldsEq
  simpa [crossingRecordCodeOfScanUnaryFields?_scan] using decodedEq

end LeanTrominoes.PeriodicOrthocrossing
