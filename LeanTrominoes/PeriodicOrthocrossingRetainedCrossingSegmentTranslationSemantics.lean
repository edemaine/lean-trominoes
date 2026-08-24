/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership

/-! # Supporting segments under retained-crossing translation -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Translating a crossing record translates its first physical segment by
the same drawing-period vector. -/
theorem CrossingRecord.firstSegment_retainedPeriodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).firstSegment graph =
      (record.firstSegment graph).translate
        ((drawing graph).periodTranslation shift) := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases first.segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases firstTranslate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.firstSegment,
    GridSegment.translate,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]
  constructor <;> constructor <;> ring

/-- Translating a crossing record translates its second physical segment by
the same drawing-period vector. -/
theorem CrossingRecord.secondSegment_retainedPeriodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).secondSegment graph =
      (record.secondSegment graph).translate
        ((drawing graph).periodTranslation shift) := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases second.segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases secondTranslate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.secondSegment,
    GridSegment.translate,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]
  constructor <;> constructor <;> ring

end LeanTrominoes.PeriodicOrthocrossing
