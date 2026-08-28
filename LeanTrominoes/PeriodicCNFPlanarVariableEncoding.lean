/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree

/-! # Canonical encodings of routed planar-SAT variables -/

noncomputable section

namespace LeanTrominoes

namespace PeriodicOrthocrossing

namespace IndexedGridSegment

/-- Product representation of an indexed segment. -/
def equivData : IndexedGridSegment ≃ Nat × Nat × GridSegment where
  toFun indexed :=
    (indexed.routeIndex, indexed.segmentIndex, indexed.segment)
  invFun data :=
    { routeIndex := data.1
      segmentIndex := data.2.1
      segment := data.2.2 }
  left_inv indexed := by cases indexed; rfl
  right_inv data := by rcases data with ⟨routeIndex, segmentIndex, segment⟩; rfl

noncomputable instance : Primcodable IndexedGridSegment :=
  Primcodable.ofEquiv (Nat × Nat × GridSegment) equivData

end IndexedGridSegment

namespace CrossingRecord

/-- Product representation of a crossing record. -/
def equivData : CrossingRecord ≃
    IndexedGridSegment × Cell × IndexedGridSegment × Cell × Cell where
  toFun record :=
    (record.first, record.firstTranslate, record.second,
      record.secondTranslate, record.point)
  invFun data :=
    { first := data.1
      firstTranslate := data.2.1
      second := data.2.2.1
      secondTranslate := data.2.2.2.1
      point := data.2.2.2.2 }
  left_inv record := by cases record; rfl
  right_inv data := by
    rcases data with ⟨first, firstTranslate, second, secondTranslate, point⟩
    rfl

noncomputable instance : Primcodable CrossingRecord :=
  Primcodable.ofEquiv
    (IndexedGridSegment × Cell × IndexedGridSegment × Cell × Cell)
    equivData

end CrossingRecord

deriving instance Fintype for CrossingSide

namespace CrossingSide

noncomputable instance : Primcodable CrossingSide :=
  Primcodable.ofEquiv (Fin (Fintype.card CrossingSide))
    (Fintype.equivFin CrossingSide)

end CrossingSide

namespace CrossingBoundary

/-- Product representation of a crossing boundary. -/
def equivData : CrossingBoundary ≃ CrossingRecord × CrossingSide where
  toFun boundary := (boundary.crossing, boundary.side)
  invFun data := ⟨data.1, data.2⟩
  left_inv boundary := by cases boundary; rfl
  right_inv _ := rfl

noncomputable instance : Primcodable CrossingBoundary :=
  Primcodable.ofEquiv (CrossingRecord × CrossingSide) equivData

end CrossingBoundary

deriving instance Fintype for SegmentEnd

namespace SegmentEnd

noncomputable instance : Primcodable SegmentEnd :=
  Primcodable.ofEquiv (Fin (Fintype.card SegmentEnd))
    (Fintype.equivFin SegmentEnd)

end SegmentEnd

end PeriodicOrthocrossing

namespace PlanarThreeSAT

namespace CrossoverInternal

noncomputable instance : Primcodable CrossoverInternal :=
  Primcodable.ofEquiv (Fin (Fintype.card CrossoverInternal))
    (Fintype.equivFin CrossoverInternal)

end CrossoverInternal

end PlanarThreeSAT

namespace PeriodicOrthocrossing

namespace PeriodicPlanarSATVariable

/-- Sum-of-products representation of a routed planar-SAT variable. -/
def equivData {Variable : Type*} :
    PeriodicPlanarSATVariable Variable ≃ (
      (IndexedGridSegment × SegmentEnd) ⊕
        CrossingBoundary ⊕ Variable ⊕
          (CrossingRecord × PlanarThreeSAT.CrossoverInternal)) where
  toFun input :=
    match input with
    | .terminal indexed endpoint => .inl (indexed, endpoint)
    | .boundary boundaryValue => .inr (.inl boundaryValue)
    | .atom atomValue => .inr (.inr (.inl atomValue))
    | .crossoverInternal internalData => .inr (.inr (.inr internalData))
  invFun data :=
    match data with
    | .inl terminalData => .terminal terminalData.1 terminalData.2
    | .inr (.inl boundaryValue) => .boundary boundaryValue
    | .inr (.inr (.inl atomValue)) => .atom atomValue
    | .inr (.inr (.inr internalData)) => .crossoverInternal internalData
  left_inv input := by cases input <;> rfl
  right_inv data := by
    cases data with
    | inl terminalData => rfl
    | inr rest =>
        cases rest with
        | inl boundaryValue => rfl
        | inr rest =>
            cases rest with
            | inl atomValue => rfl
            | inr internalData => rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PeriodicPlanarSATVariable Variable) :=
  Primcodable.ofEquiv
    ((IndexedGridSegment × SegmentEnd) ⊕
      CrossingBoundary ⊕ Variable ⊕
        (CrossingRecord × PlanarThreeSAT.CrossoverInternal))
    equivData

end PeriodicPlanarSATVariable

namespace WrappedPeriodicVariable

/-- The wrapper is equivalent to its stored original value. -/
def equivOriginal {Original : Type*} :
    WrappedPeriodicVariable Original ≃ Original where
  toFun wrapped := wrapped.original
  invFun original := ⟨original⟩
  left_inv wrapped := by cases wrapped; rfl
  right_inv _ := rfl

noncomputable instance {Original : Type*} [Primcodable Original] :
    Primcodable (WrappedPeriodicVariable Original) :=
  Primcodable.ofEquiv Original equivOriginal

end WrappedPeriodicVariable

end PeriodicOrthocrossing

end LeanTrominoes

end
