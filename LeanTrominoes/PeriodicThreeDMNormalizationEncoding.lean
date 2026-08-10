import LeanTrominoes.PeriodicGridDrawingComputability
import LeanTrominoes.PeriodicThreeDMNormalizationRasterization

/-!
# Computability encodings for periodic 3DM normalization

The normalized-drawing compiler uses only finite data: a natural-number 3DM
instance and its finite periodic grid drawing.  Building on the shared graph
and drawing encodings, this file gives the compiler-specific incidence,
contracted-edge, endpoint, and direction types canonical encodings.  Later
compiler proofs can therefore ignore the geometric proof fields of
`PlanarPresentation`.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

namespace Incidence

/-- Product representation of one colored-element incidence. -/
def equivData : Incidence ≃ Nat × Cell where
  toFun incidence := (incidence.tripleIndex, incidence.offset)
  invFun data := ⟨data.1, data.2⟩
  left_inv incidence := by cases incidence; rfl
  right_inv data := by rcases data with ⟨index, offset⟩; rfl

noncomputable instance : Primcodable Incidence :=
  Primcodable.ofEquiv (Nat × Cell) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem tripleIndex_primrec : Primrec Incidence.tripleIndex :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem offset_primrec : Primrec Incidence.offset :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

end Incidence

namespace IncidenceTag

/-- Product representation of an incidence's triple index and color. -/
def equivData : IncidenceTag ≃ Nat × WireColor where
  toFun tag := (tag.tripleIndex, tag.color)
  invFun data := ⟨data.1, data.2⟩
  left_inv tag := by cases tag; rfl
  right_inv data := by rcases data with ⟨index, color⟩; rfl

noncomputable instance : Primcodable IncidenceTag :=
  Primcodable.ofEquiv (Nat × WireColor) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem tripleIndex_primrec : Primrec IncidenceTag.tripleIndex :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem color_primrec : Primrec IncidenceTag.color :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

end IncidenceTag

namespace ContractedEdge

/-- Sum-of-products representation of retained and through edges. -/
def equivData : ContractedEdge ≃
    (WireColor × Nat × Incidence) ⊕
      (WireColor × Nat × Incidence × Incidence) where
  toFun
    | .retained color atom incidence => .inl (color, atom, incidence)
    | .through color atom first second =>
        .inr (color, atom, first, second)
  invFun
    | .inl data => .retained data.1 data.2.1 data.2.2
    | .inr data =>
        .through data.1 data.2.1 data.2.2.1 data.2.2.2
  left_inv edge := by cases edge <;> rfl
  right_inv data := by
    rcases data with ⟨color, atom, incidence⟩ |
      ⟨color, atom, first, second⟩ <;> rfl

noncomputable instance : Primcodable ContractedEdge :=
  Primcodable.ofEquiv
    ((WireColor × Nat × Incidence) ⊕
      (WireColor × Nat × Incidence × Incidence))
    equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

end ContractedEdge

namespace ContractedEndpoint

/-- Sum representation distinguishing the two ends of a contracted edge. -/
def equivData : ContractedEndpoint ≃ ContractedEdge ⊕ ContractedEdge where
  toFun
    | .source edge => .inl edge
    | .target edge => .inr edge
  invFun
    | .inl edge => .source edge
    | .inr edge => .target edge
  left_inv endpoint := by cases endpoint <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance : Primcodable ContractedEndpoint :=
  Primcodable.ofEquiv (ContractedEdge ⊕ ContractedEdge) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

end ContractedEndpoint

end PeriodicThreeDM

namespace AxisDirection

noncomputable instance : Primcodable AxisDirection :=
  Primcodable.ofEquiv (Fin (Fintype.card AxisDirection))
    (Fintype.equivFin AxisDirection)

end AxisDirection

namespace DegreeThreeVertexNormalization

noncomputable instance : Primcodable VertexSide :=
  Primcodable.ofEquiv (Fin (Fintype.card VertexSide))
    (Fintype.equivFin VertexSide)

noncomputable instance : Primcodable CanonicalVertexPort :=
  Primcodable.ofEquiv (Fin (Fintype.card CanonicalVertexPort))
    (Fintype.equivFin CanonicalVertexPort)

noncomputable instance : Primcodable PortRotationCount :=
  Primcodable.ofEquiv (Fin (Fintype.card PortRotationCount))
    (Fintype.equivFin PortRotationCount)

end DegreeThreeVertexNormalization

end LeanTrominoes
