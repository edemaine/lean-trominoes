import LeanTrominoes.PeriodicThreeDMNormalizationFinalRoundComputability

/-!
# Primitive-recursive geometry for periodic 3DM normalization

This module proves computability of the affine magnification, unit segment
subdivision, endpoint trimming, and local-template splicing operations used
by every normalized route round.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem int_natAbs_primrec : Primrec Int.natAbs :=
  (intCodeMagnitude_primrec.comp Primrec.encode).of_eq
    intCodeMagnitude_encode

theorem normalizeVertexPosition_primrec :
    Primrec normalizeVertexPosition := by
  exact (cell_add_primrec.comp
    (cell_scale_primrec.comp
      (Primrec.const vertexNormalizationScale) Primrec.id)
    (Primrec.const center)).of_eq fun _ => rfl

theorem normalizationTemplateAt_primrec :
    Primrec fun input : Cell × List Cell =>
      normalizationTemplateAt input.1 input.2 := by
  have offset : Primrec (fun input : Cell × List Cell =>
      Cell.scale vertexNormalizationScale input.1) :=
    cell_scale_primrec.comp
      (Primrec.const vertexNormalizationScale) Primrec.fst
  exact (translatePolyline_primrec.comp
    (Primrec.pair offset Primrec.snd)).of_eq fun _ => rfl

theorem axisDirection_step_primrec :
    Primrec AxisDirection.step :=
  Primrec.dom_finite _

theorem segmentLength_primrec :
    Primrec fun input : Cell × Cell =>
      AxisDirection.segmentLength input.1 input.2 := by
  have deltaX : Primrec (fun input : Cell × Cell =>
      input.2.1 - input.1.1) :=
    int_subtract_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have deltaY : Primrec (fun input : Cell × Cell =>
      input.2.2 - input.1.2) :=
    int_subtract_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.nat_add.comp
    (int_natAbs_primrec.comp deltaX)
    (int_natAbs_primrec.comp deltaY)).of_eq fun _ => rfl

theorem unitSegmentPoints_primrec :
    Primrec fun input : Cell × Cell =>
      AxisDirection.unitSegmentPoints input.1 input.2 := by
  let Segment := Cell × Cell
  have direction : Primrec (fun input : Segment =>
      AxisDirection.between input.1 input.2) :=
    axisDirection_between_primrec
  have step : Primrec (fun input : Segment =>
      (AxisDirection.between input.1 input.2).step) :=
    axisDirection_step_primrec.comp direction
  have indices : Primrec (fun input : Segment =>
      List.range (AxisDirection.segmentLength input.1 input.2 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp segmentLength_primrec)
  have point : Primrec₂ fun (input : Segment) (index : Nat) =>
      Cell.add input.1
        (Cell.scale (index : Int)
          (AxisDirection.between input.1 input.2).step) := by
    have scaled : Primrec (fun combined : Segment × Nat =>
        Cell.scale (combined.2 : Int)
          (AxisDirection.between combined.1.1 combined.1.2).step) :=
      cell_scale_primrec.comp
        (int_ofNat_primrec.comp Primrec.snd)
        (step.comp Primrec.fst)
    exact (cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst) scaled).to₂
  exact (Primrec.list_map indices point).of_eq fun _ => rfl

theorem joinAtEndpoint_primrec {alpha : Type*} [Primcodable alpha] :
    Primrec₂ (joinAtEndpoint : List alpha → List alpha → List alpha) := by
  exact (Primrec.list_append.comp Primrec.fst
    (Primrec.list_tail.comp Primrec.snd)).to₂

theorem unitSubdividePolyline_primrec :
    Primrec AxisDirection.unitSubdividePolyline := by
  have step : Primrec₂ fun (_points : List Cell)
      (state : Cell × List Cell × List Cell) =>
      match state.2.1 with
      | [] => [state.1]
      | second :: _rest =>
          joinAtEndpoint
            (AxisDirection.unitSegmentPoints state.1 second)
            state.2.2 := by
    change Primrec fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
      match combined.2.2.1 with
      | [] => [combined.2.1]
      | second :: _rest =>
          joinAtEndpoint
            (AxisDirection.unitSegmentPoints combined.2.1 second)
            combined.2.2.2
    have tail : Primrec (fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
        combined.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have singleton : Primrec (fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
        [combined.2.1]) :=
      Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.const [])
    have consCase : Primrec₂ fun
        (combined : List Cell ×
          (Cell × List Cell × List Cell))
        (tailData : Cell × List Cell) =>
        joinAtEndpoint
          (AxisDirection.unitSegmentPoints combined.2.1 tailData.1)
          combined.2.2.2 := by
      have segment : Primrec (fun data :
          (List Cell × (Cell × List Cell × List Cell)) ×
            (Cell × List Cell) =>
          AxisDirection.unitSegmentPoints data.1.2.1 data.2.1) :=
        unitSegmentPoints_primrec.comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
      exact (joinAtEndpoint_primrec.comp segment
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.fst)))).to₂
    exact (Primrec.list_casesOn tail singleton consCase).of_eq
      fun combined => by cases combined.2.2.1 <;> rfl
  have recursion := Primrec.list_rec
    (f := fun points : List Cell => points)
    (g := fun _ => ([] : List Cell))
    (h := fun _ state =>
      match state.2.1 with
      | [] => [state.1]
      | second :: _rest =>
          joinAtEndpoint
            (AxisDirection.unitSegmentPoints state.1 second)
            state.2.2)
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun points => by
    induction points with
    | nil => simp
    | cons first rest induction =>
        cases rest with
        | nil => simp
        | cons second rest =>
            simp [AxisDirection.unitSubdividePolyline, induction]

theorem magnifiedUnitRoute_primrec :
    Primrec magnifiedUnitRoute := by
  have magnified : Primrec fun points : List Cell =>
      points.map normalizeVertexPosition :=
    Primrec.list_map Primrec.id
      (normalizeVertexPosition_primrec.comp Primrec.snd).to₂
  exact (unitSubdividePolyline_primrec.comp magnified).of_eq
    fun _ => rfl

theorem trimmedMagnifiedRoute_primrec :
    Primrec trimmedMagnifiedRoute := by
  have magnified := magnifiedUnitRoute_primrec
  have dropped : Primrec fun points : List Cell =>
      (magnifiedUnitRoute points).drop 3 :=
    Primrec.list_drop.comp (Primrec.const 3) magnified
  have retainedLength : Primrec fun points : List Cell =>
      (magnifiedUnitRoute points).length - 6 :=
    Primrec.nat_sub.comp
      (Primrec.list_length.comp magnified) (Primrec.const 6)
  exact (Primrec.list_take.comp retainedLength dropped).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
