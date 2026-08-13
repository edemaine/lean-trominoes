/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-!
# Primitive-recursive encodings for orthocrossing carriers

The finite carrier construction uses several geometric sum and record types.
This module gives each one its canonical product encoding and certifies all
constructors and projections needed by the retained-link enumeration.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

namespace SegmentEnd

def equivBool : SegmentEnd ≃ Bool where
  toFun
    | .start => false
    | .finish => true
  invFun
    | false => .start
    | true => .finish
  left_inv endpoint := by cases endpoint <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance : Primcodable SegmentEnd :=
  Primcodable.ofEquiv Bool equivBool

theorem equivBool_primrec : Primrec equivBool :=
  Primrec.of_equiv

theorem equivBool_symm_primrec : Primrec equivBool.symm :=
  Primrec.of_equiv_symm

end SegmentEnd

namespace SegmentTerminal

def equivData : SegmentTerminal ≃
    (IndexedGridSegment × Cell) × SegmentEnd where
  toFun terminal :=
    ((terminal.indexed, terminal.translate), terminal.endpoint)
  invFun data := ⟨data.1.1, data.1.2, data.2⟩
  left_inv terminal := by cases terminal; rfl
  right_inv data := by rcases data with ⟨⟨indexed, translate⟩, endpoint⟩; rfl

noncomputable instance : Primcodable SegmentTerminal :=
  Primcodable.ofEquiv
    ((IndexedGridSegment × Cell) × SegmentEnd) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem indexed_primrec : Primrec SegmentTerminal.indexed :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem translate_primrec : Primrec SegmentTerminal.translate :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem endpoint_primrec : Primrec SegmentTerminal.endpoint :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data :
    (IndexedGridSegment × Cell) × SegmentEnd =>
    SegmentTerminal.mk data.1.1 data.1.2 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end SegmentTerminal

namespace CrossingSide

def equivBools : CrossingSide ≃ Bool × Bool where
  toFun
    | .left => (false, false)
    | .right => (false, true)
    | .top => (true, false)
    | .bottom => (true, true)
  invFun
    | (false, false) => .left
    | (false, true) => .right
    | (true, false) => .top
    | (true, true) => .bottom
  left_inv side := by cases side <;> rfl
  right_inv data := by rcases data with ⟨first, second⟩; cases first <;> cases second <;> rfl

noncomputable instance : Primcodable CrossingSide :=
  Primcodable.ofEquiv (Bool × Bool) equivBools

theorem equivBools_primrec : Primrec equivBools :=
  Primrec.of_equiv

theorem equivBools_symm_primrec : Primrec equivBools.symm :=
  Primrec.of_equiv_symm

end CrossingSide

namespace CrossingBoundary

def equivData : CrossingBoundary ≃ CrossingRecord × CrossingSide where
  toFun boundary := (boundary.crossing, boundary.side)
  invFun data := ⟨data.1, data.2⟩
  left_inv boundary := by cases boundary; rfl
  right_inv data := by cases data; rfl

noncomputable instance : Primcodable CrossingBoundary :=
  Primcodable.ofEquiv (CrossingRecord × CrossingSide) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem crossing_primrec : Primrec CrossingBoundary.crossing :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem side_primrec : Primrec CrossingBoundary.side :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data : CrossingRecord × CrossingSide =>
    CrossingBoundary.mk data.1 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end CrossingBoundary

namespace CarrierNode

def equivData : CarrierNode ≃ CrossingBoundary ⊕ SegmentTerminal where
  toFun
    | CarrierNode.boundary value => Sum.inl value
    | CarrierNode.terminal value => Sum.inr value
  invFun
    | Sum.inl value => CarrierNode.boundary value
    | Sum.inr value => CarrierNode.terminal value
  left_inv node := by cases node <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance : Primcodable CarrierNode :=
  Primcodable.ofEquiv (CrossingBoundary ⊕ SegmentTerminal) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem boundary_primrec : Primrec fun boundary : CrossingBoundary =>
    CarrierNode.boundary boundary := by
  change Primrec fun boundary : CrossingBoundary =>
    equivData.symm (Sum.inl boundary)
  exact equivData_symm_primrec.comp
    (Primrec.sumInl : Primrec fun boundary : CrossingBoundary =>
      (Sum.inl boundary : CrossingBoundary ⊕ SegmentTerminal))

theorem terminal_primrec : Primrec fun terminal : SegmentTerminal =>
    CarrierNode.terminal terminal := by
  change Primrec fun terminal : SegmentTerminal =>
    equivData.symm (Sum.inr terminal)
  exact equivData_symm_primrec.comp
    (Primrec.sumInr : Primrec fun terminal : SegmentTerminal =>
      (Sum.inr terminal : CrossingBoundary ⊕ SegmentTerminal))

end CarrierNode

end PeriodicOrthocrossing

namespace PlanarThreeSAT.EqualityPositions

def equivData : EqualityPositions ≃ Cell × Cell where
  toFun positions := (positions.forward, positions.backward)
  invFun data := ⟨data.1, data.2⟩
  left_inv positions := by cases positions; rfl
  right_inv data := by cases data; rfl

noncomputable instance : Primcodable EqualityPositions :=
  Primcodable.ofEquiv (Cell × Cell) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem forward_primrec : Primrec EqualityPositions.forward :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem backward_primrec : Primrec EqualityPositions.backward :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data : Cell × Cell =>
    EqualityPositions.mk data.1 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end PlanarThreeSAT.EqualityPositions

namespace PlanarThreeSAT.EqualityLink

def equivData {Variable : Type*} : EqualityLink Variable ≃
    (Variable × Variable) × EqualityPositions where
  toFun link := ((link.first, link.second), link.positions)
  invFun data := ⟨data.1.1, data.1.2, data.2⟩
  left_inv link := by cases link; rfl
  right_inv data := by rcases data with ⟨⟨first, second⟩, positions⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (EqualityLink Variable) :=
  Primcodable.ofEquiv
    ((Variable × Variable) × EqualityPositions) equivData

theorem equivData_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem first_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (EqualityLink.first : EqualityLink Variable → Variable) :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem second_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (EqualityLink.second : EqualityLink Variable → Variable) :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem positions_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (EqualityLink.positions :
      EqualityLink Variable → EqualityPositions) :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : (Variable × Variable) × EqualityPositions =>
      EqualityLink.mk data.1.1 data.1.2 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end PlanarThreeSAT.EqualityLink

end LeanTrominoes
