/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitComputability
import LeanTrominoes.PeriodicCNFPlanarVertexGadgetsComputability
import LeanTrominoes.PeriodicGridDrawingGeometryComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-!
# Computability of retained-ray rasterization

The retained planar-SAT construction uses eight compass rays and three
exceptional routed-clause rays.  This module gives their finite direction
types primitive-recursive encodings, proves the exact executable classifiers
primitive recursive, and lifts the two staircase generators through segment
and whole-polyline rasterization.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT
open LeanTrominoes.Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ## Encodings -/

namespace RetainedTerminalDirection

def equivData : RetainedTerminalDirection ≃ Port ⊕ DuplicatorArm where
  toFun
    | .compass port => .inl port
    | .routedClause arm => .inr arm
  invFun
    | .inl port => .compass port
    | .inr arm => .routedClause arm
  left_inv direction := by cases direction <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance : Primcodable RetainedTerminalDirection :=
  Primcodable.ofEquiv (Port ⊕ DuplicatorArm) equivData

deriving instance Fintype for RetainedTerminalDirection

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

end RetainedTerminalDirection

namespace RetainedRay

def equivData : RetainedRay ≃
    (Port × Nat) ⊕ (DuplicatorArm × Nat) where
  toFun
    | .compass port length => .inl (port, length)
    | .routedClause arm length => .inr (arm, length)
  invFun
    | .inl data => .compass data.1 data.2
    | .inr data => .routedClause data.1 data.2
  left_inv ray := by cases ray <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance : Primcodable RetainedRay :=
  Primcodable.ofEquiv
    ((Port × Nat) ⊕ (DuplicatorArm × Nat)) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem compass_primrec :
    Primrec fun input : Port × Nat =>
      RetainedRay.compass input.1 input.2 := by
  exact (equivData_symm_primrec.comp
    (Primrec.sumInl.comp Primrec.id)).of_eq fun _ => rfl

theorem routedClause_primrec :
    Primrec fun input : DuplicatorArm × Nat =>
      RetainedRay.routedClause input.1 input.2 := by
  exact (equivData_symm_primrec.comp
    (Primrec.sumInr.comp Primrec.id)).of_eq fun _ => rfl

end RetainedRay

/-! ## Exact ray classifiers -/

theorem terminalPort_primrec : Primrec terminalPort := by
  let x : Cell → Int := Prod.fst
  let y : Cell → Int := Prod.snd
  have xPrimrec : Primrec x := Primrec.fst
  have yPrimrec : Primrec y := Primrec.snd
  have xNegative : PrimrecPred fun vector : Cell => x vector < 0 :=
    int_lt_primrec.comp xPrimrec (Primrec.const 0)
  have yNegative : PrimrecPred fun vector : Cell => y vector < 0 :=
    int_lt_primrec.comp yPrimrec (Primrec.const 0)
  have xZero : PrimrecPred fun vector : Cell => x vector = 0 :=
    Primrec.eq.comp xPrimrec (Primrec.const 0)
  have yZero : PrimrecPred fun vector : Cell => y vector = 0 :=
    Primrec.eq.comp yPrimrec (Primrec.const 0)
  have yPositive : PrimrecPred fun vector : Cell => 0 < y vector :=
    int_lt_primrec.comp (Primrec.const 0) yPrimrec
  have xEqY : PrimrecPred fun vector : Cell => x vector = y vector :=
    Primrec.eq.comp xPrimrec yPrimrec
  have negX : Primrec fun vector : Cell => -x vector :=
    int_negate_primrec.comp xPrimrec
  have negY : Primrec fun vector : Cell => -y vector :=
    int_negate_primrec.comp yPrimrec
  have yEqNegX : PrimrecPred fun vector : Cell => y vector = -x vector :=
    Primrec.eq.comp yPrimrec negX
  have xEqNegY : PrimrecPred fun vector : Cell => x vector = -y vector :=
    Primrec.eq.comp xPrimrec negY
  exact (Primrec.ite xNegative
      (Primrec.ite yNegative
        (Primrec.ite xEqY
          (Primrec.const (some Port.northwest))
          (Primrec.const none))
        (Primrec.ite yZero
          (Primrec.const (some Port.west))
          (Primrec.ite yEqNegX
            (Primrec.const (some Port.southwest))
            (Primrec.const none))))
      (Primrec.ite xZero
        (Primrec.ite yNegative
          (Primrec.const (some Port.north))
          (Primrec.ite yPositive
            (Primrec.const (some Port.south))
            (Primrec.const none)))
        (Primrec.ite yNegative
          (Primrec.ite xEqNegY
            (Primrec.const (some Port.northeast))
            (Primrec.const none))
          (Primrec.ite yZero
            (Primrec.const (some Port.east))
            (Primrec.ite xEqY
              (Primrec.const (some Port.southeast))
              (Primrec.const none)))))).of_eq fun _ => rfl

theorem compassLength_primrec :
    Primrec fun input : Port × Cell =>
      compassLength input.1 input.2 := by
  let x : Port × Cell → Int := fun input => input.2.1
  let y : Port × Cell → Int := fun input => input.2.2
  have xPrimrec : Primrec x := Primrec.fst.comp Primrec.snd
  have yPrimrec : Primrec y := Primrec.snd.comp Primrec.snd
  have negX : Primrec fun input : Port × Cell => -x input :=
    int_negate_primrec.comp xPrimrec
  have negY : Primrec fun input : Port × Cell => -y input :=
    int_negate_primrec.comp yPrimrec
  have isNorthwest : PrimrecPred fun input : Port × Cell =>
      input.1 = Port.northwest :=
    Primrec.eq.comp Primrec.fst (Primrec.const Port.northwest)
  have isNorth : PrimrecPred fun input : Port × Cell =>
      input.1 = Port.north :=
    Primrec.eq.comp Primrec.fst (Primrec.const Port.north)
  have isSouth : PrimrecPred fun input : Port × Cell =>
      input.1 = Port.south :=
    Primrec.eq.comp Primrec.fst (Primrec.const Port.south)
  have isSouthwest : PrimrecPred fun input : Port × Cell =>
      input.1 = Port.southwest :=
    Primrec.eq.comp Primrec.fst (Primrec.const Port.southwest)
  have isWest : PrimrecPred fun input : Port × Cell =>
      input.1 = Port.west :=
    Primrec.eq.comp Primrec.fst (Primrec.const Port.west)
  let selected : Port × Cell → Int := fun input =>
    match input.1 with
    | .northwest => -input.2.1
    | .north => -input.2.2
    | .northeast | .east | .southeast => input.2.1
    | .south => input.2.2
    | .southwest | .west => -input.2.1
  have selectedPrimrec : Primrec selected :=
    (Primrec.ite isNorthwest negX
      (Primrec.ite isNorth negY
        (Primrec.ite isSouth yPrimrec
          (Primrec.ite (isSouthwest.or isWest) negX xPrimrec)))).of_eq
            fun input => by
              rcases input with ⟨port, vector⟩
              cases port <;> simp [selected, x, y]
  exact (int_toNat_primrec.comp selectedPrimrec).of_eq fun input => by
    rcases input with ⟨port, vector⟩
    cases port <;> simp [selected, compassLength]

theorem routedClauseRayLengthCandidate_primrec :
    Primrec fun input : DuplicatorArm × Cell =>
      routedClauseRayLengthCandidate input.1 input.2 := by
  have magnitude : Primrec fun input : DuplicatorArm × Cell =>
      input.2.1.natAbs :=
    PeriodicThreeDM.NormalizationCompiler.int_natAbs_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have isLeft : PrimrecPred fun input : DuplicatorArm × Cell =>
      input.1 = DuplicatorArm.left :=
    Primrec.eq.comp Primrec.fst (Primrec.const DuplicatorArm.left)
  have isMiddle : PrimrecPred fun input : DuplicatorArm × Cell =>
      input.1 = DuplicatorArm.middle :=
    Primrec.eq.comp Primrec.fst (Primrec.const DuplicatorArm.middle)
  have dividedNine : Primrec fun input : DuplicatorArm × Cell =>
      input.2.1.natAbs / 9 :=
    Primrec.nat_div.comp magnitude (Primrec.const 9)
  have dividedFour : Primrec fun input : DuplicatorArm × Cell =>
      input.2.1.natAbs / 4 :=
    Primrec.nat_div.comp magnitude (Primrec.const 4)
  exact (Primrec.ite isLeft dividedNine
    (Primrec.ite isMiddle dividedFour magnitude)).of_eq fun input => by
      cases input.1 <;> rfl

theorem routedClauseRayPrimitive_primrec :
    Primrec routedClauseRayPrimitive :=
  Primrec.dom_finite _

theorem routedClauseRayMatches_primrec :
    Primrec fun input : DuplicatorArm × Cell =>
      routedClauseRayMatches input.1 input.2 := by
  have length := routedClauseRayLengthCandidate_primrec
  have positive : PrimrecPred fun input : DuplicatorArm × Cell =>
      0 < routedClauseRayLengthCandidate input.1 input.2 :=
    Primrec.nat_lt.comp (Primrec.const 0) length
  have primitive : Primrec fun input : DuplicatorArm × Cell =>
      routedClauseRayPrimitive input.1 :=
    routedClauseRayPrimitive_primrec.comp Primrec.fst
  have scaled : Primrec fun input : DuplicatorArm × Cell =>
      Cell.scale (routedClauseRayLengthCandidate input.1 input.2)
        (routedClauseRayPrimitive input.1) :=
    cell_scale_primrec.comp
      (int_ofNat_primrec.comp length) primitive
  have exactVector : PrimrecPred fun input : DuplicatorArm × Cell =>
      input.2 = Cell.scale
        (routedClauseRayLengthCandidate input.1 input.2)
        (routedClauseRayPrimitive input.1) :=
    Primrec.eq.comp Primrec.snd scaled
  exact (positive.and exactVector).decide.of_eq fun _ => rfl

theorem routedClauseRayClassify_primrec :
    Primrec routedClauseRayClassify := by
  have matchPred (arm : DuplicatorArm) : PrimrecPred fun vector : Cell =>
      0 < routedClauseRayLengthCandidate arm vector ∧
        vector = Cell.scale
          (routedClauseRayLengthCandidate arm vector)
          (routedClauseRayPrimitive arm) :=
    (routedClauseRayMatches_primrec.comp
      (Primrec.pair (Primrec.const arm) Primrec.id)).primrecPred
  have length (arm : DuplicatorArm) : Primrec fun vector : Cell =>
      routedClauseRayLengthCandidate arm vector :=
    routedClauseRayLengthCandidate_primrec.comp
      (Primrec.pair (Primrec.const arm) Primrec.id)
  have answer (arm : DuplicatorArm) : Primrec fun vector : Cell =>
      some (arm, routedClauseRayLengthCandidate arm vector) :=
    Primrec.option_some.comp
      (Primrec.pair (Primrec.const arm) (length arm))
  exact (Primrec.ite (matchPred .left) (answer .left)
    (Primrec.ite (matchPred .middle) (answer .middle)
      (Primrec.ite (matchPred .right) (answer .right)
        (Primrec.const none)))).of_eq fun vector => by
          simp only [routedClauseRayClassify, routedClauseRayMatches,
            decide_eq_true_eq]

theorem retainedRayClassify_primrec :
    Primrec retainedRayClassify := by
  have port := terminalPort_primrec
  have noPort : Primrec fun vector : Cell =>
      match routedClauseRayClassify vector with
      | none => none
      | some data => some (RetainedRay.routedClause data.1 data.2) := by
    have routed := routedClauseRayClassify_primrec
    have none : Primrec fun _vector : Cell =>
        (none : Option RetainedRay) :=
      Primrec.const (none : Option RetainedRay)
    have some : Primrec₂ fun (_vector : Cell)
        (data : DuplicatorArm × Nat) =>
        some (RetainedRay.routedClause data.1 data.2) :=
      (Primrec.option_some.comp₂
        (RetainedRay.routedClause_primrec.comp₂
          Primrec₂.right)).of_eq fun _ _ => rfl
    exact (Primrec.option_casesOn routed none some).of_eq fun vector => by
      cases routedClauseRayClassify vector <;> rfl
  have somePort : Primrec₂ fun (vector : Cell) (port : Port) =>
      some (RetainedRay.compass port (compassLength port vector)) := by
    have length : Primrec fun input : Cell × Port =>
        compassLength input.2 input.1 :=
      compassLength_primrec.comp
        (Primrec.pair Primrec.snd Primrec.fst)
    have ray : Primrec fun input : Cell × Port =>
        RetainedRay.compass input.2
          (compassLength input.2 input.1) :=
      RetainedRay.compass_primrec.comp
        (Primrec.pair Primrec.snd length)
    exact (Primrec.option_some.comp ray).to₂
  exact (Primrec.option_casesOn port noPort somePort).of_eq fun vector => by
    unfold retainedRayClassify
    cases terminalPort vector with
    | some port => rfl
    | none =>
        cases routedClauseRayClassify vector with
        | none => rfl
        | some data => cases data; rfl

theorem oppositePort_primrec : Primrec oppositePort :=
  Primrec.dom_finite _

theorem RetainedRay.terminalDirection_primrec :
    Primrec RetainedRay.terminalDirection := by
  have encoded := RetainedRay.equivData_primrec
  have compass : Primrec₂ fun (_ray : RetainedRay)
      (data : Port × Nat) =>
      RetainedTerminalDirection.compass (oppositePort data.1) := by
    have direction : Primrec fun input : RetainedRay × (Port × Nat) =>
        (Sum.inl (oppositePort input.2.1) : Port ⊕ DuplicatorArm) :=
      Primrec.sumInl.comp
        (oppositePort_primrec.comp
          (Primrec.fst.comp Primrec.snd))
    exact (RetainedTerminalDirection.equivData_symm_primrec.comp
      direction).to₂
  have routed : Primrec₂ fun (_ray : RetainedRay)
      (data : DuplicatorArm × Nat) =>
      RetainedTerminalDirection.routedClause data.1 := by
    have direction : Primrec fun input :
        RetainedRay × (DuplicatorArm × Nat) =>
        (Sum.inr input.2.1 : Port ⊕ DuplicatorArm) :=
      Primrec.sumInr.comp (Primrec.fst.comp Primrec.snd)
    exact (RetainedTerminalDirection.equivData_symm_primrec.comp
      direction).to₂
  exact (Primrec.sumCasesOn encoded compass routed).of_eq fun ray => by
    cases ray <;> rfl

theorem RetainedRay.length_primrec : Primrec RetainedRay.length := by
  have encoded := RetainedRay.equivData_primrec
  have compass : Primrec₂ fun (_ray : RetainedRay)
      (data : Port × Nat) => data.2 :=
    (Primrec.snd.comp Primrec₂.right).to₂
  have routed : Primrec₂ fun (_ray : RetainedRay)
      (data : DuplicatorArm × Nat) => data.2 :=
    (Primrec.snd.comp Primrec₂.right).to₂
  exact (Primrec.sumCasesOn encoded compass routed).of_eq fun ray => by
    cases ray <;> rfl

theorem retainedTerminalDirectionClassify_primrec :
    Primrec retainedTerminalDirectionClassify := by
  have negated : Primrec fun vector : Cell => Cell.sub (0, 0) vector :=
    cell_sub_primrec.comp (Primrec.const (0, 0)) Primrec.id
  have classified := retainedRayClassify_primrec.comp negated
  have selected : Primrec₂ fun (_vector : Cell) (ray : RetainedRay) =>
      (ray.terminalDirection, ray.length) := by
    exact (Primrec.pair
      (RetainedRay.terminalDirection_primrec.comp Primrec₂.right)
      (RetainedRay.length_primrec.comp Primrec₂.right)).to₂
  exact (Primrec.option_map classified selected).of_eq fun vector => by
    rfl

theorem classifiedRetainedTerminalData_primrec :
    Primrec (classifiedRetainedTerminalData :
      Cell → RetainedTerminalData) := by
  have fallback : Primrec fun _vector : Cell =>
      ((RetainedTerminalDirection.compass Port.east, 1) :
        RetainedTerminalData) :=
    Primrec.const
      ((RetainedTerminalDirection.compass Port.east, 1) :
        RetainedTerminalData)
  exact (Primrec.option_getD.comp
    retainedTerminalDirectionClassify_primrec
    fallback).of_eq fun _ => rfl

/-! ## Staircase generators -/

private theorem cell_add_assoc (first second third : Cell) :
    Cell.add (Cell.add first second) third =
      Cell.add first (Cell.add second third) := by
  apply Prod.ext <;> simp [Cell.add] <;> ring

private theorem cell_add_comm (first second : Cell) :
    Cell.add first second = Cell.add second first := by
  apply Prod.ext <;> simp [Cell.add] <;> ring

private theorem diagonalStaircase_translate
    (horizontal vertical : Int) (length : Nat)
    (offset start : Cell) :
    diagonalStaircase horizontal vertical length
        (Cell.add offset start) =
      (diagonalStaircase horizontal vertical length start).map
        (Cell.add offset) := by
  induction length generalizing start with
  | zero => simp [diagonalStaircase, Cell.add]
  | succ length induction =>
      simp only [diagonalStaircase, List.map_cons]
      apply congrArg₂ (fun head tail => head :: tail) rfl
      apply congrArg₂ (fun head tail => head :: tail)
      · exact cell_add_assoc offset start (horizontal, 0)
      · rw [cell_add_assoc]
        exact induction _

theorem diagonalStaircase_primrec :
    Primrec fun input : ((Int × Int) × Nat) × Cell =>
      diagonalStaircase input.1.1.1 input.1.1.2
        input.1.2 input.2 := by
  let Parameters := (Int × Int) × Cell
  have base : Primrec fun parameters : Parameters => [parameters.2] :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  have step : Primrec₂ fun (parameters : Parameters)
      (state : Nat × List Cell) =>
      parameters.2 ::
        Cell.add parameters.2 (parameters.1.1, 0) ::
          state.2.map (Cell.add (parameters.1.1, parameters.1.2)) := by
    have second : Primrec fun input : Parameters × (Nat × List Cell) =>
        Cell.add input.1.2 (input.1.1.1, 0) :=
      cell_add_primrec.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.const 0))
    have shifted : Primrec fun input : Parameters ×
        (Nat × List Cell) =>
        input.2.2.map
          (Cell.add (input.1.1.1, input.1.1.2)) := by
      have shift : Primrec₂ fun
          (input : Parameters × (Nat × List Cell)) (point : Cell) =>
          Cell.add (input.1.1.1, input.1.1.2) point := by
        exact cell_add_primrec.comp₂
          (Primrec.pair
            ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).comp₂
              Primrec₂.left)
            ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).comp₂
              Primrec₂.left))
          Primrec₂.right
      exact Primrec.list_map
        (Primrec.snd.comp Primrec.snd) shift
    exact (Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp second shifted)).to₂
  have recursion := Primrec.nat_rec base step
  have parameters : Primrec fun input : ((Int × Int) × Nat) × Cell =>
      ((input.1.1.1, input.1.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  have computed := recursion.comp parameters (Primrec.snd.comp Primrec.fst)
  exact computed.of_eq fun input => by
    rcases input with ⟨⟨⟨horizontal, vertical⟩, length⟩, start⟩
    induction length generalizing start with
    | zero => rfl
    | succ length induction =>
      simp only [diagonalStaircase]
      rw [induction]
      rw [← diagonalStaircase_translate horizontal vertical length
          (horizontal, vertical) start]
      congr 2
      exact congrArg (diagonalStaircase horizontal vertical length)
        (cell_add_comm (horizontal, vertical) start)

theorem compassRay_primrec :
    Primrec fun input : (Port × Nat) × Cell =>
      compassRay input.1.1 input.1.2 input.2 := by
  let Query := (Port × Nat) × Cell
  have singleton : Primrec fun input : Query => [input.2] :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  have successor : Primrec₂ fun (input : Query) (length : Nat) =>
      compassRay input.1.1 (length + 1) input.2 := by
    have diagonal (horizontal vertical : Int) :
        Primrec fun input : Query × Nat =>
          diagonalStaircase horizontal vertical (input.2 + 1) input.1.2 :=
      diagonalStaircase_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.const horizontal) (Primrec.const vertical))
            (Primrec.succ.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
    have direct : Primrec fun input : Query × Nat =>
        [input.1.2,
          Cell.add input.1.2
            (Cell.scale (input.2 + 1) input.1.1.1.unitVector)] := by
      have unitVector : Primrec fun input : Query × Nat =>
          input.1.1.1.unitVector :=
        (Primrec.dom_finite Port.unitVector).comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      have scaled : Primrec fun input : Query × Nat =>
          Cell.scale (input.2 + 1) input.1.1.1.unitVector :=
        cell_scale_primrec.comp
          (int_ofNat_primrec.comp
            (Primrec.succ.comp Primrec.snd))
          unitVector
      have finish : Primrec fun input : Query × Nat =>
          Cell.add input.1.2
            (Cell.scale (input.2 + 1) input.1.1.1.unitVector) :=
        cell_add_primrec.comp
          (Primrec.snd.comp Primrec.fst) scaled
      exact Primrec.list_cons.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp finish (Primrec.const []))
    have isPort (port : Port) : PrimrecPred fun input : Query × Nat =>
        input.1.1.1 = port :=
      Primrec.eq.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const port)
    have chosen : Primrec fun input : Query × Nat =>
        compassRay input.1.1.1 (input.2 + 1) input.1.2 :=
      (Primrec.ite (isPort .northwest) (diagonal (-1) (-1))
      (Primrec.ite (isPort .northeast) (diagonal 1 (-1))
        (Primrec.ite (isPort .southeast) (diagonal 1 1)
          (Primrec.ite (isPort .southwest) (diagonal (-1) 1)
            direct)))).of_eq fun input => by
              rcases input with ⟨⟨⟨port, originalLength⟩, start⟩, length⟩
              cases port <;> simp [compassRay]
    exact chosen.to₂
  have length : Primrec fun input : Query => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact (Primrec.nat_casesOn length singleton successor).of_eq fun input => by
    rcases input with ⟨⟨port, length⟩, start⟩
    cases length <;> cases port <;> rfl

theorem routedClauseRayBlock_primrec :
    Primrec fun input : DuplicatorArm × Cell =>
      routedClauseRayBlock input.1 input.2 := by
  have offsets : Primrec fun input : DuplicatorArm × Cell =>
      routedClauseRayOffsets input.1 :=
    (Primrec.dom_finite routedClauseRayOffsets).comp Primrec.fst
  have translated : Primrec₂ fun
      (input : DuplicatorArm × Cell) (point : Cell) =>
      Cell.add input.2 point :=
    cell_add_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.list_map offsets translated).of_eq fun _ => rfl

private theorem routedClauseRay_translate
    (arm : DuplicatorArm) (length : Nat)
    (offset start : Cell) :
    routedClauseRay arm length (Cell.add offset start) =
      (routedClauseRay arm length start).map (Cell.add offset) := by
  have blockTranslate (blockStart : Cell) :
      routedClauseRayBlock arm (Cell.add offset blockStart) =
        (routedClauseRayBlock arm blockStart).map (Cell.add offset) := by
    simp only [routedClauseRayBlock, List.map_map]
    apply List.map_congr_left
    intro point _
    exact cell_add_assoc offset blockStart point
  have mapJoin (first second : List Cell) :
      (joinAtEndpoint first second).map (Cell.add offset) =
        joinAtEndpoint (first.map (Cell.add offset))
          (second.map (Cell.add offset)) := by
    simp [joinAtEndpoint]
  induction length generalizing start with
  | zero => simp [routedClauseRay, Cell.add]
  | succ length induction =>
      simp only [routedClauseRay]
      rw [blockTranslate, mapJoin]
      congr 1
      rw [cell_add_assoc]
      exact induction _

theorem routedClauseRay_primrec :
    Primrec fun input : (DuplicatorArm × Nat) × Cell =>
      routedClauseRay input.1.1 input.1.2 input.2 := by
  let Parameters := DuplicatorArm × Cell
  have base : Primrec fun parameters : Parameters => [parameters.2] :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  have step : Primrec₂ fun (parameters : Parameters)
      (state : Nat × List Cell) =>
      joinAtEndpoint
        (routedClauseRayBlock parameters.1 parameters.2)
        (state.2.map
          (Cell.add (routedClauseRayPrimitive parameters.1))) := by
    have block : Primrec fun input : Parameters ×
        (Nat × List Cell) =>
        routedClauseRayBlock input.1.1 input.1.2 :=
      routedClauseRayBlock_primrec.comp Primrec.fst
    have primitive : Primrec fun input : Parameters ×
        (Nat × List Cell) =>
        routedClauseRayPrimitive input.1.1 :=
      routedClauseRayPrimitive_primrec.comp
        (Primrec.fst.comp Primrec.fst)
    have shifted : Primrec fun input : Parameters ×
        (Nat × List Cell) =>
        input.2.2.map
          (Cell.add (routedClauseRayPrimitive input.1.1)) := by
      have shift : Primrec₂ fun
          (input : Parameters × (Nat × List Cell)) (point : Cell) =>
          Cell.add (routedClauseRayPrimitive input.1.1) point :=
        cell_add_primrec.comp₂
          (primitive.comp₂ Primrec₂.left) Primrec₂.right
      exact Primrec.list_map
        (Primrec.snd.comp Primrec.snd) shift
    exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
      block shifted).to₂
  have recursion := Primrec.nat_rec base step
  have parameters : Primrec fun input : (DuplicatorArm × Nat) × Cell =>
      (input.1.1, input.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have computed := recursion.comp parameters (Primrec.snd.comp Primrec.fst)
  exact computed.of_eq fun input => by
    rcases input with ⟨⟨arm, length⟩, start⟩
    induction length generalizing start with
    | zero => rfl
    | succ length induction =>
      simp only [routedClauseRay]
      rw [induction]
      rw [← routedClauseRay_translate arm length
          (routedClauseRayPrimitive arm) start]
      rw [cell_add_comm]

/-! ## Retained rays, segments, and polylines -/

theorem RetainedRay.rasterize_primrec :
    Primrec fun input : RetainedRay × Cell =>
      input.1.rasterize input.2 := by
  have encoded : Primrec fun input : RetainedRay × Cell =>
      RetainedRay.equivData input.1 :=
    RetainedRay.equivData_primrec.comp Primrec.fst
  have compass : Primrec₂ fun (input : RetainedRay × Cell)
      (data : Port × Nat) =>
      compassRay data.1 data.2 input.2 := by
    exact (compassRay_primrec.comp
      (Primrec.pair Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))).to₂
  have routed : Primrec₂ fun (input : RetainedRay × Cell)
      (data : DuplicatorArm × Nat) =>
      routedClauseRay data.1 data.2 input.2 := by
    exact (routedClauseRay_primrec.comp
      (Primrec.pair Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))).to₂
  exact (Primrec.sumCasesOn encoded compass routed).of_eq fun input => by
    cases input.1 <;> rfl

theorem rasterizeRetainedSegment_primrec :
    Primrec rasterizeRetainedSegment := by
  have displacement : Primrec fun segment : GridSegment =>
      Cell.sub segment.finish segment.start :=
    cell_sub_primrec.comp
      GridSegment.finish_primrec GridSegment.start_primrec
  have classified := retainedRayClassify_primrec.comp displacement
  have fallback : Primrec fun segment : GridSegment =>
      [segment.start, segment.finish] :=
    Primrec.list_cons.comp GridSegment.start_primrec
      (Primrec.list_cons.comp GridSegment.finish_primrec
        (Primrec.const []))
  have selected : Primrec₂ fun (segment : GridSegment)
      (ray : RetainedRay) => ray.rasterize segment.start := by
    exact (RetainedRay.rasterize_primrec.comp
      (Primrec.pair Primrec₂.right
        (GridSegment.start_primrec.comp₂ Primrec₂.left))).to₂
  exact (Primrec.option_casesOn classified fallback selected).of_eq
    fun segment => by
      unfold rasterizeRetainedSegment
      cases retainedRayClassify (Cell.sub segment.finish segment.start) <;>
        rfl

theorem rasterizeRetainedPolyline_primrec :
    Primrec rasterizeRetainedPolyline := by
  have step : Primrec₂ fun (_points : List Cell)
      (state : Cell × List Cell × List Cell) =>
      match state.2.1 with
      | [] => [state.1]
      | second :: _rest =>
          joinAtEndpoint
            (rasterizeRetainedSegment
              (GridSegment.mk state.1 second))
            state.2.2 := by
    change Primrec fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
      match combined.2.2.1 with
      | [] => [combined.2.1]
      | second :: _rest =>
          joinAtEndpoint
            (rasterizeRetainedSegment
              (GridSegment.mk combined.2.1 second))
            combined.2.2.2
    have tail : Primrec fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
        combined.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have singleton : Primrec fun combined :
        List Cell × (Cell × List Cell × List Cell) =>
        [combined.2.1] :=
      Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.const [])
    have consCase : Primrec₂ fun
        (combined : List Cell ×
          (Cell × List Cell × List Cell))
        (tailData : Cell × List Cell) =>
        joinAtEndpoint
          (rasterizeRetainedSegment
            (GridSegment.mk combined.2.1 tailData.1))
          combined.2.2.2 := by
      have segment : Primrec fun data :
          (List Cell × (Cell × List Cell × List Cell)) ×
            (Cell × List Cell) =>
          GridSegment.mk data.1.2.1 data.2.1 :=
        GridSegment.mk_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)
      have rasterized : Primrec fun data :
          (List Cell × (Cell × List Cell × List Cell)) ×
            (Cell × List Cell) =>
          rasterizeRetainedSegment
            (GridSegment.mk data.1.2.1 data.2.1) :=
        rasterizeRetainedSegment_primrec.comp segment
      exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
        rasterized
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
            (rasterizeRetainedSegment
              (GridSegment.mk state.1 second))
            state.2.2)
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun points => by
    induction points with
    | nil => rfl
    | cons first rest induction =>
        cases rest with
        | nil => rfl
        | cons second rest =>
            simp [rasterizeRetainedPolyline, induction]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
