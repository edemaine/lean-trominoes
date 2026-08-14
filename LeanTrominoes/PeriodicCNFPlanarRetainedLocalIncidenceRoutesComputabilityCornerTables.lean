/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityGeometry
import LeanTrominoes.PeriodicCNFPlanarRetainedClauseMetadataComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing
import LeanTrominoes.PeriodicThreeDMNormalizationEncoding

/-! # Primitive-recursive retained local gadget route tables -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarThreeSAT

namespace CornerPort

def equivBools : CornerPort ≃ Bool × Bool where
  toFun
    | .west => (false, false)
    | .east => (false, true)
    | .south => (true, false)
    | .north => (true, true)
  invFun
    | (false, false) => .west
    | (false, true) => .east
    | (true, false) => .south
    | (true, true) => .north
  left_inv value := by cases value <;> rfl
  right_inv value := by
    rcases value with ⟨first, second⟩
    cases first <;> cases second <;> rfl

noncomputable instance : Fintype CornerPort :=
  Fintype.ofEquiv (Bool × Bool) equivBools.symm

noncomputable instance : Primcodable CornerPort :=
  Primcodable.ofEquiv (Bool × Bool) equivBools

theorem equivBools_primrec : Primrec equivBools :=
  Primrec.of_equiv

theorem equivBools_symm_primrec : Primrec equivBools.symm :=
  Primrec.of_equiv_symm

end CornerPort

theorem cornerEqualityRouteTable_primrec :
    Primrec₂ cornerEqualityRouteTable :=
  Primrec.dom_finite fun input : CornerPort × CornerPort =>
    cornerEqualityRouteTable input.1 input.2

theorem cornerEqualityRoutes_primrec :
    Primrec fun input : ((CornerPort × CornerPort) × Nat) × Nat =>
      cornerEqualityRoutes input.1.1.1 input.1.1.2
        input.1.2 input.2 := by
  have table : Primrec fun input :
      ((CornerPort × CornerPort) × Nat) × Nat =>
      cornerEqualityRouteTable input.1.1.1 input.1.1.2 :=
    cornerEqualityRouteTable_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have routeIndex : Primrec fun input :
      ((CornerPort × CornerPort) × Nat) × Nat =>
      2 * input.1.2 + input.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact (Primrec.list_getD ([] : List Cell) |>.comp
    table routeIndex).of_eq fun _ => rfl

theorem horizontalEqualityLensRoutes_primrec :
    Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensRoutes input.1.1 input.1.2 input.2 := by
  have clauseZero : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.1.2 = 0 :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const 0)
  have clauseOne : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.1.2 = 1 :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const 1)
  have literalZero : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have literalOne : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.2 = 1 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have upperLeft : Primrec fun _input : (Int × Nat) × Nat =>
      horizontalEqualityLensUpperLeftRoute :=
    Primrec.const horizontalEqualityLensUpperLeftRoute
  have upperRight : Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensUpperRightRoute input.1.1 := by
    change Primrec fun input : (Int × Nat) × Nat =>
      [(3, 0), (3, -2), (input.1.1, -2), (input.1.1, 0)]
    have spanMinusTwo : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (-2 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (-2 : Int))
    have spanZero : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (0 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (0 : Int))
    exact Primrec.list_cons.comp (Primrec.const ((3, 0) : Cell))
      (Primrec.list_cons.comp (Primrec.const ((3, -2) : Cell))
        (Primrec.list_cons.comp spanMinusTwo
          (Primrec.list_cons.comp spanZero (Primrec.const []))))
  have lowerLeft : Primrec fun _input : (Int × Nat) × Nat =>
      horizontalEqualityLensLowerLeftRoute :=
    Primrec.const horizontalEqualityLensLowerLeftRoute
  have lowerRight : Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensLowerRightRoute input.1.1 := by
    change Primrec fun input : (Int × Nat) × Nat =>
      [(6, 0), (input.1.1, 0)]
    have spanZero : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (0 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (0 : Int))
    exact Primrec.list_cons.comp (Primrec.const ((6, 0) : Cell))
      (Primrec.list_cons.comp spanZero (Primrec.const []))
  exact (Primrec.ite clauseZero
    (Primrec.ite literalZero upperLeft
      (Primrec.ite literalOne upperRight (Primrec.const [])))
    (Primrec.ite clauseOne
      (Primrec.ite literalZero lowerLeft
        (Primrec.ite literalOne lowerRight (Primrec.const [])))
      (Primrec.const []))).of_eq fun input => by
        rcases input with ⟨⟨span, clauseIndex⟩, literalIndex⟩
        rcases clauseIndex with _ | clauseIndex
        · rcases literalIndex with _ | literalIndex
          · rfl
          · rcases literalIndex with _ | literalIndex <;> rfl
        · rcases clauseIndex with _ | clauseIndex
          · rcases literalIndex with _ | literalIndex
            · rfl
            · rcases literalIndex with _ | literalIndex <;> rfl
          · rfl

theorem crossoverStraightRoutes_primrec :
    Primrec fun input :
        (PeriodicOrthocrossing.CrossingRecord × Nat) × Nat =>
      crossoverStraightIncidenceDrawing.routes input.1.2 input.2 := by
  have position : Primrec fun input :
      PeriodicOrthocrossing.CrossingRecord × CrossoverVariable =>
      CrossoverVariable.position input.2 :=
    (Primrec.dom_finite CrossoverVariable.position).comp Primrec.snd
  exact (straightIncidenceRoutes_primrec
    (fun _crossing : PeriodicOrthocrossing.CrossingRecord =>
      crossoverFormula)
    (fun _crossing role => CrossoverVariable.position role)
    (Primrec.const crossoverFormula) position).of_eq fun _ => rfl


end PlanarThreeSAT
end LeanTrominoes
