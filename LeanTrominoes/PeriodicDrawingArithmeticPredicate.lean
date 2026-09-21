/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticGeometry

/-! # A bounded-counter program checking periodic drawing planarity -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
set_option maxRecDepth 10000

def routeBody : Expr :=
  orE (sameKey 6 (var 5) (var 4) (var 3) (var 2))
    (notE (andE (interiorContains (translateSegment 6 (var 5) (var 3) (var 2)) (probe 6 (var 1) (var 0)))
      (contains (segment 6 (var 4)) (probe 6 (var 1) (var 0)))))

def routePredicate : Expr :=
  .all (var 2) (.all (var 3) (.all (4*var 3+1) (.all (4*var 4+1)
    (.all (2*var 5+1) (.all (2*var 6+1) routeBody)))))

def vertexBody : Expr := notE
  (interiorContains (translateSegment 4 (var 2) (var 1) (var 0)) (vertex 4 (var 3)))

def vertexPredicate : Expr :=
  .all (var 3) (.all (var 3) (.all (4*var 3+1) (.all (4*var 4+1) vertexBody)))

def continuousBody : Expr :=
  orE (sameKey 4 (var 3) (var 2) (var 1) (var 0))
    (notE (interiorsMeet (translateSegment 4 (var 3) (var 1) (var 0)) (segment 4 (var 2))))

def continuousPredicate : Expr :=
  .all (var 2) (.all (var 3) (.all (4*var 3+1) (.all (4*var 4+1) continuousBody)))

def predicate : Expr := andE routePredicate (andE vertexPredicate continuousPredicate)
def decision : Expr := .ite predicate 1 0

theorem predicate_noPower : predicate.noPower = true := by decide
theorem decision_noPower : decision.noPower = true := by decide

/-- The compiled machine uses linear space in the binary geometry fields. -/
theorem decision_fits (values : List Nat) :
    Turing.PartrecToTM2.EvaluatorCodeFits decision.code values [decision.eval values]
      (decision.weight*(decision.radius+1)*(Turing.PartrecToTM2.encodedListSpace values+1)) :=
  decision.code_fits_automatic values decision_noPower

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
