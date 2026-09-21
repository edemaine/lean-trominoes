/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATFormulaQueries
import LeanTrominoes.PeriodicDrawingArithmeticGeometry
import LeanTrominoes.BoundedArithmeticSignedResidue

/-! # The native route-endpoint verifier

The query counts clause, literal, and representative addresses to recover
incidence indices, traverses the lossless route trailer, and compares signed
endpoints. Semantic identification with `RoutesMatch` is proved separately.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open RouteInput PeriodicCNF.IncidenceFields

private def arithmetic (expr : Expr) (h : expr.noPower=true := by decide) := NativeScalar.arithmetic expr h

def subtract (a b : Signed) : Signed := ⟨a.positive+b.negative,a.negative+b.positive⟩

theorem subtract_eval (a b : Signed) (v : List Nat) :
    (subtract a b).eval v = a.eval v-b.eval v := by
  simp [subtract,Signed.eval,eval_add]; ring

def pointAt (address : Expr) : Point := (fromCode (.load address),fromCode (.load (address+1)))

def offset (depth : Nat) (literal header : Expr) : Point :=
  (subtract (fromCode (formulaField depth (literal+1))) (fromCode (formulaField depth (header+2))),
    subtract (fromCode (formulaField depth (literal+2))) (fromCode (formulaField depth (header+3))))

def endpointExpr (depth : Nat) (route source target header literal : Expr) : Expr :=
  let size := .load route
  let first := pointAt (route+1)
  let last := pointAt (route+1+2*(size-1))
  let sourcePoint := PeriodicGridDrawing.Arithmetic.vertex (depth+6) source
  let targetPoint := PeriodicGridDrawing.Arithmetic.vertex (depth+6) target
  andE (ltE 0 size) (andE (pointEqual first sourcePoint)
    (pointEqual last (pointAdd targetPoint (pointScale (var (depth+6)) (offset depth literal header)))))

-- Context: cursor, target rank, representative, edge rank, literal index,
-- clause index, clause header, variable count, then the shared environment.
def endpoint : NativeScalar.Program := arithmetic
  (endpointExpr 8 (var 0+1) (var 7+var 5) (var 1) (var 6) (var 6+1+4*var 4))

def routeStart (depth : Nat) : Expr :=
  .literal (depth+11)+6*var (depth+8)+2*var (depth+9)

def cursorQuery : NativeScalar.Program := NativeScalar.cursor
  (arithmetic (var 2)) (arithmetic (routeStart 7))

def targetBody : NativeScalar.Program := NativeScalar.bind cursorQuery endpoint

def targetRank : NativeScalar.Program := countQuery 6 (var 0) representativeExpr (by decide) (by decide)

def representativeGuard : Expr := andE (formulaQuery 5 representativeExpr)
  (eqE (formulaField 6 (var 0)) (formulaField 6 (var 4+1+4*var 2)))

def representativeBody : NativeScalar.Program := NativeScalar.implies (arithmetic representativeGuard)
  (NativeScalar.bind targetRank targetBody)

def representatives : NativeScalar.Program := NativeScalar.all (arithmetic (var 5)) representativeBody

def edgeRank : NativeScalar.Program := countQuery 4 (var 2+1+4*var 0) literalMarkExpr (by decide) (by decide)

def literalBody : NativeScalar.Program := NativeScalar.bind edgeRank representatives

def literals : NativeScalar.Program := NativeScalar.all (arithmetic (formulaField 3 (var 1))) literalBody

def clauseRank : NativeScalar.Program := countQuery 2 (var 0) clauseMarkExpr (by decide) (by decide)

def clauseBody : NativeScalar.Program := NativeScalar.implies (arithmetic (.testBit (var 3) (var 0)))
  (NativeScalar.bind clauseRank literals)

def clauses : NativeScalar.Program := NativeScalar.all (arithmetic (var 1)) clauseBody

def variableCount : NativeScalar.Program := countQuery 0 (var 0) representativeExpr (by decide) (by decide)

def program : NativeScalar.Program := NativeScalar.bind variableCount clauses

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
