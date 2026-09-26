/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionRouteFieldsCompiler
import LeanTrominoes.DelimitedDirectionSegmentFieldsCompiler

/-! # Route serialization from a uniform signed-coordinate compiler family -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Turing UnaryColumn
variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  (rows : List Symbol → List Row) (directions : List Symbol → Row → List AxisDirection)
  (start : List Symbol → Row → Cell)
  (routes : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))
  (coordinates : ∀ horizontal positive, Compiler rows (fun s r =>
    SignedUnaryCoordinateRefinement.field positive (component horizontal (start s r))))

def signedRouteFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (rows s).flatMap (fun r => PeriodicGridDrawing.Arithmetic.routeFields
      (Gadget.rebuildRoute (start s r) (directions s r)))) :=
  routeFieldsCompiler rows directions start routes
    (coordinates true true) (coordinates true false) (coordinates false true) (coordinates false false)

def signedSegmentFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => segmentTableFields ((rows s).map (fun r => Gadget.rebuildRoute (start s r) (directions s r)))) :=
  segmentFieldsCompiler rows directions start routes
    (coordinates true true) (coordinates true false) (coordinates false true) (coordinates false false)

end LeanTrominoes.DelimitedDirectionDisplacement
end
