/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionSparseDrawing
import LeanTrominoes.UnaryPointLookupCompiler
import LeanTrominoes.UnaryColumnModuloCompiler

/-! # Polynomial-time cell-kind queries in a sparse completion source -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn Gadget Gadget.PeriodicOrthogonalDrawing LBricks
set_option maxHeartbeats 2000000
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {qx qy : List Symbol → Index → Nat}
  {drawing : List Symbol → PeriodicOrthogonalDrawing} {entries : List Symbol → List DrawingEntry}

def sparseQueryCompiler (cx : Compiler rows qx) (cy : Compiler rows qy)
    (ex : Compiler entries (fun _ a => a.1.1.toNat))
    (ey : Compiler entries (fun _ a => a.1.2.toNat))
    (ev : Compiler entries (fun _ a => (kindIndex (kindOf a.2)).val))
    (cw : ScalarCompiler (fun s => (drawing s).horizontalPeriod))
    (model : ∀ s, SparseModel (drawing s) (entries s))
    (queryBound : ∀ s i, i ∈ rows s → qx s i < (drawing s).horizontalPeriod) :
    Compiler rows (fun s i => (kindIndex (stripKinds (drawing s) ((qx s i:Int),(qy s i:Int)))).val) := by
  let queryKeys := add cx (multiplyScalar cy cw)
  let entryKeys := add ex (multiplyScalar (add ey (constant ey 1)) cw)
  let datum := fun s key => (kindIndex (stripKinds (drawing s)
    (((key%(drawing s).horizontalPeriod:Nat):Int),((key/(drawing s).horizontalPeriod:Nat):Int)))).val
  have positive s : 0 < (drawing s).horizontalPeriod := by simp [horizontalPeriod]
  have result := keyedSupported queryKeys entryKeys ev datum (by
    intro s a ha
    have bounds := (model s).bounds a ha
    have bx : a.1.1.toNat < (drawing s).horizontalPeriod := by omega
    have dec := UnaryPointLookup.decode_key _ a.1.1.toNat (a.1.2.toNat+1) (positive s) bx
    have dx := congrArg Prod.fst dec
    have dy := congrArg Prod.snd dec
    dsimp only at dx dy
    simp only [datum,dx,dy]
    exact (model s).natEntry_correct a ha) (by
    intro s i hi missing
    have dec := UnaryPointLookup.decode_key _ (qx s i) (qy s i) (positive s) (queryBound s i hi)
    have dx := congrArg Prod.fst dec
    have dy := congrArg Prod.snd dec
    dsimp only at dx dy
    simp only [datum,dx,dy]
    apply (model s).natEntry_support _ _ (queryBound s i hi)
    rintro ⟨a,ha,eq⟩
    apply missing
    refine ⟨a,ha,?_⟩
    have ax := congrArg Prod.fst eq
    have ay := congrArg Prod.snd eq
    change a.1.1.toNat+(a.1.2.toNat+1)*(drawing s).horizontalPeriod = _
    simp only [natEntry] at ax ay
    rw [ax,ay])
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i hi
  have dec := UnaryPointLookup.decode_key _ (qx s i) (qy s i) (positive s) (queryBound s i hi)
  have dx := congrArg Prod.fst dec
  have dy := congrArg Prod.snd dec
  dsimp only at dx dy
  simp only [datum,dx,dy]

theorem stripKinds_mod_horizontal (d : PeriodicOrthogonalDrawing) (x y : Nat) :
    stripKinds d (((x%d.horizontalPeriod:Nat):Int),(y:Int)) = stripKinds d ((x:Int),(y:Int)) := by
  simp [stripKinds,Circuit.cutKinds,drawingKinds,getAt,positionAt,PeriodicOrthogonalDrawing.residue,horizontalPeriod]

def wrappedSparseQueryCompiler {bound : List Symbol → Nat}
    (cx : Compiler rows qx) (cy : Compiler rows qy)
    (ex : Compiler entries (fun _ a => a.1.1.toNat))
    (ey : Compiler entries (fun _ a => a.1.2.toNat))
    (ev : Compiler entries (fun _ a => (kindIndex (kindOf a.2)).val))
    (cw : ScalarCompiler (fun s => (drawing s).horizontalPeriod)) (cb : ScalarCompiler bound)
    (model : ∀ s, SparseModel (drawing s) (entries s))
    (bounded : ∀ s i, i ∈ rows s → qx s i < bound s) :
    Compiler rows (fun s i => (kindIndex (stripKinds (drawing s) ((qx s i:Int),(qy s i:Int)))).val) := by
  have positive s : 0 < (drawing s).horizontalPeriod := by simp [horizontalPeriod]
  let normalized := boundedMod cx cw cb positive bounded
  let result := sparseQueryCompiler normalized cy ex ey ev cw model
    (fun s i _ => Nat.mod_lt _ (positive s))
  exact TM2ComputableInPolyTime.of_eq result
    (fun s => by simp only [stripKinds_mod_horizontal])
end LeanTrominoes.CompletionPattern.Runtime
