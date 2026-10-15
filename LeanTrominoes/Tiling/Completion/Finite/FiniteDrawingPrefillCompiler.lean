/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.Finite.FiniteDrawingPaletteCompiler
import LeanTrominoes.Tiling.Completion.CompletionStripBandFieldsCompiler
import LeanTrominoes.Tiling.Tromino.Finite.FiniteCoordinateColumns

/-! # Exact signed columns of the finite completion preplacements -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
open _root_.Computability Turing UnaryColumn Gadget Gadget.PeriodicOrthogonalDrawing LBricks
set_option maxHeartbeats 3000000
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (drawing : List Symbol → PeriodicOrthogonalDrawing)

private def shiftedPlacement (t : Tromino) (s : List Symbol) (r : MotifRow) : Placement Unit :=
  r.2.2.shift (brickOrigin t ((r.1.1:Int)-radius drawing s,(r.1.2:Int)-radius drawing s))

private theorem selected_shifted (t : Tromino) (s : List Symbol) :
    (selectedRows t (side drawing s) (side drawing s) (palette drawing s)).map
      (shiftedPlacement drawing t s) = finiteDrawingPrefill (drawing s) t := by
  have expand : ∀ (sites : List (Nat×Nat)),
      ((sites.flatMap fun c => (taggedMotifs t).map fun a => (c,a)).filter
        (keepRow (palette drawing s))).map (shiftedPlacement drawing t s)=
      sites.flatMap fun c => (brickMotif t (palette drawing s ((c.1:Int),(c.2:Int)))).map
        (fun p => p.shift (brickOrigin t ((c.1:Int)-radius drawing s,(c.2:Int)-radius drawing s))) := by
    intro sites
    rw [List.filter_flatMap,List.map_flatMap]
    apply congrArg (sites.flatMap)
    funext c
    rw [List.filter_map,List.map_map]
    have eq := congrArg (fun ps : List (Placement Unit) => ps.map fun p =>
      p.shift (brickOrigin t ((c.1:Int)-radius drawing s,(c.2:Int)-radius drawing s)))
      (tagged_filter t (palette drawing s ((c.1:Int),(c.2:Int))))
    simpa only [List.map_map,Function.comp_def,keepRow,shiftedPlacement] using eq
  unfold selectedRows expandedRows
  rw [expand]
  cases t <;> simp [finiteDrawingPrefill,LBricks.FiniteGuards.squarePrefill,
    IBricks.FiniteGuards.squarePrefill,LBricks.FiniteGuards.prefill,IBricks.FiniteGuards.prefill,
    Tromino.FiniteWitness.boxList,gridSites,side,radius,palette,brickMotif,brickOrigin,LBricks.squareOfBrick,IBricks.squareOfBrick,
    List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

variable (entries : List Symbol → List DrawingEntry)
    (cw : ScalarCompiler (fun s => (drawing s).horizontalPeriod))
    (ch : ScalarCompiler (fun s => (drawing s).verticalPeriod))
    (ex : Compiler entries (fun _ a => a.1.1.toNat))
    (ey : Compiler entries (fun _ a => a.1.2.toNat))
    (ev : Compiler entries (fun _ a => (kindIndex (kindOf a.2)).val))
    (model : ∀ s,SparseModel (drawing s) (entries s))

def prefillSymmetryCompiler (t : Tromino) :
    Compiler (fun s => finiteDrawingPrefill (drawing s) t)
      (fun _ p => CompletionStripEncoding.symmetryCode p.symmetry) := by
  let cp := paletteCompiler drawing entries cw ch ex ey ev model
  let result := selectedTableColumn t cp (fun a => CompletionStripEncoding.symmetryCode a.2.symmetry)
  apply result.of_eq
  intro s
  dsimp only
  rw [← selected_shifted drawing t s,List.map_map]
  rfl

private def signedOffsetCompiler (t : Tromino) (horizontal : Bool) :
    Compiler (fun s => finiteDrawingPrefill (drawing s) t)
      (fun _ p => Encodable.encode (if horizontal then p.offset.1 else p.offset.2)) := by
  let cp := paletteCompiler drawing entries cw ch ex ey ev model
  let x := selectedSiteColumn t cp (xCompiler drawing cw ch)
  let y := selectedSiteColumn t cp (yCompiler drawing cw ch)
  let r := broadcast x (radiusCompiler drawing cw ch)
  let coord : Cell → Int := fun c => if horizontal then c.1 else c.2
  let positive := selectedTableColumn t cp (fun a => (coord a.2.offset).toNat)
  let negative := selectedTableColumn t cp (fun a => (-(coord a.2.offset)).toNat)
  let base : Compiler (fun s => selectedRows t (side drawing s) (side drawing s) (palette drawing s))
      (fun _ row => if horizontal then row.1.1*brickWidth t+row.1.2*brickSkew t else row.1.2*brickHeight t) := by
    cases horizontal
    · exact scale y (brickHeight t)
    · exact add (scale x (brickWidth t)) (scale y (brickSkew t))
  let translation := scale r (if horizontal then brickWidth t+brickSkew t else brickHeight t)
  let result := signedDifference (add base positive) (add translation negative)
  apply result.of_eq
  intro s
  dsimp only
  rw [← selected_shifted drawing t s,List.map_map]
  apply List.map_congr_left
  intro row _
  apply congrArg Encodable.encode
  dsimp only [coord,base,translation]
  cases horizontal <;> cases t <;>
    simp [shiftedPlacement,brickOrigin,brickWidth,brickSkew,brickHeight,
      LBricks.origin,IBricks.origin,Placement.shift,Cell.add,Nat.cast_add,Nat.cast_mul] <;> omega

def prefillXCompiler (t : Tromino) : Compiler (fun s => finiteDrawingPrefill (drawing s) t)
    (fun _ p => Encodable.encode p.offset.1) :=
  signedOffsetCompiler drawing entries cw ch ex ey ev model t true

def prefillYCompiler (t : Tromino) : Compiler (fun s => finiteDrawingPrefill (drawing s) t)
    (fun _ p => Encodable.encode p.offset.2) :=
  signedOffsetCompiler drawing entries cw ch ex ey ev model t false
end LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
