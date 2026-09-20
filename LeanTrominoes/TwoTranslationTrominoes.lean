/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TranslationTiling
import LeanTrominoes.Theorem52Proof

/-! # Corollary 5.3: translations of the two oriented I trominoes -/
namespace LeanTrominoes.TwoTranslationTrominoes

def tiles (vertical : Bool) : Polyomino :=
  if vertical then Tromino.I.cells.image SquareSymmetry.rotate90.act else Tromino.I.cells

def vertical : SquareSymmetry → Bool
  | .rotate90 | .rotate270 | .reflectDiagonal | .reflectAntidiagonal => true
  | _ => false

def correction : SquareSymmetry → Cell
  | .rotate180 | .reflectY => (-2,0)
  | .rotate270 | .reflectAntidiagonal => (0,-2)
  | _ => (0,0)

theorem orbit (s : SquareSymmetry) :
    (tiles (vertical s)).image (Cell.add (correction s)) = Tromino.I.cells.image s.act := by
  cases s <;> decide

def normalize (p : Placement Unit) : Placement Bool :=
  ⟨vertical p.symmetry,.identity,Cell.add p.offset (correction p.symmetry)⟩

theorem normalize_cells (p : Placement Unit) :
    (normalize p).cells tiles = p.cells (fun _ => Tromino.I.cells) := by
  have h := congrArg (Finset.image (Cell.add p.offset)) (orbit p.symmetry)
  simpa [normalize,Placement.cells,Finset.image_image,SquareSymmetry.act,
    Cell.add,Int.add_assoc,Function.comp_def] using h

def forget (p : Placement Bool) : Placement Unit :=
  ⟨(),if p.kind then .rotate90 else .identity,p.offset⟩

theorem forget_cells (p : Placement Bool) (legal : p.symmetry = .identity) :
    (forget p).cells (fun _ => Tromino.I.cells) = p.cells tiles := by
  cases p with
  | mk kind symmetry offset =>
    change symmetry = .identity at legal
    subst symmetry
    cases kind <;> simp [forget,tiles,Placement.cells,Finset.image_image,
      SquareSymmetry.act,Function.comp_def]

theorem translationTileable_iff (region : Set Cell) :
    TranslationTileable tiles region ↔ Tromino.I.Tileable region := by
  constructor
  · rintro ⟨ps,h,legal⟩
    exact ⟨forget '' ps,h.map_cells forget (fun p hp => forget_cells p (legal p hp))⟩
  · rintro ⟨ps,h⟩
    exact ⟨normalize '' ps,h.map_cells normalize (fun p _ => normalize_cells p),
      by rintro _ ⟨p,_,rfl⟩; rfl⟩

def planeProblem (input : PeriodicRegion) : Prop :=
  input.IsFullRank ∧ TranslationTileable tiles input.carrier

def stripProblem (input : PeriodicStrip) : Prop :=
  input.IsWellFormed ∧ TranslationTileable tiles input.carrier

theorem plane_eq : planeProblem = PeriodicTrominoTiling .I := by
  funext input; apply propext; exact and_congr_right fun _ => translationTileable_iff _
theorem strip_eq : stripProblem = PeriodicStripTrominoTiling .I := by
  funext input; apply propext; exact and_congr_right fun _ => translationTileable_iff _

/-- The plane assertion, with translations only. -/
theorem planeProved : LeanWang.CoREComplete planeProblem := by
  rw [plane_eq]; exact Theorem52.proved.1 .I

/-- The strip assertion under the existing flat strip encoding. -/
theorem stripProved : Complexity.PSPACEComplete PeriodicStripFlatEncoding.finEncoding stripProblem := by
  rw [strip_eq]; exact Theorem52.stripProved .I

/-- Both parts of Corollary 5.3. -/
theorem proved : LeanWang.CoREComplete planeProblem ∧
    Complexity.PSPACEComplete PeriodicStripFlatEncoding.finEncoding stripProblem :=
  ⟨planeProved,stripProved⟩
end LeanTrominoes.TwoTranslationTrominoes
