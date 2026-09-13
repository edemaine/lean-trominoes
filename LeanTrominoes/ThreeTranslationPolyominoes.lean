/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TranslationTiling
import LeanTrominoes.Theorem55StripEncoding

/-! # Three polyominoes placed by translation only -/

namespace LeanTrominoes.ThreeTranslationPolyominoes

/-- Two fixed axis orientations of the connected 15-omino. -/
def fixed (vertical : Bool) : Polyomino :=
  if vertical then PlusRefinement.bumpy.image SquareSymmetry.rotate90.act else PlusRefinement.bumpy

/-- `none` is the input tile; `some false` and `some true` are the fixed tiles. -/
def tiles (q : Polyomino) : Option Bool → Polyomino
  | none => q
  | some vertical => fixed vertical

def planeProblem (input : List Cell) : Prop :=
  input.toFinset.Nonempty ∧ ¬ Polyomino.IsConnected input.toFinset ∧
    TranslationTileable (tiles input.toFinset) Set.univ

def stripProblem (input : Theorem55.StripInput) : Prop :=
  0 < input.1 ∧ input.2.toFinset.Nonempty ∧ ¬ Polyomino.IsConnected input.2.toFinset ∧
    TranslationTileable (tiles input.2.toFinset) (horizontalStrip input.1)

/-- Intermediate two-kind presentation: P may rotate; Q may only translate. -/
def Allowed (p : Placement Bool) : Prop := p.kind = true → p.symmetry = .identity

def vertical : SquareSymmetry → Bool
  | .rotate90 | .rotate270 | .reflectDiagonal | .reflectAntidiagonal => true
  | _ => false

def correction : SquareSymmetry → Cell
  | .rotate180 | .reflectY => (-6,0)
  | .rotate270 | .reflectAntidiagonal => (0,-6)
  | _ => (0,0)

theorem fixed_orbit (s : SquareSymmetry) :
    (fixed (vertical s)).image (Cell.add (correction s)) = PlusRefinement.bumpy.image s.act := by
  cases s <;> decide

def normalize (p : Placement Bool) : Placement (Option Bool) :=
  if p.kind then ⟨none,.identity,p.offset⟩
  else ⟨some (vertical p.symmetry),.identity,Cell.add p.offset (correction p.symmetry)⟩

theorem normalize_cells (q : Polyomino) (p : Placement Bool) (legal : Allowed p) :
    (normalize p).cells (tiles q) = p.cells (pairTiles PlusRefinement.bumpy q) := by
  cases p with
  | mk kind symmetry offset =>
    cases kind with
    | true =>
      have hs : symmetry = .identity := legal rfl
      subst symmetry
      rfl
    | false =>
      have eq := congrArg (Finset.image (Cell.add offset)) (fixed_orbit symmetry)
      simpa [normalize,Placement.cells,tiles,pairTiles,Finset.image_image,
        SquareSymmetry.act,Cell.add,Int.add_assoc,Function.comp_def] using eq

theorem normalize_legal (p : Placement Bool) : (normalize p).symmetry = .identity := by
  unfold normalize
  split <;> rfl

def forget (p : Placement (Option Bool)) : Placement Bool :=
  match p.kind with
  | none => ⟨true,.identity,p.offset⟩
  | some v => ⟨false,if v then .rotate90 else .identity,p.offset⟩

theorem forget_cells (q : Polyomino) (p : Placement (Option Bool)) (legal : p.symmetry = .identity) :
    (forget p).cells (pairTiles PlusRefinement.bumpy q) = p.cells (tiles q) := by
  cases p with
  | mk kind symmetry offset =>
    change symmetry = .identity at legal
    subst symmetry
    cases kind with
    | none => rfl
    | some v => cases v <;> simp [forget,tiles,fixed,Placement.cells,pairTiles,
        Finset.image_image,SquareSymmetry.act,Cell.add,Function.comp_def]

theorem forget_legal (p : Placement (Option Bool)) : Allowed (forget p) := by
  cases p with
  | mk kind symmetry offset =>
    cases kind with
    | none => simp [Allowed,forget]
    | some v => simp [Allowed,forget]

theorem translationTileable_iff (q : Polyomino) (region : Set Cell) :
    TranslationTileable (tiles q) region ↔
      TileableWith (pairTiles PlusRefinement.bumpy q) region Allowed := by
  constructor
  · intro h
    exact h.map_cells forget (forget_cells q) (fun p _ => forget_legal p)
  · intro h
    exact h.map_cells normalize (normalize_cells q) (fun p _ => normalize_legal p)

end LeanTrominoes.ThreeTranslationPolyominoes
