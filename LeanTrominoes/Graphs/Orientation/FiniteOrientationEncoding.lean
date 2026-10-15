/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseAssignmentTokens
import LeanTrominoes.Tiling.Completion.CompletionSparseDrawing
import LeanTrominoes.Tiling.Tromino.Finite.FiniteGadgetSubstitution
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseExpandedMotif

/-! # Finite normalized orientation drawings in sparse unary coordinates

The input records specify a finite drawing, with implicit blank space outside
its support. The input type requires a well-formed, separated, blank-bordered
realization. Its dimensions are immaterial: every realization has the same
finite gadget region and therefore the same orientation semantics.
-/
noncomputable section
namespace LeanTrominoes.Gadget.FiniteOrientation
open _root_.Computability GadgetSparseAssignmentTokens CompletionPattern.Runtime
open PeriodicOrthogonalDrawing

abbrev Records := List ((Nat × Nat) × OrthogonalCellType)

def entries (records : Records) : List DrawingEntry :=
  records.map fun a => (((a.1.1 : Int),(a.1.2 : Int)),a.2)

def Valid (records : Records) : Prop :=
  ((entries records).map Prod.fst).Nodup ∧
    ∃ d : PeriodicOrthogonalDrawing,
      d.IsWellFormed ∧ d.VerticesSeparated ∧ d.BlankBoundary ∧ SparseModel d (entries records)

/-- A valid finite normalized drawing, encoded by its explicit sparse cells. -/
abbrev Input := { records : Records // Valid records }

def Problem (input : Input) : Prop :=
  ∃ d : PeriodicOrthogonalDrawing,
    d.IsWellFormed ∧ d.VerticesSeparated ∧ d.BlankBoundary ∧
      SparseModel d (entries input.1) ∧ d.HasOrientation

def readAux : Phase → Nat → Nat → List Token → Option Records
  | .horizontal,0,_,[] => some []
  | _,_,_,[] => none
  | .horizontal,x,_,.coordinateUnit::rest => readAux .horizontal (x+1) 0 rest
  | .horizontal,x,_,.fieldEnd::rest => readAux .vertical x 0 rest
  | .horizontal,_,_,.cellType _::_ => none
  | .vertical,x,y,.coordinateUnit::rest => readAux .vertical x (y+1) rest
  | .vertical,_,_,.fieldEnd::_ => none
  | .vertical,x,y,.cellType k::rest =>
      (readAux .horizontal 0 0 rest).map (((x,y),k) :: ·)

private theorem readAux_horizontal (initial count : Nat) (rest : List Token) :
    readAux .horizontal initial 0 (List.replicate count .coordinateUnit ++ rest) =
      readAux .horizontal (initial+count) 0 rest := by
  induction count generalizing initial with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ,List.cons_append]
      simp only [readAux]
      rw [ih]
      congr 1; omega

private theorem readAux_vertical (x initial count : Nat) (rest : List Token) :
    readAux .vertical x initial (List.replicate count .coordinateUnit ++ rest) =
      readAux .vertical x (initial+count) rest := by
  induction count generalizing initial with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ,List.cons_append]
      simp only [readAux]
      rw [ih]
      congr 1; omega

private theorem readAux_record (a : (Nat × Nat) × OrthogonalCellType) (rest : List Token) :
    readAux .horizontal 0 0
      (assignmentTokens (((a.1.1 : Int),(a.1.2 : Int)),a.2) ++ rest) =
        (readAux .horizontal 0 0 rest).map (a :: ·) := by
  simp only [assignmentTokens,Int.toNat_natCast,List.append_assoc,List.cons_append]
  rw [readAux_horizontal]
  simp only [Nat.zero_add,readAux]
  rw [readAux_vertical]
  simp [readAux]

@[simp] theorem readAux_encode (records : Records) :
    readAux .horizontal 0 0 (assignmentsTokens (entries records)) = some records := by
  induction records with
  | nil => rfl
  | cons a records ih =>
      change readAux .horizontal 0 0
        (assignmentTokens (((a.1.1 : Int),(a.1.2 : Int)),a.2) ++
          assignmentsTokens (entries records)) = _
      rw [readAux_record,ih]
      rfl

def decode (tokens : List Token) : Option Input := by
  classical
  exact do
    let records ← readAux .horizontal 0 0 tokens
    if h : Valid records then some ⟨records,h⟩ else none

def finEncoding : FiniteEncoding Input where
  Γ := Token
  ΓFin := inferInstance
  encoding := {
    encode input := assignmentsTokens (entries input.1)
    decode := decode
    decode_encode input := by
      simp [decode,input.2] }

def region (input : Input) : List Cell := sparseExpandedMotif .I (entries input.1)

theorem nonnegative (input : Input) (a : DrawingEntry) (ha : a ∈ entries input.1) :
    0 ≤ a.1.1 ∧ 0 ≤ a.1.2 := by
  obtain ⟨record,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩

theorem model_motif (records : Records) (d : PeriodicOrthogonalDrawing)
    (nodup : ((entries records).map Prod.fst).Nodup) (model : SparseModel d (entries records)) :
    (sparseExpandedMotif .I (entries records)).toFinset = (d.expandedMotif .I).toFinset := by
  ext cell
  simp only [List.mem_toFinset]
  rw [← d.computableExpandedMotif_eq .I]
  apply mem_sparseExpandedMotif_iff .I d (entries records) nodup model.bounds
  intro x y hx hy
  have xBound : (x : Int) < d.horizontalPeriod := by exact_mod_cast hx
  have yBound : (y : Int) < d.verticalPeriod := by exact_mod_cast hy
  have lookup := model.lookup ((x : Int),(y : Int))
    ⟨Int.natCast_nonneg _,xBound,Int.natCast_nonneg _,yBound⟩
  have positionEq : d.positionAt ((x : Int),(y : Int)) = (⟨x,hx⟩,⟨y,hy⟩) := by
    apply Prod.ext
    · apply Fin.ext
      change ((x : Int) % (d.horizontalPeriod : Int)).toNat = x
      rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) xBound,Int.toNat_natCast]
    · apply Fin.ext
      change ((y : Int) % (d.verticalPeriod : Int)).toNat = y
      rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) yBound,Int.toNat_natCast]
  rw [d.indexedCellType_eq_get ⟨x,hx⟩ ⟨y,hy⟩]
  convert lookup using 1
  · simp only [getAt,positionEq]

theorem problem_iff (input : Input) :
    Problem input ↔ Tromino.I.Tileable ((region input).toFinset : Set Cell) := by
  obtain ⟨nodup,d,wf,separated,boundary,model⟩ := input.2
  have motif := model_motif input.1 d nodup model
  constructor
  · rintro ⟨other,otherWf,otherSeparated,otherBoundary,otherModel,oriented⟩
    have otherMotif := model_motif input.1 other nodup otherModel
    have tiled := (finiteSubstitution_correct .I other otherWf otherSeparated otherBoundary).mp oriented
    simpa only [region,otherMotif] using tiled
  · intro tiled
    refine ⟨d,wf,separated,boundary,model,?_⟩
    apply (finiteSubstitution_correct .I d wf separated boundary).mpr
    simpa only [region,motif] using tiled

end LeanTrominoes.Gadget.FiniteOrientation
