/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnLookupSupport

/-! # Polynomial-time sparse lookup by two unary coordinates -/
noncomputable section
namespace LeanTrominoes.UnaryPointLookup
open Computability Turing UnaryColumn

def pointValue (entries : List ((Nat×Nat)×Nat)) (p : Nat×Nat) : Nat := (entries.lookup p).getD 0

private theorem lookup_member {entries : List ((Nat×Nat)×Nat)} {e : (Nat×Nat)×Nat}
    (member : e ∈ entries) (unique : (entries.map Prod.fst).Nodup) : entries.lookup e.1 = some e.2 := by
  induction entries with
  | nil => simp at member
  | cons a entries ih =>
    obtain ⟨key,value⟩ := a
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp member with eq | member
    · subst e
      simp
    · have different : e.1 ≠ key := by
        intro eq
        exact unique.1 (List.mem_map.mpr ⟨e,member,eq⟩)
      simp only [List.lookup_cons,beq_eq_false_iff_ne.mpr different,ih member unique.2]

theorem decode_key (width x y : Nat) (positive : 0 < width) (hx : x < width) :
    ((x+y*width)%width,(x+y*width)/width) = (x,y) := by
  apply Prod.ext
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hx]
  · dsimp only
    rw [Nat.mul_comm y width,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt hx,Nat.zero_add]

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {qx qy : List Symbol → Index → Nat}
  {entries : List Symbol → List ((Nat×Nat)×Nat)} {width : List Symbol → Nat}

def computableInPolyTime (cx : Compiler rows qx) (cy : Compiler rows qy)
    (ex : Compiler entries (fun _ e => e.1.1)) (ey : Compiler entries (fun _ e => e.1.2))
    (ev : Compiler entries (fun _ e => e.2)) (cw : ScalarCompiler width)
    (positive : ∀ s, 0 < width s)
    (queryBound : ∀ s i, i ∈ rows s → qx s i < width s)
    (entryBound : ∀ s e, e ∈ entries s → e.1.1 < width s)
    (unique : ∀ s, ((entries s).map Prod.fst).Nodup) :
    Compiler rows (fun s i => pointValue (entries s) (qx s i,qy s i)) := by
  let queryKeys := add cx (multiplyScalar cy cw)
  let entryKeys := add ex (multiplyScalar ey cw)
  let datum := fun s key => pointValue (entries s) (key%width s,key/width s)
  have result := keyedSupported queryKeys entryKeys ev datum (by
    intro s e he
    dsimp [datum]
    rw [decode_key _ _ _ (positive s) (entryBound s e he)]
    exact (show pointValue (entries s) e.1 = e.2 by
      simp [pointValue,lookup_member he (unique s)]).symm) (by
    intro s i hi absent
    dsimp [datum]
    rw [decode_key _ _ _ (positive s) (queryBound s i hi)]
    have missing : (entries s).lookup (qx s i,qy s i) = none := by
      rw [List.lookup_eq_none_iff]
      intro e he
      rw [bne_iff_ne]
      intro eq
      apply absent
      refine ⟨e,he,?_⟩
      rw [← eq]
    simp [pointValue,missing])
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i hi
  dsimp [datum]
  rw [decode_key _ _ _ (positive s) (queryBound s i hi)]
end LeanTrominoes.UnaryPointLookup
