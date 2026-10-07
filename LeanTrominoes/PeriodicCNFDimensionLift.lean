/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceTilingCoRE
import LeanTrominoes.WangPeriodicCNFComputability

/-! # Plane CNF constraints in higher-dimensional lattices

The lifted formula uses the first two coordinates. A plane assignment extends
constantly in the extra directions, and any lattice assignment restricts to
the plane with all other coordinates zero. Manhattan locality is preserved.
-/

namespace LeanTrominoes.PeriodicCNFDimensions

abbrev Lattice (d : Nat) := Fin d → Int
abbrev Formula (d : Nat) := PeriodicConstraints.Formula (Lattice d)

/-- Manhattan distance, computed one coordinate at a time. -/
def distance : (d : Nat) → Lattice d → Lattice d → Nat
  | 0, _, _ => 0
  | d + 1, a, b => (a 0 - b 0).natAbs +
      distance d (fun i => a i.succ) (fun i => b i.succ)

theorem distance_self (d : Nat) (a : Lattice d) : distance d a a = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [distance, ih]

/-- Locality bounds pairwise offset differences, allowing common shifts. -/
def IsLocal {d : Nat} (f : Formula d) : Prop :=
  ∀ clause ∈ f, ∀ first ∈ clause, ∀ second ∈ clause,
    distance d first.1.2 second.1.2 ≤ 1

instance {d : Nat} (f : Formula d) : Decidable (IsLocal f) := by
  unfold IsLocal
  infer_instance

def planeEmbed (d : Nat) (c : Cell) : Lattice d :=
  fun i => if i.val = 0 then c.1 else if i.val = 1 then c.2 else 0

def planeProject {d : Nat} (dimension : 2 ≤ d) (z : Lattice d) : Cell :=
  (z ⟨0, by omega⟩, z ⟨1, by omega⟩)

theorem planeEmbed_add (d : Nat) (a b : Cell) :
    planeEmbed d (Cell.add a b) = planeEmbed d a + planeEmbed d b := by
  funext i
  simp only [planeEmbed, Cell.add, Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem planeProject_embed {d : Nat} (dimension : 2 ≤ d) (c : Cell) :
    planeProject dimension (planeEmbed d c) = c := by
  simp [planeProject, planeEmbed]

theorem planeProject_add {d : Nat} (dimension : 2 ≤ d) (a b : Lattice d) :
    planeProject dimension (a + b) =
      Cell.add (planeProject dimension a) (planeProject dimension b) := rfl

theorem distance_planeEmbed {d : Nat} (dimension : 2 ≤ d) (a b : Cell) :
    distance d (planeEmbed d a) (planeEmbed d b) =
      (a.1 - b.1).natAbs + (a.2 - b.2).natAbs := by
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => omega
    | succ d =>
      have tail (c : Cell) :
          (fun i : Fin d => planeEmbed (d + 2) c i.succ.succ) = 0 := by
        funext i
        simp [planeEmbed]
      change (a.1 - b.1).natAbs +
        ((a.2 - b.2).natAbs + distance d
          (fun i => planeEmbed (d + 2) a i.succ.succ)
          (fun i => planeEmbed (d + 2) b i.succ.succ)) = _
      rw [tail, tail, distance_self]
      omega

def liftLiteral {V : Type} [Encodable V] (d : Nat) (l : PeriodicLiteral V) :
    PeriodicConstraints.Literal (Lattice d) :=
  ((Encodable.encode l.atom, planeEmbed d l.offset), l.value)

def liftPlane {V : Type} [Encodable V] (d : Nat) (f : PeriodicCNF V) : Formula d :=
  f.clauses.map fun clause => clause.map (liftLiteral d)

/-- Satisfiability is unchanged by adding unused coordinates. -/
theorem liftPlane_satisfiable_iff {V : Type} [Encodable V] {d : Nat}
    (dimension : 2 ≤ d) (f : PeriodicCNF V) :
    PeriodicConstraints.Satisfiable (Lattice d) (liftPlane d f) ↔ f.Satisfiable := by
  constructor
  · rintro ⟨b, satisfied⟩
    refine ⟨fun v c => b (Encodable.encode v) (planeEmbed d c), ?_⟩
    intro c clause member
    obtain ⟨l, hl, value⟩ := satisfied (planeEmbed d c)
      (clause.map (liftLiteral d)) (List.mem_map.mpr ⟨clause, member, rfl⟩)
    obtain ⟨literal, hLiteral, rfl⟩ := List.mem_map.mp hl
    refine ⟨literal, hLiteral, ?_⟩
    change b (Encodable.encode literal.atom)
      (planeEmbed d (Cell.add c literal.offset)) = literal.value
    rw [planeEmbed_add]
    exact value
  · rintro ⟨a, satisfied⟩
    let b : Nat → Lattice d → Bool := fun n z =>
      ((Encodable.decode n : Option V).map
        (fun v => a v (planeProject dimension z))).getD false
    refine ⟨b, ?_⟩
    intro z clause member
    obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp member
    obtain ⟨literal, hLiteral, value⟩ := satisfied (planeProject dimension z) original hOriginal
    refine ⟨liftLiteral d literal, List.mem_map.mpr ⟨literal, hLiteral, rfl⟩, ?_⟩
    change b (Encodable.encode literal.atom)
      (z + planeEmbed d literal.offset) = literal.value
    simpa [b, planeProject_add, PeriodicLiteral.Holds] using value

theorem liftPlane_local_iff {V : Type} [Encodable V] {d : Nat}
    (dimension : 2 ≤ d) (f : PeriodicCNF V) :
    IsLocal (liftPlane d f) ↔ f.IsLocal := by
  simp only [IsLocal, liftPlane, List.forall_mem_map, liftLiteral,
    distance_planeEmbed dimension, PeriodicCNF.IsLocal,
    PeriodicClause.IsLocal, PeriodicClause.offsetDistance]

end LeanTrominoes.PeriodicCNFDimensions
