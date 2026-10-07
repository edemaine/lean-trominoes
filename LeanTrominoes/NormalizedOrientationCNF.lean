/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationCNFLocal

/-! # A finite periodic CNF presentation of normalized drawing orientations -/
namespace LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
open PeriodicOrthogonalDrawing

def positions (d : Drawing) : List Cell :=
  (List.range d.horizontalPeriod).flatMap fun (x : Nat) =>
    (List.range d.verticalPeriod).map fun (y : Nat) => ((x : Int),(y : Int))

theorem address_mem_positions (d : Drawing) (location : Cell) :
    (((address d location).1 : Int),((address d location).2 : Int)) ∈ positions d :=
  List.mem_flatMap.mpr ⟨(address d location).1,
    List.mem_range.mpr (d.positionAt location).1.isLt,
    List.mem_map.mpr ⟨(address d location).2,
      List.mem_range.mpr (d.positionAt location).2.isLt,rfl⟩⟩

def clausesAt (d : Drawing) (location : Cell) : List (PeriodicClause Variable) :=
  localClauses d location (d.getAt location) ++ sides.flatMap (neighborClauses d location)

theorem clausesAt_correct (d : Drawing) (a : Variable → Cell → Bool) (location translate : Cell) :
    (∀ clause ∈ clausesAt d location, clause.Holds a translate) ↔
      satisfiesOrientation (d.getAt (lift d location translate))
        (orientation d a (lift d location translate)) ∧
      ∀ side, ((d.getAt (lift d location translate)).portColor side).isSome →
        orientation d a (lift d location translate) side =
          !(orientation d a (latticeNeighbor (lift d location translate) side) side.opposite) := by
  simp only [clausesAt,List.forall_mem_append,localClauses_correct,List.forall_mem_flatMap,
    neighborClauses_correct,getAt_lift]
  constructor
  · rintro ⟨localRule,neighbors⟩
    exact ⟨localRule,fun side => neighbors side (mem_sides side)⟩
  · rintro ⟨localRule,neighbors⟩
    exact ⟨localRule,fun side _ => neighbors side⟩

def formula (d : Drawing) : PeriodicCNF Variable := ⟨(positions d).flatMap (clausesAt d)⟩

theorem satisfies_iff (d : Drawing) (a : Variable → Cell → Bool) :
    (formula d).Satisfies a ↔ d.IsOrientation (orientation d a) := by
  constructor
  · intro satisfies
    have atLocation (location : Cell) :
        satisfiesOrientation (d.getAt location) (orientation d a location) ∧
          ∀ side, ((d.getAt location).portColor side).isSome →
            orientation d a location side =
              !(orientation d a (latticeNeighbor location side) side.opposite) := by
      have valid := (clausesAt_correct d a
        (((address d location).1 : Int),((address d location).2 : Int)) (quotient d location)).1
        (fun clause member => satisfies (quotient d location) clause
          (List.mem_flatMap.mpr ⟨_,address_mem_positions d location,member⟩))
      simpa only [location_decomposition] using valid
    exact ⟨fun location => (atLocation location).1,fun location => (atLocation location).2⟩
  · rintro ⟨localRule,neighbors⟩ translate clause member
    obtain ⟨location,_,clauseMember⟩ := List.mem_flatMap.mp member
    exact (clausesAt_correct d a location translate).2
      ⟨localRule _,neighbors _⟩ clause clauseMember

theorem assignment_satisfies_iff (d : Drawing) (o : d.Orientation) :
    (formula d).Satisfies (assignment d o) ↔ d.IsOrientation o := by
  rw [satisfies_iff,orientation_assignment]

theorem satisfiable_iff (d : Drawing) :
    (formula d).Satisfiable ↔ ∃ o, d.IsOrientation o := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨orientation d a,(satisfies_iff d a).1 ha⟩
  · rintro ⟨o,ho⟩
    exact ⟨assignment d o,(assignment_satisfies_iff d o).2 ho⟩

abbrev PhysicalSeed := List ((Cell × Side) × Bool)

def Prescribed (d : Drawing) (seed : PhysicalSeed) : Prop :=
  ∃ o : d.Orientation, d.IsOrientation o ∧ ∀ pin ∈ seed, o pin.1.1 pin.1.2 = pin.2

def seed (d : Drawing) (prescriptions : PhysicalSeed) : PeriodicCNF.Seed Variable :=
  prescriptions.map fun pin => (((address d pin.1.1,pin.1.2),quotient d pin.1.1),pin.2)

theorem seeded_iff (d : Drawing) (prescriptions : PhysicalSeed) :
    (formula d).Seeded (seed d prescriptions) ↔ Prescribed d prescriptions := by
  constructor
  · rintro ⟨a,ha,pins⟩
    refine ⟨orientation d a,(satisfies_iff d a).1 ha,?_⟩
    intro pin member
    exact pins _ (List.mem_map.mpr ⟨pin,member,rfl⟩)
  · rintro ⟨o,ho,pins⟩
    refine ⟨assignment d o,(assignment_satisfies_iff d o).2 ho,?_⟩
    intro pin member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    change orientation d (assignment d o) original.1.1 original.1.2 = original.2
    rw [orientation_assignment]
    exact pins original originalMember

open Lean Elab Command in
run_cmd do
  for name in [``satisfies_iff,``seeded_iff] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
