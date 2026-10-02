/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingAugment

/-! # Interleaved path vertices and projection to protovertices -/
namespace LeanTrominoes.BlockingPath
variable {L R A B : Type*}
def Route.map (f : L → A) (g : R → B) : Route L R → Route A B
  | .last l r => .last (f l) (g r)
  | .cons l r p => .cons (f l) (g r) (p.map f g)

def Route.allVertices : Route L R → List (Sum L R)
  | .last l r => [.inl l,.inr r]
  | .cons l r p => .inl l :: .inr r :: p.allVertices

theorem Route.map_vertices (f : L → A) (g : R → B) (p : Route L R) :
    (p.map f g).vertices=p.vertices.map f := by induction p <;> simp_all [Route.map,Route.vertices]
theorem Route.map_labels (f : L → A) (g : R → B) (p : Route L R) :
    BipartiteMatching.routeLabels (p.map f g)=(BipartiteMatching.routeLabels p).map g := by
  induction p <;> simp_all [Route.map,BipartiteMatching.routeLabels]
theorem Route.map_first (f : L → A) (g : R → B) (p : Route L R) : (p.map f g).first=f p.first := by
  cases p <;> rfl

theorem Route.allVertices_map (f : L → A) (g : R → B) (p : Route L R) :
    (p.map f g).allVertices=p.allVertices.map (Sum.map f g) := by
  induction p <;> simp_all [Route.map,Route.allVertices]
theorem Route.allVertices_length (p : Route L R) : p.allVertices.length=2*p.vertices.length := by
  induction p <;> simp_all [Route.allVertices,Route.vertices] <;> omega

theorem Route.inl_mem (l : L) (p : Route L R) : Sum.inl l ∈ p.allVertices ↔ l ∈ p.vertices := by
  induction p <;> simp_all [Route.allVertices,Route.vertices]
theorem Route.inr_mem (r : R) (p : Route L R) : Sum.inr r ∈ p.allVertices ↔ r ∈ BipartiteMatching.routeLabels p := by
  induction p <;> simp_all [Route.allVertices,BipartiteMatching.routeLabels]

theorem Route.allVertices_nodup (p : Route L R) (left : p.vertices.Nodup)
    (right : (BipartiteMatching.routeLabels p).Nodup) : p.allVertices.Nodup := by
  induction p with
  | last l r => simp [Route.allVertices]
  | cons l r p ih =>
    have ls := List.nodup_cons.mp left
    have rs := List.nodup_cons.mp right
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,ih ls.2 rs.2⟩⟩
    · simpa [Route.allVertices,Route.inl_mem] using ls.1
    · exact fun member => rs.1 ((Route.inr_mem r p).mp member)

end LeanTrominoes.BlockingPath
