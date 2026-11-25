import Mathlib.Data.Set.Basic

namespace PEqualNP.Research.BipartiteBoundaryRows

variable {L R : Type}
def left (edge : L → R → Prop) (t : Set R) : Set L :=
  {i | ∀ j ∈ t, ¬ edge i j}
def right (edge : L → R → Prop) (s : Set L) : Set R :=
  {j | ∀ i ∈ s, ¬ edge i j}

theorem boundary (edge : L → R → Prop) (f : Set L → Set R → Prop)
    (mono : ∀ a b c d, a ⊆ c → b ⊆ d → f a b → f c d) :
    (∀ a b, f a b ↔ ∃ i ∈ a, ∃ j ∈ b, edge i j) ↔
    (∀ i j, edge i j → f {i} {j}) ∧
    (∀ t, right edge (left edge t) = t → ¬ f (left edge t) t) := by
  constructor
  · intro computes
    refine ⟨fun i j h => (computes _ _).2 ⟨i,rfl,j,rfl,h⟩,?_⟩
    intro t _ ht
    obtain ⟨i,hi,j,hj,e⟩ := (computes _ _).1 ht
    exact hi j hj e
  · rintro ⟨pos,neg⟩ a b
    constructor
    · intro yes
      by_contra empty
      let s := left edge b
      let t := right edge s
      have asub : a ⊆ s := fun i hi j hj e => empty ⟨i,hi,j,hj,e⟩
      have bsub : b ⊆ t := fun j hj i hi => hi j hj
      have same : left edge t = s := by
        ext i
        constructor
        · exact fun h j hj => h j (bsub hj)
        · exact fun hi j hj => hj i hi
      have close : right edge (left edge t) = t := by rw [same]
      exact (neg t close) (mono a b _ t (same.symm ▸ asub) bsub yes)
    · rintro ⟨i,hi,j,hj,e⟩
      exact mono {i} {j} a b (by intro v hv; have e : v = i := hv; exact e.symm ▸ hi)
        (by intro v hv; have e : v = j := hv; exact e.symm ▸ hj) (pos i j e)

end PEqualNP.Research.BipartiteBoundaryRows

open PEqualNP.Research.BipartiteBoundaryRows in
theorem PEqualNP.Research.BipartiteBoundaryRows :
    ∀ (edge : Fin 21 → Fin 19 → Prop) (f : Set (Fin 21) → Set (Fin 19) → Prop),
    (∀ a b c d, a ⊆ c → b ⊆ d → f a b → f c d) →
    ((∀ a b, f a b ↔ ∃ i ∈ a, ∃ j ∈ b, edge i j) ↔
    (∀ i j, edge i j → f {i} {j}) ∧
    (∀ t, right edge (left edge t) = t → ¬ f (left edge t) t)) := boundary
