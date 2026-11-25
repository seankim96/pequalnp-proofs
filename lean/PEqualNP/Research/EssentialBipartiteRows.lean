import PEqualNP.Research.BipartiteBoundaryRows

namespace PEqualNP.Research.EssentialBipartiteRows
open BipartiteBoundaryRows
abbrev I := Fin 21
abbrev J := Fin 19
def hit (e : I → J → Prop) (a : Set I) (b : Set J) := ∃ i ∈ a, ∃ j ∈ b, e i j
def increasing (f : Set I → Set J → Prop) :=
  ∀ a b c d, a ⊆ c → b ⊆ d → f a b → f c d

private theorem grow {e : I → J → Prop} : increasing (hit e) := by
  rintro _ _ _ _ ac bd ⟨i,hi,j,hj,edge⟩
  exact ⟨i,ac hi,j,bd hj,edge⟩

theorem omitEdge (e : I → J → Prop) (p : I) (q : J) :
    ∃ f, increasing f ∧ ∀ a b, f a b ↔ hit e a b ∧ ¬ (a = {p} ∧ b = {q}) := by
  refine ⟨fun a b => hit e a b ∧ ¬ (a = {p} ∧ b = {q}), ?_, fun _ _ => Iff.rfl⟩
  rintro a b c d ac bd ⟨yes,other⟩
  refine ⟨grow _ _ _ _ ac bd yes,?_⟩
  rintro ⟨rfl,rfl⟩
  obtain ⟨i,hi,j,hj,_⟩ := yes
  have ip : i = p := ac hi
  have jq : j = q := bd hj
  subst i; subst j
  apply other
  exact ⟨Set.Subset.antisymm ac (fun k hk => (show k = p from hk).symm ▸ hi),
         Set.Subset.antisymm bd (fun k hk => (show k = q from hk).symm ▸ hj)⟩

theorem omitClosed (e : I → J → Prop) (t : Set J) (ht : right e (left e t) = t) :
    ∃ f, increasing f ∧ ∀ a b, f a b ↔ hit e a b ∨ (a = left e t ∧ b = t) := by
  let s := left e t
  refine ⟨fun a b => hit e a b ∨ (s ⊆ a ∧ t ⊆ b),?_,?_⟩
  · rintro a b c d ac bd (yes|⟨sa,tb⟩)
    · exact Or.inl (grow _ _ _ _ ac bd yes)
    · exact Or.inr ⟨sa.trans ac,tb.trans bd⟩
  · intro a b
    constructor
    · rintro (yes|⟨sa,tb⟩)
      · exact Or.inl yes
      by_cases h : hit e a b
      · exact Or.inl h
      refine Or.inr ⟨Set.Subset.antisymm ?_ sa, Set.Subset.antisymm ?_ tb⟩
      · exact fun i hi j hj edge => h ⟨i,hi,j,tb hj,edge⟩
      · intro j hj
        rw [← ht]
        exact fun i hi edge => h ⟨i,sa hi,j,hj,edge⟩
    · rintro (yes|⟨rfl,rfl⟩)
      · exact Or.inl yes
      · exact Or.inr ⟨fun _ h => h,fun _ h => h⟩

end PEqualNP.Research.EssentialBipartiteRows

open PEqualNP.Research.EssentialBipartiteRows PEqualNP.Research.BipartiteBoundaryRows in
theorem PEqualNP.Research.EssentialBipartiteRows :
    ∀ e : I → J → Prop,
    (∀ p q, e p q → ∃ f, increasing f ∧
      ∀ a b, f a b ↔ hit e a b ∧ ¬ (a = {p} ∧ b = {q})) ∧
    (∀ t, right e (left e t) = t → ∃ f, increasing f ∧
      ∀ a b, f a b ↔ hit e a b ∨ (a = left e t ∧ b = t)) :=
  fun e => ⟨fun p q _ => omitEdge e p q, omitClosed e⟩
