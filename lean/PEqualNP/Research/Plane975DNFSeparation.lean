import PEqualNP.Research.Plane975DNF

open PEqualNP.Research.Plane975DNF PEqualNP.Research.Plane975AndConjunction in
theorem PEqualNP.Research.Plane975DNFSeparation : ∀ ts : List Term,
    ∃ flags : List (Fin 52), flags.length ≤ ts.length ∧
      ∀ (p : Fin 52) (a b : Nat), p ∉ flags →
        (∀ w : Fin 31, wire positive[p.val]! w = true → wire a w = true ∨ wire b w = true) →
        value ts positive[p.val]! = true → value ts a = true ∨ value ts b = true := by
  intro ts
  obtain ⟨ws,flags,count,sub,cover⟩ := PEqualNP.Research.Plane975DNF ts
  refine ⟨flags,by omega,?_⟩
  intro p a b off pair on
  have inheritedOn := (cover p on).resolve_right off
  obtain ⟨w,mem,hit⟩ := List.any_eq_true.mp inheritedOn
  rcases pair w hit with left | right
  · exact Or.inl (sub a (List.any_eq_true.mpr ⟨w,mem,left⟩))
  · exact Or.inr (sub b (List.any_eq_true.mpr ⟨w,mem,right⟩))
