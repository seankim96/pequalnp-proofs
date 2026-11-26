import PEqualNP.Research.Plane975AndConjunction

namespace PEqualNP.Research.Plane975DNF
open Plane975AndConjunction

abbrev Term := Fin 31 × List (Fin 31)
def value (ts : List Term) (x : Nat) := ts.any (fun t => product t.1 t.2 x)
def inherited (ws : List (Fin 31)) (x : Nat) := ws.any (wire x)

end PEqualNP.Research.Plane975DNF

open PEqualNP.Research.Plane975DNF PEqualNP.Research.Plane975AndConjunction in
theorem PEqualNP.Research.Plane975DNF : ∀ ts : List Term,
    ∃ (ws : List (Fin 31)) (flags : List (Fin 52)),
      ws.length + flags.length = ts.length ∧
      (∀ x : Nat, inherited ws x = true → value ts x = true) ∧
      (∀ p : Fin 52, value ts positive[p.val]! = true →
        inherited ws positive[p.val]! = true ∨ p ∈ flags) := by
  intro ts
  induction ts with
  | nil => exact ⟨[],[],by simp [value,inherited]⟩
  | cons t ts ih =>
    obtain ⟨ws,flags,hsize,sub,cover⟩ := ih
    rcases PEqualNP.Research.Plane975AndConjunction t.1 t.2 with ⟨w,hw⟩ | ⟨e,he⟩
    · refine ⟨w :: ws,flags,by simp only [List.length_cons]; omega,?_,?_⟩
      · intro x h
        simp only [inherited,List.any_cons,Bool.or_eq_true] at h
        change (product t.1 t.2 x || value ts x) = true
        exact Bool.or_eq_true_iff.mpr (h.imp (fun a => (hw x).trans a) (sub x))
      · intro p h
        change (product t.1 t.2 _ || value ts _) = true at h
        change (wire _ w || inherited ws _) = true ∨ _
        rcases Bool.or_eq_true_iff.mp h with a | b
        · exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inl ((hw _).symm.trans a)))
        · rcases cover p b with c | d
          · exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inr c))
          · exact Or.inr d
    · refine ⟨ws,e :: flags,by simp only [List.length_cons]; omega,?_,?_⟩
      · intro x h
        exact Bool.or_eq_true_iff.mpr (Or.inr (sub x h))
      · intro p h
        rcases Bool.or_eq_true_iff.mp h with a | b
        · exact Or.inr (List.mem_cons.mpr (Or.inl (he p a)))
        · exact (cover p b).imp_right (fun h => List.mem_cons.mpr (Or.inr h))
