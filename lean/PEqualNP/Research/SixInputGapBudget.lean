import PEqualNP.Outside.L_meta_8669

namespace PEqualNP.Research.SixInputGapBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_8669_aux
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264000 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def gates : List Gate := [⟨.or, [1,5]⟩, ⟨.and, [3,6]⟩, ⟨.or, [4,7]⟩, ⟨.and, [0,8]⟩, ⟨.and, [4,5]⟩, ⟨.or, [3,10]⟩, ⟨.or, [0,11]⟩, ⟨.and, [2,12]⟩, ⟨.and, [1,13]⟩, ⟨.or, [9,14]⟩]
def inputMap : Fin 6 → Fin 5 := ![1,0,0,3,2,4]
theorem lower (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  have hd : ∃ x : Fin 6 → Bool, target (Function.update x 2 (!x 2)) ≠ target x := by
    exact ⟨![true,true,false,false,false,false], by decide +kernel⟩
  have hn : ∃ x y : Fin 6 → Bool, target (Function.update x 2 true) ≠ target (Function.update y 2 true) := by
    exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨r, hr, hc⟩ := one_gate_at 5 target 2 true s hd hn h
  have hh := relabel_size inputMap _ r hc
  have ee : (fun x : Fin 5 → Bool => target (Function.update (x ∘ inputMap) 2 true)) = (fun x => Nat.testBit 0xeee8eac8 (idx5 x)) := by
    funext x
    have eqx : x = ![x 0,x 1,x 2,x 3,x 4] := by
      funext i
      fin_cases i <;> rfl
    rw [eqx]
    exact (by
      intro b0 b1 b2 b3 b4
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide +kernel
      : ∀ b0 b1 b2 b3 b4 : Bool, target (Function.update (![b0,b1,b2,b3,b4] ∘ inputMap) 2 true) = Nat.testBit 0xeee8eac8 (idx5 ![b0,b1,b2,b3,b4])) (x 0) (x 1) (x 2) (x 3) (x 4)
  change HasCircuitSize 5 (fun x => target (Function.update (x ∘ inputMap) 2 true)) r at hh
  rw [ee] at hh
  have := R0.lb r hh
  omega
theorem monotone : Monotone2 ⟨gates,15⟩ := by simp [Monotone2,gates]
theorem computes : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates,15⟩ (List.ofFn x) = target x := by
  intro x
  have eqx : x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [eqx]
  exact (by
    intro b0 b1 b2 b3 b4 b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide +kernel
    : ∀ b0 b1 b2 b3 b4 b5 : Bool, Circuit.eval ⟨gates,15⟩ (List.ofFn ![b0,b1,b2,b3,b4,b5]) = target ![b0,b1,b2,b3,b4,b5]) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- A budget separating the two bases must be exactly nine. -/
theorem separatingBudget (s : Nat) (h : HasCircuitSize 6 target s)
    (noMono : ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) : s = 9 := by
  have lo := lower s h
  by_contra hn
  apply noMono
  exact ⟨⟨gates,15⟩, monotone, by change 10 ≤ s; omega, computes⟩

end PEqualNP.Research.SixInputGapBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.SixInputGapBudget in
theorem PEqualNP.Research.SixInputGapBudget :
    (¬ ∀ s : Nat, HasCircuitSize 6 target s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) ↔
    (HasCircuitSize 6 target 9 ∧ ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 9 ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Classical.not_forall.mp h
    have hp := Classical.not_imp.mp hs
    obtain ⟨hs, noMono⟩ := hp
    have eq := separatingBudget s hs noMono
    subst s
    exact ⟨hs,noMono⟩
  · rintro ⟨hs, hn⟩ h
    exact hn (h 9 hs)
