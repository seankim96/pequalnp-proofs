import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs.MetaComplexityLgpMono

namespace PEqualNP.Research.Gap16796Witness
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def gates : List Gate := [⟨.and, [0,5]⟩, ⟨.and, [2,4]⟩, ⟨.or, [6,7]⟩, ⟨.or, [1,8]⟩, ⟨.and, [3,9]⟩, ⟨.or, [0,1]⟩, ⟨.or, [0,5]⟩, ⟨.and, [4,12]⟩, ⟨.or, [2,13]⟩, ⟨.and, [11,14]⟩, ⟨.or, [10,15]⟩]
theorem monotone : Monotone2 ⟨gates,16⟩ := by simp [Monotone2,gates]
theorem computes : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates,16⟩ (List.ofFn x) = target x := by
  intro x
  have eqx : x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [eqx]
  exact (by
    intro b0 b1 b2 b3 b4 b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide +kernel
    : ∀ b0 b1 b2 b3 b4 b5 : Bool, Circuit.eval ⟨gates,16⟩ (List.ofFn ![b0,b1,b2,b3,b4,b5]) = target ![b0,b1,b2,b3,b4,b5]) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

end PEqualNP.Research.Gap16796Witness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.Gap16796Witness in
theorem PEqualNP.Research.Gap16796Witness : ∃ C : Circuit, Monotone2 C ∧ C.size = 11 ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x :=
  ⟨⟨gates,16⟩, monotone, rfl, computes⟩
