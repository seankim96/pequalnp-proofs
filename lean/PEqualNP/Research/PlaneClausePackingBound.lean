import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

theorem PEqualNP.Research.PlaneClausePackingBound : ∀ (n m p : Nat) (pos : Fin p → Nat → Bool) (neg : Fin n → Nat → Bool)
    (clauses : Fin m → List Nat),
    (∀ i j : Fin n, i ≠ j → ∃ k : Fin p, ∀ l, pos k l = true →
      neg i l = true ∨ neg j l = true) →
    (∀ k c, (clauses c).any (pos k) = true) →
    (∀ i, ∃ c, (clauses c).any (neg i) = false) → n ≤ m := by
  intro n m p pos neg clauses obstruction positive negative
  classical
  choose reject rejected using negative
  have inj : Function.Injective reject := by
    intro i j same
    by_contra distinct
    obtain ⟨k, covers⟩ := obstruction i j distinct
    obtain ⟨l, mem, lit⟩ := List.any_eq_true.mp (positive k (reject i))
    rcases covers l lit with hi | hj
    · have hit := List.any_eq_true.mpr ⟨l, mem, hi⟩
      simpa [rejected i] using hit
    · rw [same] at mem
      have hit := List.any_eq_true.mpr ⟨l, mem, hj⟩
      simpa [rejected j] using hit
  simpa using Fintype.card_le_of_injective reject inj
