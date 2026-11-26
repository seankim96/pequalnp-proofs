import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

namespace PEqualNP.Research.PlaneFiveFlagMultiplicity
def bound (k : Nat) : Nat := if k = 1 then 18 else if k = 2 then 4 else if k = 3 then 3 else if k = 4 then 2 else if k = 5 then 1 else 0
end PEqualNP.Research.PlaneFiveFlagMultiplicity

open PEqualNP.Research.PlaneFiveFlagMultiplicity in
theorem PEqualNP.Research.PlaneFiveFlagMultiplicity :
    ∀ (S : Finset (Fin 52)) (endpoints : Finset (Fin 52) → Finset (Fin 468)),
    S.card ≤ 5 →
    (∀ t ⊆ S, (endpoints t).card ≤ bound t.card) →
    (S.powerset.biUnion endpoints).card ≤ 171 := by
  intro S endpoints small cap
  let layer := fun k => (S.powersetCard k).biUnion endpoints
  have incl : S.powerset.biUnion endpoints ⊆ (Finset.range 6).biUnion layer := by
    intro i hi
    obtain ⟨t,ht,mem⟩ := Finset.mem_biUnion.mp hi
    have sub := Finset.mem_powerset.mp ht
    have card := Finset.card_le_card sub
    exact Finset.mem_biUnion.mpr ⟨t.card,Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.mpr ⟨t,Finset.mem_powersetCard.mpr ⟨sub,rfl⟩,mem⟩⟩
  have per (k : Nat) : (layer k).card ≤ Nat.choose 5 k * bound k := by
    apply le_trans (Finset.card_biUnion_le_card_mul _ endpoints (bound k) ?_)
    · rw [Finset.card_powersetCard]
      exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ small)
    · intro t ht
      obtain ⟨sub,hk⟩ := Finset.mem_powersetCard.mp ht
      simpa only [← hk] using cap t sub
  calc
    _ ≤ ((Finset.range 6).biUnion layer).card := Finset.card_le_card incl
    _ ≤ ∑ k ∈ Finset.range 6, (layer k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range 6, Nat.choose 5 k * bound k := Finset.sum_le_sum (fun k _ => per k)
    _ = 171 := by decide
