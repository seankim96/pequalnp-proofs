import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Action.Defs

namespace PEqualNP.Research.PlaneComplementaryTraceBound

private theorem loss {k : Nat} (D : Finset (Fin 256)) (f : Fin k → Fin 256)
    (w : Fin 256 → Nat) (t : Nat) (inj : Function.Injective f) (mem : ∀ i, f i ∈ D) :
    k * t ≤ (∑ i, w (f i)) + ∑ x ∈ D, (t - w x) := by
  classical
  have sub : Finset.univ.image f ⊆ D := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact mem i
  have h := Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => Nat.zero_le (t - w i))
  rw [Finset.sum_image (fun _ _ _ _ he => inj he)] at h
  have aux := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (f := fun _ => t) (g := fun i => w (f i) + (t - w (f i))) (fun i _ => by omega)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at aux
  omega

end PEqualNP.Research.PlaneComplementaryTraceBound

open PEqualNP.Research.PlaneComplementaryTraceBound in
theorem PEqualNP.Research.PlaneComplementaryTraceBound :
  ∀ {k m : Nat} (D E : Finset (Fin 256))
    (left right : Fin k → Fin 256) (weightL weightR : Fin 256 → Nat)
    (orOn : Fin k → Fin m → Bool) (width : Fin k → Nat) (t u : Nat),
    Function.Injective left → Function.Injective right →
    (∀ i, left i ∈ D) → (∀ i, right i ∈ E) →
    (∀ i, weightL (left i) + weightR (right i) ≤
      (Finset.univ.filter (fun j => orOn i j = true)).card) →
    (∀ i, width i ≤ 1 + (Finset.univ.filter (fun j => orOn i j = false)).card) →
    (∑ i, width i) + k * (t + u) ≤ k * (m + 1) +
      (∑ x ∈ D, (t - weightL x)) + (∑ x ∈ E, (u - weightR x)) := by
  intro k m D E left right weightL weightR orOn width t u il ir ml mr charged packed
  have L := loss D left weightL t il ml
  have R := loss E right weightR u ir mr
  have point (i : Fin k) : width i + weightL (left i) + weightR (right i) ≤ m+1 := by
    have split := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (p := fun j => orOn i j = true)
    simp only [Bool.not_eq_true,Finset.card_univ,Fintype.card_fin] at split
    have h := charged i
    have g := packed i
    omega
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun i _ => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  simp only [Nat.mul_add,Nat.mul_one] at total ⊢
  omega
