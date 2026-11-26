import PEqualNP.Research.PlaneFiveFlagMultiplicity
import PEqualNP.Research.PlaneSparseAndPrefix

namespace PEqualNP.Research.PlaneFiveFlagSuffixBudget
def higher (witness : Fin 468 → Fin 468 → Finset (Fin 52)) (t : Finset (Fin 52)) :
    Finset (Fin 468) := Finset.univ.filter fun b => ∃ a : Fin 468, a < b ∧ witness a b = t
end PEqualNP.Research.PlaneFiveFlagSuffixBudget

open PEqualNP.Research.PlaneFiveFlagSuffixBudget PEqualNP.Research.PlaneFiveFlagMultiplicity
  PEqualNP.Research.PlaneSparseAndPrefix PEqualNP.Research.PlaneFirstAndSeparation
  PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneFiveFlagSuffixBudget :
    ∀ (s : List Column) (preGates tail : List Gate) (out : Nat)
      (S : Finset (Fin 52)) (flags : Nat → Bool) (witness : Fin 468 → Fin 468 → Finset (Fin 52)),
    S.card ≤ 5 →
    (∀ p : Fin 52, flags p.val = true ↔ p ∈ S) →
    (∀ t ⊆ S, (higher witness t).card ≤ bound t.card) →
    (∀ a b : Fin 468, a < b → ∀ p ∈ witness a b, ∀ v ∈ s, good p.val (52+a.val) (52+b.val) v) →
    guarded s preGates flags →
    let final := tail.foldl step (preGates.foldl step s)
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro s pre tail out S flags witness small agree cap valid guard
  dsimp only
  intro yes no
  let excluded := S.powerset.biUnion (higher witness)
  have card := PEqualNP.Research.PlaneFiveFlagMultiplicity S (higher witness) small cap
  apply PEqualNP.Research.PlaneSparseAndPrefix s pre tail flags excluded out (le_trans card (by decide)) _ guard yes no
  intro a b _ hb lt
  have notSub : ¬ witness a b ⊆ S := by
    intro sub
    apply hb
    exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_powerset.mpr sub,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,lt,rfl⟩⟩
  obtain ⟨p,hp,off⟩ := Finset.not_subset.mp notSub
  exact ⟨p,Bool.eq_false_iff.mpr (fun on => off ((agree p).mp on)),valid a b lt p hp⟩
