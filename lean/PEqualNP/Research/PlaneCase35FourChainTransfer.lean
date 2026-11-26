import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.PlaneCase35FourChainTransfer
variable {n : Nat}
private abbrev Basis (rows : Nat → Finset (Fin n)) (high : Fin 52 → Prop) :=
  ∀ a b : Fin n, (∀ r, a ∈ rows r → b ∈ rows r) ∨
    (∀ r, b ∈ rows r → a ∈ rows r) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, high p → a ∈ rows p.val → b ∈ rows p.val → p = q

private theorem termShape {rows : Nat → Finset (Fin n)} {high : Fin 52 → Prop}
    (basis : Basis rows high) (t : Finset (Fin n)) :
    (∀ r, t ⊆ rows r) ∨ (∃ a : Fin n, ∀ r, t ⊆ rows r ↔ a ∈ rows r) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, high p → t ⊆ rows p.val → p = q := by
  induction t using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert a t _ ih =>
    rcases ih with all | ⟨b,hb⟩ | ⟨q,hq⟩
    · exact Or.inr (Or.inl ⟨a,fun r => by simp [Finset.insert_subset_iff,all r]⟩)
    · rcases basis a b with ab | ba | ⟨q,hq⟩
      · refine Or.inr (Or.inl ⟨a,?_⟩)
        intro r; rw [Finset.insert_subset_iff,hb]
        exact ⟨And.left,fun h => ⟨h,ab r h⟩⟩
      · refine Or.inr (Or.inl ⟨b,?_⟩)
        intro r; rw [Finset.insert_subset_iff,hb]
        exact ⟨And.right,fun h => ⟨ba r h,h⟩⟩
      · refine Or.inr (Or.inr ⟨q,?_⟩)
        intro p hp h
        obtain ⟨ha,ht⟩ := Finset.insert_subset_iff.mp h
        exact hq p hp ha ((hb _).mp ht)
    · exact Or.inr (Or.inr ⟨q,fun p hp h => hq p hp (Finset.insert_subset_iff.mp h).2⟩)

private abbrev Pass (rows : Nat → Finset (Fin n)) (p i j : Nat) (t : Finset (Fin n)) :=
  t ⊆ rows p → t ⊆ rows i ∨ t ⊆ rows j
private abbrev Raw (rows : Nat → Finset (Fin n)) (p i j : Nat) :=
  ∀ a ∈ rows p, a ∈ rows i ∨ a ∈ rows j

private theorem chain (rows : Nat → Finset (Fin n)) (high : Fin 52 → Prop)
    (basis : Basis rows high) (ts : List (Finset (Fin n)))
    (ordered : ts.Pairwise (· ⊆ ·)) :
    ∃ q : Fin 52, ∀ (p : Fin 52) (i j : Nat), high p → p ≠ q →
      Raw rows p.val i j → ∀ t ∈ ts, Pass rows p.val i j t := by
  induction ts with
  | nil => exact ⟨0,by simp⟩
  | cons t ts ih =>
    obtain ⟨head,rest⟩ := List.pairwise_cons.mp ordered
    obtain ⟨q,tail⟩ := ih rest
    rcases termShape basis t with all | ⟨a,one⟩ | ⟨b,single⟩
    · refine ⟨q,?_⟩
      intro p i j hp ne raw u mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact fun _ => Or.inl (all i)
      · exact tail p i j hp ne raw u h
    · refine ⟨q,?_⟩
      intro p i j hp ne raw u mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact fun hit => (raw a ((one _).mp hit)).imp (one i).mpr (one j).mpr
      · exact tail p i j hp ne raw u h
    · refine ⟨b,?_⟩
      intro p i j hp ne _ u mem hit
      have sub : t ⊆ u := by
        rcases List.mem_cons.mp mem with rfl | h
        · exact Finset.Subset.rfl
        · exact head u h
      exact False.elim (ne (single p hp (sub.trans hit)))
end PEqualNP.Research.PlaneCase35FourChainTransfer
open PEqualNP.Research.PlaneCase35FourChainTransfer in
theorem PEqualNP.Research.PlaneCase35FourChainTransfer : ∀ (n : Nat) (rows : Nat → Finset (Fin n)) (high : Fin 52 → Prop),
  (∀ a b : Fin n, (∀ r, a ∈ rows r → b ∈ rows r) ∨
    (∀ r, b ∈ rows r → a ∈ rows r) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, high p → a ∈ rows p.val → b ∈ rows p.val → p = q) →
  ∀ (chains : Fin 4 → List (Finset (Fin n))), (∀ k, (chains k).Pairwise (· ⊆ ·)) →
  ∃ S : Finset (Fin 52), S.card ≤ 4 ∧ ∀ (p : Fin 52) (i j : Nat),
    high p → p ∉ S → (∀ a ∈ rows p.val, a ∈ rows i ∨ a ∈ rows j) →
    ∀ f : List (Finset (Fin n)), (∀ t ∈ f, 1 < t.card → ∃ k, t ∈ chains k) →
      (∃ t ∈ f, t ⊆ rows p.val) → (∃ t ∈ f, t ⊆ rows i) ∨ (∃ t ∈ f, t ⊆ rows j) := by
  classical
  intro n rows high basis chains ordered
  choose exc pass using fun k => chain rows high basis (chains k) (ordered k)
  let S := Finset.univ.image exc
  refine ⟨S,Finset.card_image_le.trans (by simp),?_⟩
  intro p i j hp clear raw f covered active
  obtain ⟨t,ht,hit⟩ := active
  suffices h : t ⊆ rows i ∨ t ⊆ rows j from h.imp (fun h => ⟨t,ht,h⟩) (fun h => ⟨t,ht,h⟩)
  by_cases big : 1 < t.card
  · obtain ⟨k,hk⟩ := covered t ht big
    have ne : p ≠ exc k := fun eq => clear (eq ▸ Finset.mem_image_of_mem exc (Finset.mem_univ k))
    exact pass k p i j hp ne raw t hk hit
  · by_cases empty : t.card = 0
    · simp [Finset.card_eq_zero.mp empty]
    · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
      simpa using raw a (Finset.singleton_subset_iff.mp hit)
