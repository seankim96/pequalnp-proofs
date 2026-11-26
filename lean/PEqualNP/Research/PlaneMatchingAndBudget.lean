import PEqualNP.Research.PlaneFirstAndBudget
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Research.PlaneMatchingAndBudget
open PlaneFirstAndSeparation PlaneFirstAndBudget
def clashes (s : Finset (Fin 468)) (mate : Fin 468 → Fin 468) :=
  s.filter fun i => mate i < i ∧ mate i ∈ s
def side (l r : Column) : Finset (Fin 468) :=
  Finset.univ.filter fun i => l (52+i.val) = true → r (52+i.val) = true

private theorem extract (T : Finset (Fin 468)) (mate : Fin 468 → Fin 468)
    (count : 257 + (clashes T mate).card ≤ T.card) :
    ∃ n : Fin 257 → Fin 468, (∀ i, n i ∈ T) ∧
      ∀ i j, i < j → n i < n j ∧ mate (n j) ≠ n i := by
  let K := T \ clashes T mate
  have sub : clashes T mate ⊆ T := Finset.filter_subset _ _
  have hk : 257 ≤ K.card := by
    change 257 ≤ (T \ clashes T mate).card
    rw [Finset.card_sdiff_of_subset sub]
    omega
  let ix (i : Fin 257) : Fin K.card := ⟨i.val,by omega⟩
  let n (i : Fin 257) : Fin 468 := K.orderEmbOfFin rfl (ix i)
  have mem (i : Fin 257) : n i ∈ K := K.orderEmbOfFin_mem rfl _
  have inT (i : Fin 257) : n i ∈ T := (Finset.mem_sdiff.mp (mem i)).1
  refine ⟨n,inT,?_⟩
  intro i j lt
  have order : n i < n j := (K.orderEmbOfFin rfl).strictMono (show ix i < ix j from lt)
  refine ⟨order,?_⟩
  intro eq
  have bad : n j ∈ clashes T mate := Finset.mem_filter.mpr ⟨inT j,by rw [eq]; exact ⟨order,inT i⟩⟩
  exact (Finset.mem_sdiff.mp (mem j)).2 bad

private theorem withSide (s : List Column) (l r : Column) (mate : Fin 468 → Fin 468)
    (pairs : ∀ a b : Fin 468, a < b → mate b ≠ a →
      ∃ p : Fin 52, ∀ w ∈ s, good p.val (52+a.val) (52+b.val) w)
    (lift : ∀ p a b : Nat, (∀ w ∈ s, good p a b w) → good p a b l)
    (count : 257 + (clashes (side l r) mate).card ≤ (side l r).card) :
    separated (s ++ [both l r]) := by
  obtain ⟨n,mem,order⟩ := extract _ _ count
  refine ⟨n,?_⟩
  intro i j lt
  obtain ⟨inc,ne⟩ := order i j lt
  obtain ⟨p,h⟩ := pairs _ _ inc ne
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact h w old
  · obtain rfl := List.mem_singleton.mp last
    have a := (Finset.mem_filter.mp (mem i)).2
    have b := (Finset.mem_filter.mp (mem j)).2
    have hl := lift _ _ _ h
    unfold good both at *
    simp only [Bool.and_eq_true] at *
    tauto

end PEqualNP.Research.PlaneMatchingAndBudget

open PEqualNP.Research.PlaneMatchingAndBudget PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneMatchingAndBudget : ∀ (s : List Column) (l r : Column) (mate : Fin 468 → Fin 468)
    (tail : List Gate) (o : Nat),
    (∀ a b : Fin 468, a < b → mate b ≠ a →
      ∃ p : Fin 52, ∀ w ∈ s, good p.val (52+a.val) (52+b.val) w) →
    (∀ p a b : Nat, (∀ w ∈ s, good p a b w) → good p a b l ∧ good p a b r) →
    (257 + (clashes (side l r) mate).card ≤ (side l r).card ∨
     257 + (clashes (side r l) mate).card ≤ (side r l).card) →
    let final := tail.foldl step (s ++ [both l r])
    (∀ p : Fin 52, wire final o p.val = true) →
    (∀ n : Fin 468, wire final o (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro s l r mate tail o h hl counts
  dsimp only
  intro hp hn
  apply separated_bound _ tail o _ hp hn
  rcases counts with a | b
  · exact withSide s l r mate h (fun p i j v => (hl p i j v).1) a
  · have sep := withSide s r l mate h (fun p i j v => (hl p i j v).2) b
    have eq : both r l = both l r := by funext i; exact Bool.and_comm _ _
    rwa [eq] at sep
