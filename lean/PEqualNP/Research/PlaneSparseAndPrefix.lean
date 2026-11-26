import PEqualNP.Research.PlaneFirstAndBudget
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Research.PlaneSparseAndPrefix
open PlaneFirstAndSeparation PlaneFirstAndBudget

def guarded (s : List Column) (gs : List Gate) (flags : Nat → Bool) : Prop :=
  ∀ xs g ys, gs = xs ++ g :: ys → g.1 = true → ∀ p : Fin 52,
    let t := xs.foldl step s
    both (wire t g.2.1) (wire t g.2.2) p.val = true → flags p.val = true

private theorem readGood {s : List Column} {p a b : Nat} (h : ∀ w ∈ s, good p a b w) (i : Nat) :
    good p a b (wire s i) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => simp [good]
  | some w => exact h w (List.mem_of_getElem? e)

private theorem preserve (gs : List Gate) (s : List Column) (p : Fin 52) (a b : Nat)
    (flags : Nat → Bool) (off : flags p.val = false) (bound : guarded s gs flags)
    (h : ∀ w ∈ s, good p.val a b w) : ∀ w ∈ gs.foldl step s, good p.val a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step s g)
    · intro xs k ys eq op i
      dsimp only
      intro on
      exact bound (g :: xs) k ys (by simp [eq]) op i on
    · intro w hw
      cases op : g.1
      · simp only [step,op,Bool.false_eq_true,ite_false,addOr,List.mem_append,List.mem_singleton] at hw
        rcases hw with old | rfl
        · exact h _ old
        · have hl := readGood h g.2.1
          have hr := readGood h g.2.2
          unfold good at *
          simp only [Bool.or_eq_true] at *
          tauto
      · simp only [step,op,ite_true,List.mem_append,List.mem_singleton] at hw
        rcases hw with old | rfl
        · exact h _ old
        · intro on
          have bad := bound [] g gs rfl op p on
          rw [off] at bad
          contradiction
end PEqualNP.Research.PlaneSparseAndPrefix

open PEqualNP.Research.PlaneSparseAndPrefix PEqualNP.Research.PlaneFirstAndSeparation
  PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneSparseAndPrefix : ∀ (s : List Column) (preGates tail : List Gate)
    (flags : Nat → Bool) (excluded : Finset (Fin 468)) (out : Nat),
    excluded.card ≤ 211 →
    (∀ a b : Fin 468, a ∉ excluded → b ∉ excluded → a < b →
      ∃ p : Fin 52, flags p.val = false ∧ ∀ w ∈ s, good p.val (52+a.val) (52+b.val) w) →
    guarded s preGates flags →
    let final := tail.foldl step (preGates.foldl step s)
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro s pre tail flags excluded out card pairs bound
  dsimp only
  intro hp hn
  apply separated_bound _ tail out _ hp hn
  let K := Finset.univ \ excluded
  have hk : 257 ≤ K.card := by
    change 257 ≤ (Finset.univ \ excluded).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  let ix (i : Fin 257) : Fin K.card := ⟨i.val,by omega⟩
  let n (i : Fin 257) := K.orderEmbOfFin rfl (ix i)
  have mem (i : Fin 257) : n i ∈ K := K.orderEmbOfFin_mem rfl _
  refine ⟨n,?_⟩
  intro i j lt
  have inc : n i < n j := (K.orderEmbOfFin rfl).strictMono (show ix i < ix j from lt)
  obtain ⟨p,off,h⟩ := pairs _ _ (Finset.mem_sdiff.mp (mem i)).2 (Finset.mem_sdiff.mp (mem j)).2 inc
  exact ⟨p,preserve pre s p _ _ flags off bound h⟩
