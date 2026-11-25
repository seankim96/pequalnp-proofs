import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Union

namespace PEqualNP.Research.PuncturedPlaneOrNetwork
abbrev V := Fin 21
abbrev W := Finset V
abbrev Pool := Finset W

def columns : List W := [{2,3,6,16,18}, {3,4,7,17,19}, {4,5,8,18,20}, {0,5,6,9,19}, {1,6,7,10,20}, {0,2,7,8,11}, {1,3,8,9,12}, {2,4,9,10,13}, {3,5,10,11,14}, {4,6,11,12,15}, {5,7,12,13,16}, {6,8,13,14,17}, {7,9,14,15,18}, {8,10,15,16,19}, {9,11,16,17,20}, {0,10,12,17,18}, {1,11,13,18,19}, {2,12,14,19,20}, {0,3,13,15,20}]
def base : Pool := insert ∅ (Finset.univ.image fun v : V => {v})

/-- The list records every paid OR output, including repeated wires. -/
inductive Built : Pool → List W → Prop where
  | start : Built base []
  | add {p g a b} : Built p g → a ∈ p → b ∈ p →
      Built (insert (a ∪ b) p) ((a ∪ b) :: g)

def charged (t z : W) := decide (2 ≤ z.card ∧ z ⊆ t)
def count (t : W) (g : List W) := (g.filter (charged t)).length

private theorem localBound {p g} (h : Built p g) (t : W) :
    ∀ s : Pool, s ⊆ p → (∀ z ∈ s, z ⊆ t) →
      (s.biUnion id).card ≤ s.card + count t g := by
  induction h with
  | start =>
    intro s sub _
    have each (z : W) (hz : z ∈ s) : z.card ≤ 1 := by
      rcases Finset.mem_insert.mp (sub hz) with he|hi
      · simp [he]
      · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
        simp
    have le := (Finset.card_biUnion_le (s := s) (t := id)).trans
      (Finset.sum_le_sum (fun z hz => each z hz))
    simpa [count] using le
  | @add p g a b _ ha hb ih =>
    intro s sub inside
    let u := a ∪ b
    by_cases hu : u ∈ s
    · let rest := s.erase u
      have old : rest ⊆ p := by
        intro z hz
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hz
        exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
      have covered := inside u hu
      have size : rest.card + 1 = s.card := by
        simpa [rest] using Finset.card_erase_add_one hu
      have whole : s = insert u rest := (Finset.insert_erase hu).symm
      by_cases big : 2 ≤ u.card
      · let next := insert a (insert b rest)
        have sub' : next ⊆ p := Finset.insert_subset ha (Finset.insert_subset hb old)
        have small : ∀ z ∈ next, z ⊆ t := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl|hh
          · exact Finset.Subset.trans Finset.subset_union_left covered
          rcases Finset.mem_insert.mp hh with rfl|hh
          · exact Finset.Subset.trans Finset.subset_union_right covered
          exact inside z (Finset.mem_of_mem_erase hh)
        have eq : s.biUnion id = next.biUnion id := by
          conv_lhs => rw [whole]
          simp [next,u,Finset.union_assoc]
        have nc : next.card ≤ rest.card + 2 := by
          have h1 := Finset.card_insert_le a (insert b rest)
          have h2 := Finset.card_insert_le b rest
          dsimp [next]; omega
        have step := ih next sub' small
        have ch : charged t (a ∪ b) = true := decide_eq_true ⟨big,covered⟩
        rw [eq]; simp [count,ch] at step ⊢; omega
      · have step := ih rest old (fun z hz => inside z (Finset.mem_of_mem_erase hz))
        have le : (s.biUnion id).card ≤ u.card + (rest.biUnion id).card := by
          conv_lhs => rw [whole]
          simpa using (Finset.card_union_le u (rest.biUnion id))
        have ch : charged t (a ∪ b) = false := decide_eq_false (fun h => big h.1)
        simp [count,ch] at step ⊢; omega
    · have old : s ⊆ p := by
        intro z hz
        rcases Finset.mem_insert.mp (sub hz) with eq|hh
        · exact False.elim (hu (show a ∪ b ∈ s from eq ▸ hz))
        · exact hh
      have step := ih s old inside
      unfold count at *
      cases ch : charged t (a ∪ b) <;> simp [ch] <;> omega

private theorem pairUnique : ∀ i j : V, i ≠ j →
    (columns.filter (fun t => decide (i ∈ t ∧ j ∈ t))).length ≤ 1 := by decide +kernel

private theorem once (z : W) : (columns.filter (fun t => charged t z)).length ≤ 1 := by
  by_cases h : 2 ≤ z.card
  · obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp h
    have mono (p q : W → Bool) (imp : ∀ a, p a = true → q a = true) (l : List W) :
        (l.filter p).length ≤ (l.filter q).length := by
      induction l with
      | nil => simp
      | cons a l ih =>
        cases hp : p a with
        | true => simpa [hp,imp a hp] using ih
        | false => cases hq : q a <;> simp [hp,hq] <;> omega
    apply Nat.le_trans (mono (fun t => charged t z) (fun t => decide (i ∈ t ∧ j ∈ t)) ?_ columns)
      (pairUnique i j ne)
    intro t ht
    have sub := (of_decide_eq_true ht : 2 ≤ z.card ∧ z ⊆ t).2
    exact decide_eq_true ⟨sub hi,sub hj⟩
  · have eq : columns.filter (fun t => charged t z) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t _; simp [charged,h]
    simp [eq]

private theorem totalCost (g : List W) : (columns.map (fun t => count t g)).sum ≤ g.length := by
  induction g with
  | nil => simp [count,columns]
  | cons z g ih =>
    have tally (l : List W) :
        (l.map (fun t => count t (z::g))).sum =
          (l.map (fun t => count t g)).sum + (l.filter fun t => charged t z).length := by
      induction l with
      | nil => simp
      | cons a l ih' =>
        cases ch : charged a z <;> simp [count,ch] at ih' ⊢ <;> omega
    rw [tally]
    have hz := once z
    simp; omega

theorem lower {p g} (h : Built p g) (outputs : ∀ t ∈ columns, t ∈ p) : 76 ≤ g.length := by
  have four (t) (ht : t ∈ columns) : 4 ≤ count t g := by
    have sz : ∀ x ∈ columns, x.card = 5 := by decide +kernel
    have le := localBound h t {t} (by simpa using outputs t ht) (by simp)
    simp [sz t ht] at le; omega
  have sum (l : List W) (hl : ∀ t ∈ l, t ∈ columns) :
      4*l.length ≤ (l.map (fun t => count t g)).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have one := four a (hl a (by simp))
      have tail := ih (fun t ht => hl t (by simp [ht]))
      simp; omega
  exact (sum columns (by simp)).trans (totalCost g)

def step (p : Pool) (pair : W × W) : Pool :=
  if pair.1 ∈ p ∧ pair.2 ∈ p then insert (pair.1 ∪ pair.2) p else p

private theorem execute (l : List (W × W)) {p g} (h : Built p g) :
    ∃ gs, Built (l.foldl step p) gs ∧ gs.length ≤ g.length + l.length := by
  induction l generalizing p g with
  | nil => exact ⟨g,h,by simp⟩
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hv : a.1 ∈ p ∧ a.2 ∈ p
    · simp only [step,if_pos hv]
      obtain ⟨gs,hh,hl⟩ := ih (h.add hv.1 hv.2)
      exact ⟨gs,hh,by simp at hl ⊢; omega⟩
    · simp only [step,if_neg hv]
      obtain ⟨gs,hh,hl⟩ := ih h
      exact ⟨gs,hh,by simp; omega⟩

private def schedule : List (W × W) := [
  ({2}, {3}), ({2,3}, {6}), ({2,3,6}, {16}), ({2,3,6,16}, {18}),
  ({3}, {4}), ({3,4}, {7}), ({3,4,7}, {17}), ({3,4,7,17}, {19}),
  ({4}, {5}), ({4,5}, {8}), ({4,5,8}, {18}), ({4,5,8,18}, {20}),
  ({0}, {5}), ({0,5}, {6}), ({0,5,6}, {9}), ({0,5,6,9}, {19}),
  ({1}, {6}), ({1,6}, {7}), ({1,6,7}, {10}), ({1,6,7,10}, {20}),
  ({0}, {2}), ({0,2}, {7}), ({0,2,7}, {8}), ({0,2,7,8}, {11}),
  ({1}, {3}), ({1,3}, {8}), ({1,3,8}, {9}), ({1,3,8,9}, {12}),
  ({2}, {4}), ({2,4}, {9}), ({2,4,9}, {10}), ({2,4,9,10}, {13}),
  ({3}, {5}), ({3,5}, {10}), ({3,5,10}, {11}), ({3,5,10,11}, {14}),
  ({4}, {6}), ({4,6}, {11}), ({4,6,11}, {12}), ({4,6,11,12}, {15}),
  ({5}, {7}), ({5,7}, {12}), ({5,7,12}, {13}), ({5,7,12,13}, {16}),
  ({6}, {8}), ({6,8}, {13}), ({6,8,13}, {14}), ({6,8,13,14}, {17}),
  ({7}, {9}), ({7,9}, {14}), ({7,9,14}, {15}), ({7,9,14,15}, {18}),
  ({8}, {10}), ({8,10}, {15}), ({8,10,15}, {16}), ({8,10,15,16}, {19}),
  ({9}, {11}), ({9,11}, {16}), ({9,11,16}, {17}), ({9,11,16,17}, {20}),
  ({0}, {10}), ({0,10}, {12}), ({0,10,12}, {17}), ({0,10,12,17}, {18}),
  ({1}, {11}), ({1,11}, {13}), ({1,11,13}, {18}), ({1,11,13,18}, {19}),
  ({2}, {12}), ({2,12}, {14}), ({2,12,14}, {19}), ({2,12,14,19}, {20}),
  ({0}, {3}), ({0,3}, {13}), ({0,3,13}, {15}), ({0,3,13,15}, {20})]

set_option maxRecDepth 8192 in
private theorem attained : schedule.length = 76 ∧
    ∀ t ∈ columns, t ∈ schedule.foldl step base := by decide +kernel

set_option maxRecDepth 8192 in
theorem optimum (n : Nat) : (∃ l : List (W × W), l.length ≤ n ∧
    ∀ t ∈ columns, t ∈ l.foldl step base) ↔ 76 ≤ n := by
  constructor
  · rintro ⟨l,hl,outputs⟩
    obtain ⟨g,h,le⟩ := execute l Built.start
    exact (lower h outputs).trans ((by simpa using le : g.length ≤ l.length).trans hl)
  · intro hn
    exact ⟨schedule,attained.1.le.trans hn,attained.2⟩

end PEqualNP.Research.PuncturedPlaneOrNetwork

open PEqualNP.Research.PuncturedPlaneOrNetwork in
theorem PEqualNP.Research.PuncturedPlaneOrNetwork :
    ∀ n : Nat, (∃ l : List (W × W), l.length ≤ n ∧ ∀ t ∈ columns, t ∈ l.foldl step base) ↔
      76 ≤ n := optimum
