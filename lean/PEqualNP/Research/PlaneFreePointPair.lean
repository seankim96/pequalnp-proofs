import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Fin.Basic

namespace PEqualNP.Research.PlaneFreePointPair
abbrev Vertex := Fin 13
def differences : Finset Vertex := {0,1,3,9}
def incident (p w : Vertex) : Prop := p-w ∈ differences
instance (p w : Vertex) : Decidable (incident p w) := by unfold incident; infer_instance
def flags : Finset (Vertex × Vertex) := Finset.univ.filter fun e => incident e.1 e.2
def quad (Q : Finset Vertex) := Q.card = 4 ∧
  ∀ w : Vertex, (Q.filter fun p => incident p w).card ≤ 2
instance (Q : Finset Vertex) : Decidable (quad Q) := by unfold quad; infer_instance

private def rows : Array (Finset Vertex) := #[
{0,1,2,5},
{0,3,5,6},
{0,1,4,6},
{0,1,2,5},
{0,1,2,5},
{0,2,3,4},
{0,1,4,8},
{0,1,2,5},
{0,1,2,5},
{0,1,2,6},
{0,1,2,5},
{0,2,3,4},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{0,1,4,6},
{0,1,2,5},
{1,2,3,6},
{0,1,2,5},
{0,1,4,8},
{0,1,2,5},
{0,1,2,5},
{0,1,2,6},
{1,2,3,7},
{0,1,2,5},
{1,3,4,5},
{2,4,5,6},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{1,2,3,6},
{0,2,3,4},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{0,1,2,6},
{1,2,3,7},
{0,2,3,4},
{0,1,2,5},
{0,1,2,5},
{0,3,5,6},
{0,1,2,5},
{0,1,2,5},
{1,2,3,6},
{0,2,3,4},
{0,3,4,8},
{0,1,2,5},
{0,2,3,6},
{0,2,3,4},
{1,2,3,7},
{0,2,3,4},
{1,3,4,5},
{2,4,5,6},
{0,1,2,5},
{0,1,4,6},
{0,1,2,5},
{0,1,2,5},
{0,2,3,4},
{0,1,4,8},
{0,1,4,6},
{0,1,2,5},
{0,1,4,6},
{1,3,4,5},
{0,2,3,4},
{1,3,4,5},
{2,4,5,6},
{0,3,5,6},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{0,1,5,10},
{0,1,2,5},
{0,1,2,5},
{0,1,2,5},
{1,2,5,7},
{0,2,5,6},
{1,3,4,5},
{2,4,5,6},
{0,3,5,6},
{0,1,4,6},
{0,1,2,5},
{1,2,3,6},
{0,1,2,5},
{0,1,2,5},
{0,1,2,6},
{0,1,2,6},
{0,1,2,6},
{0,1,2,5},
{0,2,3,6},
{1,3,6,7},
{2,4,7,8},
{0,3,6,7},
{0,1,6,7},
{0,1,2,7},
{0,1,2,5},
{0,2,3,7},
{0,1,2,5},
{0,1,2,5},
{0,1,2,7},
{0,1,2,7},
{1,2,3,7},
{0,1,2,5},
{1,3,4,7},
{2,4,5,8},
{0,3,5,8},
{0,1,4,8},
{0,1,7,8},
{1,2,3,8},
{0,1,2,5},
{0,1,4,8},
{0,1,2,5},
{0,1,2,5},
{0,1,4,8},
{1,2,3,8},
{0,3,4,8},
{0,1,2,5},
{0,1,2,5},
{0,5,6,9},
{0,4,6,9},
{0,2,5,9},
{1,2,8,9},
{0,2,4,9},
{0,1,2,5},
{0,2,4,9},
{0,1,2,5},
{0,1,2,5},
{1,2,5,9},
{0,2,4,9},
{1,4,5,9},
{2,5,6,10},
{0,1,2,5},
{0,1,7,10},
{0,1,5,10},
{1,3,6,10},
{0,2,3,10},
{0,1,5,10},
{0,1,2,5},
{0,1,5,10},
{0,1,2,5},
{0,1,2,5},
{0,2,3,10},
{1,3,5,10},
{2,4,6,11},
{0,3,7,11},
{0,1,2,5},
{0,1,2,11},
{1,2,6,11},
{0,2,4,11},
{0,1,4,11},
{0,1,2,11},
{0,1,2,5},
{0,1,2,11},
{0,1,2,5},
{0,1,2,5},
{1,3,4,11},
{2,4,5,12},
{0,3,5,12},
{0,1,4,12},
{0,1,2,5},
{1,2,3,12},
{0,3,7,12},
{0,1,4,12},
{0,1,4,12},
{0,1,5,12},
{0,1,2,5},
{1,2,3,12},
{0,1,2,5},
{0,1,2,5}]
private def row (p w : Vertex) := rows[13*p.val+w.val]!
private theorem negatives : ∀ p w : Vertex, ¬ incident p w →
    quad (row p w) ∧ p ∈ row p w ∧ ∀ q ∈ row p w, ¬ incident q w := by decide +kernel

private theorem unique_line : ∀ p q : Vertex, p ≠ q →
    (Finset.univ.filter fun w => incident p w ∧ incident q w).card ≤ 1 := by
  decide +kernel

private theorem degrees : ∀ x : Vertex,
    (Finset.univ.filter fun w => incident x w).card = 4 ∧
    (Finset.univ.filter fun p => incident p x).card = 4 := by decide +kernel

private theorem rectangle_bounds (A B : Finset Vertex) (ha : A.Nonempty) (hb : B.Nonempty)
    (edges : ∀ p ∈ A, ∀ w ∈ B, incident p w) :
    A.card * B.card ≤ 4 ∧ A.card * B.card + 1 = A.card + B.card := by
  by_cases a : A.card = 1
  · obtain ⟨p,hp⟩ := ha
    have sub : B ⊆ Finset.univ.filter (fun w => incident p w) := fun w hw =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges p hp w hw⟩
    have bound := (Finset.card_le_card sub).trans (degrees p).1.le
    simp [a,bound,Nat.add_comm]
  · have two : 1 < A.card := by have := Finset.card_pos.mpr ha; omega
    obtain ⟨p,hp,q,hq,diff⟩ := Finset.one_lt_card.mp two
    have sub : B ⊆ Finset.univ.filter (fun w => incident p w ∧ incident q w) := fun w hw =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges p hp w hw,edges q hq w hw⟩
    have le := (Finset.card_le_card sub).trans (unique_line p q diff)
    have b : B.card = 1 := by have := Finset.card_pos.mpr hb; omega
    obtain ⟨w,hw⟩ := hb
    have sub' : A ⊆ Finset.univ.filter (fun p => incident p w) := fun p hp =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges p hp w hw⟩
    have bound := (Finset.card_le_card sub').trans (degrees w).2.le
    simp [b,bound]


def discount (A : Finset Vertex) (a b : Vertex) : Nat := if a ∈ A ∧ b ∈ A then 1 else 0
def cost (A B : Finset Vertex) (a b : Vertex) := A.card + B.card - discount A a b

-- A term fires on Q when its point side meets Q and some selected line misses Q.
-- The free pair counts as one point leaf wherever both endpoints occur.
set_option maxRecDepth 8192 in
theorem lower {k : Nat} (A B : Fin k → Finset Vertex) (a b : Vertex) (ab : a ≠ b)
    (nonempty : ∀ t, (A t).Nonempty ∧ (B t).Nonempty)
    (safe : ∀ t Q, quad Q → ∀ p ∈ A t, p ∈ Q → ∀ w ∈ B t, ∃ q ∈ Q, incident q w)
    (cover : ∀ p w, incident p w → ∃ t, p ∈ A t ∧ w ∈ B t) :
    63 ≤ (∑ t, cost (A t) (B t) a b) - 1 := by
  have good (t : Fin k) (p) (hp : p ∈ A t) (w) (hw : w ∈ B t) : incident p w := by
    by_contra hn
    obtain ⟨hq, hmem, hmiss⟩ := negatives p w hn
    obtain ⟨q, hq', hit⟩ := safe t (row p w) hq p hp hmem w hw
    exact hmiss q hq' hit
  have common : ∀ p q : Vertex, p ≠ q → ∃ w : Vertex, (incident p w ∧ incident q w) ∧
      ∀ v : Vertex, incident p v ∧ incident q v → v = w := by decide +kernel
  obtain ⟨u,hu,uniq⟩ := common a b ab
  let R (t : Fin k) := A t ×ˢ B t
  have facts t := rectangle_bounds (A t) (B t) (nonempty t).1 (nonempty t).2 (good t)
  have whole : flags ⊆ Finset.univ.biUnion R := by
    intro e he
    obtain ⟨t,hp,hw⟩ := cover _ _ (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,Finset.mem_product.mpr ⟨hp,hw⟩⟩
  have nf : flags.card = 52 := by decide +kernel
  have cap (t) : (R t).card ≤ 4 := by simpa [R] using (facts t).1
  have count : 52 ≤ 4*k := calc
    52 = flags.card := nf.symm
    _ ≤ _ := Finset.card_le_card whole
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin k, 4 := Finset.sum_le_sum (fun t _ => cap t)
    _ = _ := by simp [Nat.mul_comm]
  let e := (a,u)
  have he : e ∈ flags := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu.1⟩
  have remaining : flags.erase e ⊆ Finset.univ.biUnion (fun t => (R t).erase e) := by
    intro x hx
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
    obtain ⟨t,ht,h⟩ := Finset.mem_biUnion.mp (whole mem)
    exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_erase.mpr ⟨ne,h⟩⟩
  have each (t) : ((R t).erase e).card + 1 ≤ cost (A t) (B t) a b := by
    have area : (R t).card + 1 = (A t).card + (B t).card := by simpa [R] using (facts t).2
    by_cases h : a ∈ A t ∧ b ∈ A t
    · obtain ⟨w, hw⟩ := (nonempty t).2
      have eq := uniq w ⟨good t _ h.1 _ hw,good t _ h.2 _ hw⟩
      have hin : e ∈ R t := Finset.mem_product.mpr ⟨h.1,show u ∈ B t from eq ▸ hw⟩
      have pos := Finset.card_pos.mpr ⟨e,hin⟩
      rw [Finset.card_erase_of_mem hin]
      simp [cost,discount,h]
      omega
    · have le := Finset.card_le_card (Finset.erase_subset e (R t))
      simp [cost,discount,h]
      omega
  have many := (Finset.card_le_card remaining).trans Finset.card_biUnion_le
  rw [Finset.card_erase_of_mem he,nf] at many
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => each t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at sum
  omega


def linePoints (w : Vertex) := Finset.univ.filter fun p => incident p w

theorem concrete :
    (∀ w : Vertex, (linePoints w).Nonempty) ∧
    (∀ p w : Vertex, incident p w → p ∈ linePoints w) ∧
    (∀ w Q, quad Q → ∀ p ∈ linePoints w, p ∈ Q → ∃ q ∈ Q, incident q w) ∧
    (∑ w : Vertex, cost (linePoints w) {w} 0 1) - 1 = 63 := by
  refine ⟨by decide +kernel, ?_, ?_, by decide +kernel⟩
  · intro p w h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro w Q _ p hp hin
    exact ⟨p,hin,(Finset.mem_filter.mp hp).2⟩

end PEqualNP.Research.PlaneFreePointPair

theorem PEqualNP.Research.PlaneFreePointPair : ∀ (k : Nat) (A B : Fin k → Finset (Fin 13)) (a b : Fin 13), a ≠ b →
    let D : Finset (Fin 13) := {0,1,3,9}
    (∀ t, (A t).Nonempty ∧ (B t).Nonempty) →
    (∀ t (Q : Finset (Fin 13)), (Q.card = 4 ∧ ∀ w : Fin 13,
        (Q.filter fun p => p-w ∈ D).card ≤ 2) →
      ∀ p ∈ A t, p ∈ Q → ∀ w ∈ B t, ∃ q ∈ Q, q-w ∈ D) →
    (∀ p w : Fin 13, p-w ∈ D → ∃ t, p ∈ A t ∧ w ∈ B t) →
    63 ≤ (∑ t, ((A t).card + (B t).card - (if a ∈ A t ∧ b ∈ A t then 1 else 0))) - 1 := by
  intro k A B a b ab
  exact PEqualNP.Research.PlaneFreePointPair.lower A B a b ab
