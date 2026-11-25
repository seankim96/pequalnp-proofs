import Mathlib
import PEqualNP.Research.OrderThreePlaneControls

/-! A rectangle term is an OR of point inputs AND an OR of line inputs.
For a formula that ORs such terms together, each binary gate has a single
use. The count is the total number of literal leaves minus one. -/

namespace PEqualNP.Research.OrderThreePlaneRectangles

open OrderThreePlanePrefixData OrderThreePlaneControls
open scoped BigOperators

abbrev Vertex := Fin 13

def incident (p w : Vertex) : Prop := p - w ∈ OrderThreePlanePrefixes.differences
instance (p w : Vertex) : Decidable (incident p w) := by unfold incident; infer_instance

def flags : Finset (Vertex × Vertex) := Finset.univ.filter fun e => incident e.1 e.2

def fires (A B : Finset Vertex) (r : Row) : Prop :=
  (∃ p ∈ A, (mask r).testBit p.val = true) ∧
  (∃ w ∈ B, (mask r).testBit (13+w.val) = true)

-- A negative row containing each nonincident point-line pair.
private def indices : Array Nat := #[
  0,2,2,2,0,10,22,41,71,113,0,244,0,
  0,0,8,8,8,0,24,46,74,118,173,0,347,
  7,0,0,7,7,11,0,43,73,115,170,245,0,
  0,16,0,0,16,16,26,0,79,121,175,250,348,
  9,0,9,0,0,9,20,49,0,112,167,243,343,
  1,1,0,1,0,0,19,40,69,0,166,245,342,
  0,0,0,0,3,0,0,40,69,111,0,243,342,
  0,0,0,1,0,9,0,0,69,111,166,0,342,
  0,0,0,1,3,0,19,0,0,111,166,243,0,
  0,2,2,2,5,10,0,41,0,0,168,244,345,
  4,0,4,7,4,9,20,0,70,0,0,243,343,
  1,1,0,1,3,11,19,40,0,111,0,0,342,
  0,0,0,0,3,9,19,40,69,0,166,0,0]


private def witness (p w : Vertex) : Fin 468 :=
  Fin.ofNat 468 (indices[13*p.val+w.val]!)

private theorem contains_nonincident : ∀ p w : Vertex, ¬ incident p w →
    (mask (.inr (witness p w))).testBit p.val = true ∧
    (mask (.inr (witness p w))).testBit (13+w.val) = true := by decide +kernel

private theorem safe_edges (A B : Finset Vertex) (safe : ∀ j, ¬ fires A B (.inr j)) :
    ∀ p ∈ A, ∀ w ∈ B, incident p w := by
  intro p hp w hw
  by_contra missing
  obtain ⟨pbit,wbit⟩ := contains_nonincident p w missing
  exact safe (witness p w) ⟨⟨p,hp,pbit⟩,⟨w,hw,wbit⟩⟩

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

/-- Every formula in the stated rectangle model that passes the tests needs at least 64 gates. -/
theorem formula_lower_bound {k : Nat} (A B : Fin k → Finset Vertex)
    (nonempty : ∀ t, (A t).Nonempty ∧ (B t).Nonempty)
    (safe : ∀ t j, ¬ fires (A t) (B t) (.inr j))
    (covers : ∀ p w, incident p w → ∃ t, p ∈ A t ∧ w ∈ B t) :
    64 ≤ (∑ t, ((A t).card + (B t).card)) - 1 := by
  have each (t : Fin k) := rectangle_bounds (A t) (B t) (nonempty t).1 (nonempty t).2
    (safe_edges _ _ (safe t))
  have all : flags ⊆ Finset.univ.biUnion (fun t => (A t) ×ˢ (B t)) := by
    intro e he
    obtain ⟨t,hp,hw⟩ := covers e.1 e.2 (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,Finset.mem_product.mpr ⟨hp,hw⟩⟩
  have size : flags.card = 52 := by decide +kernel
  have area : 52 ≤ ∑ t, ((A t).card * (B t).card) := by
    calc
      52 = flags.card := size.symm
      _ ≤ _ := Finset.card_le_card all
      _ ≤ _ := Finset.card_biUnion_le
      _ = _ := by simp [Finset.card_product]
  have cap : (∑ t, ((A t).card * (B t).card)) ≤ 4 * k := by
    calc
      _ ≤ ∑ _t : Fin k, 4 := Finset.sum_le_sum (fun t _ => (each t).1)
      _ = _ := by simp [Nat.mul_comm]
  have cost : (∑ t, ((A t).card + (B t).card)) = (∑ t, ((A t).card * (B t).card)) + k := by
    calc
      _ = ∑ t, ((A t).card * (B t).card + 1) := Finset.sum_congr rfl (fun t _ => (each t).2.symm)
      _ = _ := by simp [Finset.sum_add_distrib]
  omega

end PEqualNP.Research.OrderThreePlaneRectangles
