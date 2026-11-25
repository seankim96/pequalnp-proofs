import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Research.NineEdgeRectangles

open PEqualNP.CircuitLowerBounds

abbrev Block := Nat × Nat

def edges : List (Nat × Nat) :=
  [(0,4),(1,5),(0,6),(2,6),(3,6),(0,7),(2,7),(4,7),(6,7)]

-- Each copy charges one unit. A multiply covered edge may be charged to any one block.
def tickets : List (Nat × Nat) :=
  [(0,4),(0,4),(1,5),(1,5),(2,6),(3,6),(3,6),(0,7),(2,7),(2,7),(4,7),(6,7)]

def hit (r : Block) (e : Nat × Nat) : Bool :=
  (r.1.testBit e.1 && r.2.testBit e.2) || (r.1.testBit e.2 && r.2.testBit e.1)

def vertices := List.range 8

def cost (r : Block) := vertices.countP r.1.testBit + vertices.countP r.2.testBit

def legal (r : Block) := vertices.all fun i =>
  !r.1.testBit i || vertices.all fun j =>
    !r.2.testBit j || edges.contains (min i j, max i j)

def certificates (r : Block) :=
  !legal r || decide (tickets.countP (hit r) ≤ cost r)

def masks : List Nat := [0, 1, 2, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 32, 64, 65, 68, 69, 80, 81, 84, 85, 128, 129, 132, 133, 136, 137, 140, 141, 144, 192, 208]

def compatible (a j : Nat) := vertices.all fun i =>
  !a.testBit i || edges.contains (min i j, max i j)

set_option maxRecDepth 4096 in
theorem admissible : (List.range 256).all (fun a => vertices.all fun j =>
    !compatible a j || masks.contains a) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem smallCheck : masks.all (fun a => masks.all fun b => certificates (a,b)) = true := by
  decide +kernel

theorem charge (r : Block) (ha : r.1 < 256) (hb : r.2 < 256) (hl : legal r = true) :
    tickets.countP (hit r) ≤ cost r := by
  by_cases zero : tickets.countP (hit r) = 0
  · omega
  have live : ∃ e ∈ tickets, hit r e = true := by
    by_contra! h
    exact zero (List.countP_eq_zero.mpr h)
  obtain ⟨e,he,hh⟩ := live
  have coords : ∀ e ∈ tickets, e.1 ∈ vertices ∧ e.2 ∈ vertices := by decide
  obtain ⟨ei,ej⟩ := coords e he
  have pair : ∃ i ∈ vertices, ∃ j ∈ vertices, r.1.testBit i = true ∧ r.2.testBit j = true := by
    rcases Bool.or_eq_true_iff.mp hh with h|h
    · exact ⟨_,ei,_,ej,by simpa only [Bool.and_eq_true] using h⟩
    · exact ⟨_,ej,_,ei,by simpa only [Bool.and_eq_true] using h⟩
  obtain ⟨i,hi,j,hj,h1,h2⟩ := pair
  have ok : ∀ a ∈ vertices, ∀ b ∈ vertices, r.1.testBit a = true → r.2.testBit b = true →
      edges.contains (min a b,max a b) = true := by
    intro a ha b hb hA hB
    have t := List.all_eq_true.mp hl a ha
    simp [hA] at t
    have v := t b hb
    simpa [hB] using v
  have ca : compatible r.1 j = true := by
    apply List.all_eq_true.mpr
    intro a ha
    cases h : r.1.testBit a
    · simp
    · simpa [h] using ok a ha j hj h h2
  have cb : compatible r.2 i = true := by
    apply List.all_eq_true.mpr
    intro b hb
    cases h : r.2.testBit b
    · simp
    · simpa [h,min_comm b i,max_comm b i] using ok i hi b hb h1 h
  have get : ∀ a, a < 256 → ∀ j ∈ vertices, compatible a j = true → a ∈ masks := by
    intro a ha j hj h
    have v := List.all_eq_true.mp (List.all_eq_true.mp admissible a (List.mem_range.mpr ha)) j hj
    simpa [h] using v
  have checked := List.all_eq_true.mp (List.all_eq_true.mp smallCheck _ (get _ ha _ hj ca)) _ (get _ hb _ hi cb)
  simpa [certificates, hl] using checked

theorem splitCharge {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] at * <;> omega

theorem unionCharge (rs : List Block)
    (ok : ∀ r ∈ rs, r.1 < 256 ∧ r.2 < 256 ∧ legal r = true) :
    tickets.countP (fun e => rs.any (fun r => hit r e)) ≤ (rs.map cost).sum := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    obtain ⟨ha,hb,hl⟩ := ok r (by simp)
    have left := charge r ha hb hl
    have right := ih (fun s hs => ok s (by simp [hs]))
    have both := splitCharge tickets (hit r) (fun e => rs.any (fun s => hit s e))
    simpa only [List.any_cons, List.map_cons, List.sum_cons] using
      both.trans (Nat.add_le_add left right)

-- Each nonempty rectangle contributes |A|+|B|-1 gates internally.
-- Joining k rectangles by k-1 binary OR gates gives total cost minus one.
theorem rectangleLower (rs : List Block)
    (ok : ∀ r ∈ rs, r.1 < 256 ∧ r.2 < 256 ∧ legal r = true)
    (cover : ∀ e ∈ edges, rs.any (fun r => hit r e) = true) :
    11 ≤ (rs.map cost).sum - 1 := by
  have sub : ∀ e ∈ tickets, e ∈ edges := by decide
  have h := unionCharge rs ok
  have same : tickets.countP (fun e => rs.any (fun r => hit r e)) = tickets.length :=
    List.countP_eq_length.mpr (fun e he => cover e (sub e he))
  rw [same] at h
  change 12 ≤ _ at h
  omega

def cover11 : List Block := [(2,32),(12,64),(5,128),(80,129)]
theorem sharp : (∀ r ∈ cover11, legal r = true) ∧
    (∀ e ∈ edges, cover11.any (fun r => hit r e) = true) ∧
    (cover11.map cost).sum - 1 = 11 := by decide

end PEqualNP.Research.NineEdgeRectangles
