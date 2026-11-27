import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneNegativeOrBudget.Core
abbrev Column := Nat → Bool
abbrev Gate := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def mix (op : Bool) (x y : Column) : Column := fun r => if op then x r && y r else x r || y r
def newWire (s : List Column) (g : Gate) := mix g.1 (wire s g.2.1) (wire s g.2.2)
def step (s : List Column) (g : Gate) := s ++ [newWire s g]
def charge (t : Nat) (s : List Column) (g : Gate) := (!g.1 && !(newWire s g t)).toNat
def cost (t : Nat) (s : List Column) (gs : List Gate) : Nat :=
  (gs.foldl (fun z g => (step z.1 g,z.2 + charge t z.1 g)) (s,0)).2
variable {m : Nat} (flag : Fin m → Nat) (t : Nat)
private def supp (x : Column) : Finset (Fin m) :=
  if x t then ∅ else Finset.univ.filter (fun i => x (flag i))
private def Count (s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp flag t (s.getD j (fun _ => false)))).card ≤ q + W.card

private theorem cutOr (x y : Column) : supp flag t (mix false x y) ⊆ supp flag t x ∪ supp flag t y := by
  cases hx : x t <;> cases hy : y t <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp flag t (mix true x y) ⊆ supp flag t (if x t then y else x) := by
  cases hx : x t <;> cases hy : y t <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Column} {q c : Nat} (h : Count flag t s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp flag t v ⊆ parents.biUnion (fun j => supp flag t (s.getD j (fun _ => false)))) : Count flag t (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp flag t ((s ++ [v]).getD j (fun _ => false))) ⊆
        U.biUnion (fun j => supp flag t (s.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp flag t v := by simpa using hij
        obtain ⟨a,ha,hai⟩ := Finset.mem_biUnion.mp (sub hv)
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_right _ ha,hai⟩
      · have hd : (s ++ [v]).getD j (fun _ => false) = s.getD j (fun _ => false) := by
          by_cases hj : j < s.length
          · exact List.getD_append _ _ _ _ hj
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩),hd ▸ hij⟩
    have hc := Finset.card_union_le (W.erase s.length) parents
    rw [Finset.card_erase_of_mem incl] at hc
    have hw := Finset.card_pos.mpr ⟨_,incl⟩
    have hU := h U
    have := Finset.card_le_card hs
    change U.card ≤ _ at hc
    omega
  · have eq : W.biUnion (fun j => supp flag t ((s ++ [v]).getD j (fun _ => false))) =
        W.biUnion (fun j => supp flag t (s.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega


private theorem appendGate {s : List Column} {q : Nat} (h : Count flag t s q) (g : Gate) :
    Count flag t (step s g) (q+charge t s g) := by
  obtain ⟨op,i,j⟩ := g
  cases op
  · by_cases on : newWire s (false,i,j) t = true
    · have z : charge t s (false,i,j) = 0 := by simp [charge,on]
      rw [z]
      apply grow flag t h _ ∅ (by simp)
      simp [supp,on]
    · have z : charge t s (false,i,j) = 1 := by simp [charge,Bool.eq_false_iff.mpr on]
      rw [z]
      apply grow flag t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
      simpa [newWire,wire] using cutOr flag t (wire s i) (wire s j)
  · change Count flag t _ (q+0)
    let k := if wire s i t then j else i
    apply grow flag t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd flag t (wire s i) (wire s j)
    change _ ⊆ supp flag t (wire s k)
    cases e : wire s i t <;> simpa only [newWire,k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) (z : List Column × Nat) (h : Count flag t z.1 z.2) :
    Count flag t (gs.foldl step z.1)
      ((gs.foldl (fun z g => (step z.1 g,z.2 + charge t z.1 g)) z).2) := by
  induction gs generalizing z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (step z.1 g,z.2 + charge t z.1 g) (appendGate flag t h g)

end PEqualNP.Research.PlaneNegativeOrBudget.Core
open PEqualNP.Research.PlaneNegativeOrBudget.Core in
theorem PEqualNP.Research.PlaneNegativeOrBudget : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (o : Nat),
    (∀ i : Nat, wire s i t = false → (Finset.univ.filter (fun p : Fin m => wire s i (flag p))).card ≤ 1) →
    (∀ p : Fin m, wire (gs.foldl step s) o (flag p) = true) →
    wire (gs.foldl step s) o t = false →
    m ≤ 1 + cost t s gs := by
  intro m flag t s gs o start hp hn
  have init : Count flag t s 0 := by
    intro W
    apply le_trans Finset.card_biUnion_le
    rw [Nat.zero_add,Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro i _
    change (supp flag t (wire s i)).card ≤ 1
    cases eq : wire s i t
    · simpa [supp,eq] using start i eq
    · simp [supp,eq]
  have bound := run flag t gs (s,0) init {o}
  have full : supp flag t (wire (gs.foldl step s) o) = Finset.univ := by
    simp [supp,hn,hp]
  simp only [Finset.singleton_biUnion,Finset.card_singleton] at bound
  change (supp flag t (wire _ o)).card ≤ cost t s gs + 1 at bound
  rw [full] at bound
  simpa [Nat.add_comm] using bound
