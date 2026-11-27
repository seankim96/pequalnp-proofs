import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

namespace PEqualNP.Research.PlaneInitialCoverOrBudget.Core
abbrev Column := Nat → Bool
abbrev Gate := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def mix (op : Bool) (x y : Column) : Column := fun r => if op then x r && y r else x r || y r
def newWire (s : List Column) (g : Gate) := mix g.1 (wire s g.2.1) (wire s g.2.2)
def step (s : List Column) (g : Gate) := s ++ [newWire s g]
variable {m : Nat} (flag : Fin m → Nat) (t : Nat)
def supp (x : Column) : Finset (Fin m) :=
  if x t then ∅ else Finset.univ.filter (fun i => x (flag i))
def charge {m : Nat} (flag : Fin m → Nat) (t : Nat) (s : List Column) (g : Gate) : Nat :=
  if g.1 then 0 else
    if supp flag t (newWire s g) ⊆ supp flag t (wire s g.2.1) then 0 else
    if supp flag t (newWire s g) ⊆ supp flag t (wire s g.2.2) then 0 else 1
def cost {m : Nat} (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) : Nat :=
  (gs.foldl (fun z g => (step z.1 g,z.2 + charge flag t z.1 g)) (s,0)).2
private def Count (initial s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, ∃ U : Finset Nat, U.card ≤ q + W.card ∧
    W.biUnion (fun j => supp flag t (wire s j)) ⊆ U.biUnion (fun j => supp flag t (wire initial j))

private theorem cutOr (x y : Column) : supp flag t (mix false x y) ⊆ supp flag t x ∪ supp flag t y := by
  cases hx : x t <;> cases hy : y t <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp flag t (mix true x y) ⊆ supp flag t (if x t then y else x) := by
  cases hx : x t <;> cases hy : y t <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {initial : List Column} {s : List Column} {q c : Nat} (h : Count flag t initial s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp flag t v ⊆ parents.biUnion (fun j => supp flag t (s.getD j (fun _ => false)))) : Count flag t initial (s ++ [v]) (q+c) := by
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
    obtain ⟨I,hI,hU⟩ := h U
    refine ⟨I, ?_, hs.trans hU⟩
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
    change ∃ I : Finset Nat, I.card ≤ q+c+W.card ∧ _
    obtain ⟨I,hi,hs⟩ := h W
    exact ⟨I, by omega, eq.le.trans hs⟩


private theorem appendGate {initial : List Column} {s : List Column} {q : Nat} (h : Count flag t initial s q) (g : Gate) :
    Count flag t initial (step s g) (q+charge flag t s g) := by
  obtain ⟨op,i,j⟩ := g
  cases op
  · by_cases left : supp flag t (newWire s (false,i,j)) ⊆ supp flag t (wire s i)
    · have z : charge flag t s (false,i,j) = 0 := by simp [charge,left]
      rw [z]
      apply grow flag t h _ {i} (by simp)
      simpa only [Finset.singleton_biUnion,wire] using left
    · by_cases right : supp flag t (newWire s (false,i,j)) ⊆ supp flag t (wire s j)
      · have z : charge flag t s (false,i,j) = 0 := by simp [charge,left,right]
        rw [z]
        apply grow flag t h _ {j} (by simp)
        simpa only [Finset.singleton_biUnion,wire] using right
      · have z : charge flag t s (false,i,j) = 1 := by simp [charge,left,right]
        rw [z]
        apply grow flag t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
        simpa [newWire,wire] using cutOr flag t (wire s i) (wire s j)
  · change Count flag t initial _ (q+0)
    let k := if wire s i t then j else i
    apply grow flag t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd flag t (wire s i) (wire s j)
    change _ ⊆ supp flag t (wire s k)
    cases e : wire s i t <;> simpa only [newWire,k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run {initial : List Column} (gs : List Gate) (z : List Column × Nat) (h : Count flag t initial z.1 z.2) :
    Count flag t initial (gs.foldl step z.1)
      ((gs.foldl (fun z g => (step z.1 g,z.2 + charge flag t z.1 g)) z).2) := by
  induction gs generalizing z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (step z.1 g,z.2 + charge flag t z.1 g) (appendGate flag t h g)

end PEqualNP.Research.PlaneInitialCoverOrBudget.Core
open PEqualNP.Research.PlaneInitialCoverOrBudget.Core in
theorem PEqualNP.Research.PlaneInitialCoverOrBudget : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (W : Finset Nat),
    ∃ U : Finset Nat, U.card ≤ cost flag t s gs + W.card ∧
      W.biUnion (fun j => supp flag t (wire (gs.foldl step s) j)) ⊆
        U.biUnion (fun j => supp flag t (wire s j)) := by
  intro m flag t s gs W
  have init : Count flag t s s 0 := by
    intro A
    exact ⟨A, by simp, Finset.Subset.rfl⟩
  exact run flag t gs (s,0) init W
