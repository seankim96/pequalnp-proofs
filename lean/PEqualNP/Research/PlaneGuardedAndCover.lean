import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

namespace PEqualNP.Research.PlaneGuardedAndCover.Core
abbrev Column := Nat → Bool
abbrev Gate := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def mix (op : Bool) (x y : Column) : Column := fun r => if op then x r && y r else x r || y r
def newWire (s : List Column) (g : Gate) := mix g.1 (wire s g.2.1) (wire s g.2.2)
def step (s : List Column) (g : Gate) := s ++ [newWire s g]
variable {m : Nat} (flag : Fin m → Nat) (t : Nat)
def supp (x : Column) : Finset (Fin m) :=
  if x t then Finset.univ.filter (fun i => !(x (flag i))) else ∅
def charge (t : Nat) (free : Finset Nat) (s : List Column) (g : Gate) : Nat :=
  if g.1 && newWire s g t && decide (g.2.1 ∉ free ∧ g.2.2 ∉ free) then 1 else 0
def cost (t : Nat) (free : Finset Nat) (s : List Column) (gs : List Gate) : Nat :=
  (gs.foldl (fun z g => (step z.1 g,z.2 + charge t free z.1 g)) (s,0)).2
private def Count (initial s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, ∃ U : Finset Nat, U.card ≤ q + W.card ∧
    W.biUnion (fun j => supp flag t (wire s j)) ⊆ U.biUnion (fun j => supp flag t (wire initial j))

private theorem cutUnion (x y : Column) : supp flag t (mix true x y) ⊆ supp flag t x ∪ supp flag t y := by
  cases hx : x t <;> cases hy : y t <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutSingle (x y : Column) : supp flag t (mix false x y) ⊆ supp flag t (if x t then x else y) := by
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


private theorem appendGate {initial s : List Column} {q : Nat} (free : Finset Nat)
    (hf : ∀ k ∈ free, supp flag t (wire s k) = ∅)
    (h : Count flag t initial s q) (g : Gate) :
    Count flag t initial (step s g) (q+charge t free s g) := by
  obtain ⟨op,i,j⟩ := g
  cases op
  · change Count flag t initial _ (q+0)
    let k := if wire s i t then i else j
    apply grow flag t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutSingle flag t (wire s i) (wire s j)
    change _ ⊆ supp flag t (wire s k)
    cases e : wire s i t <;> simpa only [newWire,k,e,Bool.false_eq_true,ite_false,ite_true] using hh
  · have hh := cutUnion flag t (wire s i) (wire s j)
    by_cases on : newWire s (true,i,j) t = true
    · by_cases hi : i ∈ free
      · have z : charge t free s (true,i,j) = 0 := by simp [charge,on,hi]
        rw [z]
        apply grow flag t h _ {j} (by simp)
        rw [hf i hi,Finset.empty_union] at hh
        simp only [Finset.singleton_biUnion]
        exact hh
      · by_cases hj : j ∈ free
        · have z : charge t free s (true,i,j) = 0 := by simp [charge,on,hj]
          rw [z]
          apply grow flag t h _ {i} (by simp)
          rw [hf j hj,Finset.union_empty] at hh
          simp only [Finset.singleton_biUnion]
          exact hh
        · have z : charge t free s (true,i,j) = 1 := by simp [charge,on,hi,hj]
          rw [z]
          apply grow flag t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
          simpa [newWire,wire] using hh
    · have z : charge t free s (true,i,j) = 0 := by simp [charge,on]
      rw [z]
      apply grow flag t h _ ∅ (by simp)
      simp [supp,on]


private theorem run {initial : List Column} (free : Finset Nat) (gs : List Gate) (z : List Column × Nat)
    (hf : ∀ k ∈ free, k < z.1.length ∧ supp flag t (wire z.1 k) = ∅)
    (h : Count flag t initial z.1 z.2) : Count flag t initial (gs.foldl step z.1)
      ((gs.foldl (fun z g => (step z.1 g,z.2 + charge t free z.1 g)) z).2) := by
  induction gs generalizing z with
  | nil => exact h
  | cons g gs ih =>
    have hn : ∀ k ∈ free, k < (step z.1 g).length ∧ supp flag t (wire (step z.1 g) k) = ∅ := by
      intro k hk
      obtain ⟨lt,he⟩ := hf k hk
      refine ⟨by simp [step]; omega, ?_⟩
      simpa only [step,wire,List.getD_append _ _ _ _ lt] using he
    exact ih (step z.1 g,z.2 + charge t free z.1 g) hn (appendGate flag t free (fun k hk => (hf k hk).2) h g)

end PEqualNP.Research.PlaneGuardedAndCover.Core
open PEqualNP.Research.PlaneGuardedAndCover.Core in
theorem PEqualNP.Research.PlaneGuardedAndCover : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (free : Finset Nat)
    (gs : List Gate) (W : Finset Nat),
    (∀ k ∈ free, k < s.length ∧ supp flag t (wire s k) = ∅) →
    ∃ U : Finset Nat, U.card ≤ cost t free s gs + W.card ∧
      W.biUnion (fun j => supp flag t (wire (gs.foldl step s) j)) ⊆
        U.biUnion (fun j => supp flag t (wire s j)) := by
  intro m flag t s free gs W hf
  have init : Count flag t s s 0 := fun A => ⟨A, by simp, Finset.Subset.rfl⟩
  exact run flag t free gs (s,0) hf init W
