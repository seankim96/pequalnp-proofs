import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlanePointSevenOrBudget.Core
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

end PEqualNP.Research.PlanePointSevenOrBudget.Core
open PEqualNP.Research.PlanePointSevenOrBudget.Core in
theorem PEqualNP.Research.PlanePointSevenOrBudget.packing : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (o : Nat),
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
namespace PEqualNP.Research.PlanePointSevenOrBudget.Instance
open Core
def flag (i : Fin 19) : Nat := (#[8194, 16386, 32772, 32776, 32800, 34816, 65600, 131073, 131088, 131200, 262146, 524352, 1048832, 1049600, 2097664, 4194816, 8388672, 16777218, 33558528] : Array Nat)[i.val]!
def negative : Nat := 1217090
def initial : List Column :=
  let raw := List.ofFn (fun i : Fin 26 => fun r : Nat => r.testBit i.val)
  ([(false,0,1), (false,3,9), (true,15,27), (true,17,26), (true,13,26), (true,13,27), (false,2,6), (true,1,24), (true,15,32), (true,25,32), (true,0,17), (true,0,23), (true,0,25), (false,17,19), (false,20,24)] : List Gate).foldl step raw
private def projected : Array Column := #[(fun t : Nat => t.testBit 0),
(fun t : Nat => t.testBit 1),
(fun t : Nat => t.testBit 2),
(fun t : Nat => t.testBit 3),
(fun t : Nat => t.testBit 4),
(fun t : Nat => t.testBit 5),
(fun t : Nat => t.testBit 6),
(fun t : Nat => t.testBit 7),
(fun t : Nat => t.testBit 8),
(fun t : Nat => t.testBit 9),
(fun t : Nat => t.testBit 10),
(fun t : Nat => t.testBit 11),
(fun t : Nat => t.testBit 12),
(fun t : Nat => t.testBit 13),
(fun t : Nat => t.testBit 14),
(fun t : Nat => t.testBit 15),
(fun t : Nat => t.testBit 16),
(fun t : Nat => t.testBit 17),
(fun t : Nat => t.testBit 18),
(fun t : Nat => t.testBit 19),
(fun t : Nat => t.testBit 20),
(fun t : Nat => t.testBit 21),
(fun t : Nat => t.testBit 22),
(fun t : Nat => t.testBit 23),
(fun t : Nat => t.testBit 24),
(fun t : Nat => t.testBit 25),
(mix false (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 1)),
(mix false (fun t : Nat => t.testBit 3) (fun t : Nat => t.testBit 9)),
(mix true (fun t : Nat => t.testBit 15) (mix false (fun t : Nat => t.testBit 3) (fun t : Nat => t.testBit 9))),
(mix true (fun t : Nat => t.testBit 17) (mix false (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 1))),
(mix true (fun t : Nat => t.testBit 13) (mix false (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 1))),
(mix true (fun t : Nat => t.testBit 13) (mix false (fun t : Nat => t.testBit 3) (fun t : Nat => t.testBit 9))),
(mix false (fun t : Nat => t.testBit 2) (fun t : Nat => t.testBit 6)),
(mix true (fun t : Nat => t.testBit 1) (fun t : Nat => t.testBit 24)),
(mix true (fun t : Nat => t.testBit 15) (mix false (fun t : Nat => t.testBit 2) (fun t : Nat => t.testBit 6))),
(mix true (fun t : Nat => t.testBit 25) (mix false (fun t : Nat => t.testBit 2) (fun t : Nat => t.testBit 6))),
(mix true (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 17)),
(mix true (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 23)),
(mix true (fun t : Nat => t.testBit 0) (fun t : Nat => t.testBit 25)),
(mix false (fun t : Nat => t.testBit 17) (fun t : Nat => t.testBit 19)),
(mix false (fun t : Nat => t.testBit 20) (fun t : Nat => t.testBit 24))]
private def col (i : Fin 41) : Column := projected[i.val]!
private theorem physical (i : Fin 41) : wire initial i.val = col i := by fin_cases i <;> rfl
private def small (i : Fin 41) := col i negative = false →
    (Finset.univ.filter (fun p : Fin 19 => col i (flag p))).card ≤ 1
private theorem cert0 : small 0 := by unfold small; decide +kernel
private theorem cert1 : small 1 := by unfold small; decide +kernel
private theorem cert2 : small 2 := by unfold small; decide +kernel
private theorem cert3 : small 3 := by unfold small; decide +kernel
private theorem cert4 : small 4 := by unfold small; decide +kernel
private theorem cert5 : small 5 := by unfold small; decide +kernel
private theorem cert6 : small 6 := by unfold small; decide +kernel
private theorem cert7 : small 7 := by unfold small; decide +kernel
private theorem cert8 : small 8 := by unfold small; decide +kernel
private theorem cert9 : small 9 := by unfold small; decide +kernel
private theorem cert10 : small 10 := by unfold small; decide +kernel
private theorem cert11 : small 11 := by unfold small; decide +kernel
private theorem cert12 : small 12 := by unfold small; decide +kernel
private theorem cert13 : small 13 := by unfold small; decide +kernel
private theorem cert14 : small 14 := by unfold small; decide +kernel
private theorem cert15 : small 15 := by unfold small; decide +kernel
private theorem cert16 : small 16 := by unfold small; decide +kernel
private theorem cert17 : small 17 := by unfold small; decide +kernel
private theorem cert18 : small 18 := by unfold small; decide +kernel
private theorem cert19 : small 19 := by unfold small; decide +kernel
private theorem cert20 : small 20 := by unfold small; decide +kernel
private theorem cert21 : small 21 := by unfold small; decide +kernel
private theorem cert22 : small 22 := by unfold small; decide +kernel
private theorem cert23 : small 23 := by unfold small; decide +kernel
private theorem cert24 : small 24 := by unfold small; decide +kernel
private theorem cert25 : small 25 := by unfold small; decide +kernel
private theorem cert26 : small 26 := by unfold small; decide +kernel
private theorem cert27 : small 27 := by unfold small; decide +kernel
private theorem cert28 : small 28 := by unfold small; decide +kernel
private theorem cert29 : small 29 := by unfold small; decide +kernel
private theorem cert30 : small 30 := by unfold small; decide +kernel
private theorem cert31 : small 31 := by unfold small; decide +kernel
private theorem cert32 : small 32 := by unfold small; decide +kernel
private theorem cert33 : small 33 := by unfold small; decide +kernel
private theorem cert34 : small 34 := by unfold small; decide +kernel
private theorem cert35 : small 35 := by unfold small; decide +kernel
private theorem cert36 : small 36 := by unfold small; decide +kernel
private theorem cert37 : small 37 := by unfold small; decide +kernel
private theorem cert38 : small 38 := by unfold small; decide +kernel
private theorem cert39 : small 39 := by unfold small; decide +kernel
private theorem cert40 : small 40 := by unfold small; decide +kernel
private theorem checked (i : Fin 41) : small i := by
  fin_cases i
  · exact cert0
  · exact cert1
  · exact cert2
  · exact cert3
  · exact cert4
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
  · exact cert11
  · exact cert12
  · exact cert13
  · exact cert14
  · exact cert15
  · exact cert16
  · exact cert17
  · exact cert18
  · exact cert19
  · exact cert20
  · exact cert21
  · exact cert22
  · exact cert23
  · exact cert24
  · exact cert25
  · exact cert26
  · exact cert27
  · exact cert28
  · exact cert29
  · exact cert30
  · exact cert31
  · exact cert32
  · exact cert33
  · exact cert34
  · exact cert35
  · exact cert36
  · exact cert37
  · exact cert38
  · exact cert39
  · exact cert40
private theorem start (i : Nat) (off : wire initial i negative = false) :
    (Finset.univ.filter (fun p : Fin 19 => wire initial i (flag p))).card ≤ 1 := by
  by_cases hi : i < 41
  · have e : wire initial i = col ⟨i,hi⟩ := physical ⟨i,hi⟩
    rw [e] at off ⊢
    exact checked ⟨i,hi⟩ off
  · have e : wire initial i = fun _ => false := List.getD_eq_default _ _ (show initial.length ≤ i by change 41 ≤ i; omega)
    simp [e]
private theorem bound (gs : List Gate) (s : List Column) (q : Nat) :
    (gs.foldl (fun z g => (step z.1 g,z.2+charge negative z.1 g)) (s,q)).2 ≤ q+gs.countP (fun g => !g.1) := by
  induction gs generalizing s q with
  | nil => simp
  | cons g gs ih =>
    have h := ih (step s g) (q+charge negative s g)
    cases op : g.1 <;> cases v : newWire s g negative <;>
      simp [List.countP_cons,charge,op,v] at h ⊢ <;> omega
end PEqualNP.Research.PlanePointSevenOrBudget.Instance
open PEqualNP.Research.PlanePointSevenOrBudget.Core PEqualNP.Research.PlanePointSevenOrBudget.Instance in
theorem PEqualNP.Research.PlanePointSevenOrBudget : ∀ (gs : List Gate) (o : Nat),
    (∀ p : Fin 19, wire (gs.foldl step initial) o (flag p) = true) →
    wire (gs.foldl step initial) o negative = false →
    18 ≤ gs.countP (fun g => !g.1) := by
  intro gs o hp hn
  have a := PEqualNP.Research.PlanePointSevenOrBudget.packing 19 flag negative initial gs o start hp hn
  have b : cost negative initial gs ≤ gs.countP (fun g => !g.1) := by simpa only [cost,Nat.zero_add] using bound gs initial 0
  omega
