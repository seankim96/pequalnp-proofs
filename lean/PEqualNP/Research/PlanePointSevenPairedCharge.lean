import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases


namespace PEqualNP.Research.PlanePointSevenPairedCharge.Core
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

end PEqualNP.Research.PlanePointSevenPairedCharge.Core
open PEqualNP.Research.PlanePointSevenPairedCharge.Core in
theorem PEqualNP.Research.PlanePointSevenPairedCharge.packing : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (o : Nat),
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
namespace PEqualNP.Research.PlanePointSevenPairedCharge.Instance
open Core
def flag (k : Fin 6) (i : Fin 19) : Nat :=
  ((#[#[8194, 16386, 32772, 32776, 32800, 34816, 69632, 131073, 131088, 131200, 262146, 524352, 1048832, 1049600, 2097664, 4194816, 8388672, 16777218, 33558528], #[8194, 16386, 32772, 65552, 65600, 69632, 131073, 131104, 131200, 262146, 524292, 1048584, 1048832, 1049600, 2097664, 4194816, 8390656, 16777218, 33554436], #[8194, 16386, 32772, 69632, 131073, 131088, 131104, 131200, 262146, 524292, 1048584, 1048832, 1049600, 2097664, 4194816, 8388672, 8390656, 16777218, 33554436], #[8194, 16386, 32772, 65552, 69632, 131073, 131104, 131200, 262146, 524292, 1048584, 1048832, 1049600, 2097664, 4194816, 8388672, 8390656, 16777218, 33554436], #[8194, 16386, 34816, 65600, 131073, 131088, 131104, 131200, 262146, 524352, 1048584, 1048832, 1049600, 2097664, 4194816, 8388672, 16777218, 33554436, 33558528], #[8194, 16386, 32772, 32776, 32800, 34816, 65600, 131073, 131088, 131200, 262146, 524352, 1048832, 1049600, 2097664, 4194816, 8388672, 16777218, 33558528]] : Array (Array Nat))[k.val]!)[i.val]!
def negative (k : Fin 6) : Nat := (#[1217090, 1247750, 9572870, 9634310, 34736706, 34767426] : Array Nat)[k.val]!
def initial : List Column :=
  let raw := List.ofFn (fun i : Fin 26 => fun r : Nat => r.testBit i.val)
  let base := ([(false,0,1), (false,3,9), (true,15,27), (true,17,26), (true,13,26), (true,13,27), (false,2,6), (true,1,24), (true,15,32), (true,25,32), (true,0,17), (true,0,23), (true,0,25), (false,17,19), (false,20,24), (false,39,40), (true,7,41)] : List Gate).foldl step raw
  base ++ [mix true (mix false (wire base 3) (wire base 6)) (mix false (wire base 13) (wire base 16))]
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
(mix false (fun t : Nat => t.testBit 20) (fun t : Nat => t.testBit 24)),
(mix false (mix false (fun t : Nat => t.testBit 17) (fun t : Nat => t.testBit 19)) (mix false (fun t : Nat => t.testBit 20) (fun t : Nat => t.testBit 24))),
(mix true (fun t : Nat => t.testBit 7) (mix false (mix false (fun t : Nat => t.testBit 17) (fun t : Nat => t.testBit 19)) (mix false (fun t : Nat => t.testBit 20) (fun t : Nat => t.testBit 24)))),
(mix true (mix false (fun t : Nat => t.testBit 3) (fun t : Nat => t.testBit 6)) (mix false (fun t : Nat => t.testBit 13) (fun t : Nat => t.testBit 16)))]
private def col (i : Fin 44) : Column := projected[i.val]!
private theorem physical (i : Fin 44) : wire initial i.val = col i := by fin_cases i <;> rfl
private def small (i : Fin 44) (k : Fin 6) := col i (negative k) = false →
    (Finset.univ.filter (fun p : Fin 19 => col i (flag k p))).card ≤ 1
private theorem cert0 (k : Fin 6) : small 0 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert1 (k : Fin 6) : small 1 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert2 (k : Fin 6) : small 2 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert3 (k : Fin 6) : small 3 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert4 (k : Fin 6) : small 4 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert5 (k : Fin 6) : small 5 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert6 (k : Fin 6) : small 6 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert7 (k : Fin 6) : small 7 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert8 (k : Fin 6) : small 8 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert9 (k : Fin 6) : small 9 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert10 (k : Fin 6) : small 10 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert11 (k : Fin 6) : small 11 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert12 (k : Fin 6) : small 12 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert13 (k : Fin 6) : small 13 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert14 (k : Fin 6) : small 14 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert15 (k : Fin 6) : small 15 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert16 (k : Fin 6) : small 16 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert17 (k : Fin 6) : small 17 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert18 (k : Fin 6) : small 18 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert19 (k : Fin 6) : small 19 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert20 (k : Fin 6) : small 20 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert21 (k : Fin 6) : small 21 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert22 (k : Fin 6) : small 22 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert23 (k : Fin 6) : small 23 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert24 (k : Fin 6) : small 24 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert25 (k : Fin 6) : small 25 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert26 (k : Fin 6) : small 26 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert27 (k : Fin 6) : small 27 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert28 (k : Fin 6) : small 28 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert29 (k : Fin 6) : small 29 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert30 (k : Fin 6) : small 30 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert31 (k : Fin 6) : small 31 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert32 (k : Fin 6) : small 32 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert33 (k : Fin 6) : small 33 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert34 (k : Fin 6) : small 34 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert35 (k : Fin 6) : small 35 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert36 (k : Fin 6) : small 36 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert37 (k : Fin 6) : small 37 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert38 (k : Fin 6) : small 38 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert39 (k : Fin 6) : small 39 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert40 (k : Fin 6) : small 40 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert41 (k : Fin 6) : small 41 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert42 (k : Fin 6) : small 42 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem cert43 (k : Fin 6) : small 43 k := by fin_cases k <;> unfold small <;> decide +kernel
private theorem checked (i : Fin 44) (k : Fin 6) : small i k := by
  fin_cases i
  · exact cert0 k
  · exact cert1 k
  · exact cert2 k
  · exact cert3 k
  · exact cert4 k
  · exact cert5 k
  · exact cert6 k
  · exact cert7 k
  · exact cert8 k
  · exact cert9 k
  · exact cert10 k
  · exact cert11 k
  · exact cert12 k
  · exact cert13 k
  · exact cert14 k
  · exact cert15 k
  · exact cert16 k
  · exact cert17 k
  · exact cert18 k
  · exact cert19 k
  · exact cert20 k
  · exact cert21 k
  · exact cert22 k
  · exact cert23 k
  · exact cert24 k
  · exact cert25 k
  · exact cert26 k
  · exact cert27 k
  · exact cert28 k
  · exact cert29 k
  · exact cert30 k
  · exact cert31 k
  · exact cert32 k
  · exact cert33 k
  · exact cert34 k
  · exact cert35 k
  · exact cert36 k
  · exact cert37 k
  · exact cert38 k
  · exact cert39 k
  · exact cert40 k
  · exact cert41 k
  · exact cert42 k
  · exact cert43 k
private theorem start (k : Fin 6) (i : Nat) (off : wire initial i (negative k) = false) :
    (Finset.univ.filter (fun p : Fin 19 => wire initial i (flag k p))).card ≤ 1 := by
  by_cases hi : i < 44
  · have e : wire initial i = col ⟨i,hi⟩ := physical ⟨i,hi⟩
    rw [e] at off ⊢
    exact checked ⟨i,hi⟩ k off
  · have e : wire initial i = fun _ => false := List.getD_eq_default _ _ (show initial.length ≤ i by change 44 ≤ i; omega)
    simp [e]
end PEqualNP.Research.PlanePointSevenPairedCharge.Instance
open PEqualNP.Research.PlanePointSevenPairedCharge.Core PEqualNP.Research.PlanePointSevenPairedCharge.Instance in
theorem PEqualNP.Research.PlanePointSevenPairedCharge.single : ∀ (k : Fin 6) (gs : List Gate) (o : Nat),
    (∀ p : Fin 19, wire (gs.foldl step initial) o (flag k p) = true) →
    wire (gs.foldl step initial) o (negative k) = false →
    18 ≤ cost (negative k) initial gs := by
  intro k gs o hp hn
  have h := PEqualNP.Research.PlanePointSevenPairedCharge.packing 19 (flag k) (negative k) initial gs o (start k) hp hn
  omega
namespace PEqualNP.Research.PlanePointSevenPairedCharge.Instance
open Core
def joint (t u : Nat) (s : List Column) (gs : List Gate) : Nat :=
  (gs.foldl (fun z g => (step z.1 g,z.2 + ((!g.1 && !(newWire z.1 g t) && !(newWire z.1 g u)).toNat))) (s,0)).2
private theorem overlap (t u : Nat) (gs : List Gate) (s : List Column) (a b c : Nat) :
    (gs.foldl (fun z g => (step z.1 g,z.2 + charge t z.1 g)) (s,a)).2 +
    (gs.foldl (fun z g => (step z.1 g,z.2 + charge u z.1 g)) (s,b)).2 + c ≤
    a+b+gs.countP (fun g => !g.1) +
    (gs.foldl (fun z g => (step z.1 g,z.2 + ((!g.1 && !(newWire z.1 g t) && !(newWire z.1 g u)).toNat))) (s,c)).2 := by
  induction gs generalizing s a b c with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons,List.countP_cons]
    have h := ih (step s g) (a+charge t s g) (b+charge u s g)
      (c+((!g.1 && !(newWire s g t) && !(newWire s g u)).toNat))
    cases e : g.1 <;> cases f : newWire s g t <;> cases v : newWire s g u <;>
      simp [charge,e,f,v] at h ⊢ <;> omega
end PEqualNP.Research.PlanePointSevenPairedCharge.Instance
open PEqualNP.Research.PlanePointSevenPairedCharge.Core PEqualNP.Research.PlanePointSevenPairedCharge.Instance in
theorem PEqualNP.Research.PlanePointSevenPairedCharge : ∀ (k l : Fin 6) (gs : List Gate) (o : Nat),
    (∀ i : Fin 6, (i = k ∨ i = l) → (∀ p : Fin 19, wire (gs.foldl step initial) o (flag i p) = true) ∧
      wire (gs.foldl step initial) o (negative i) = false) →
    36 ≤ gs.countP (fun g => !g.1) + joint (negative k) (negative l) initial gs := by
  intro k l gs o h
  obtain ⟨pk,nk⟩ := h k (Or.inl rfl)
  obtain ⟨pl,nl⟩ := h l (Or.inr rfl)
  have a := PEqualNP.Research.PlanePointSevenPairedCharge.single k gs o pk nk
  have b := PEqualNP.Research.PlanePointSevenPairedCharge.single l gs o pl nl
  have c := overlap (negative k) (negative l) gs initial 0 0 0
  change cost _ initial gs + cost _ initial gs + 0 ≤ 0+0+_+joint _ _ initial gs at c
  omega
