import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlanePointSevenOrOutput.Core
abbrev Column := Nat → Bool
abbrev Gate := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def mix (op : Bool) (x y : Column) : Column := fun r => if op then x r && y r else x r || y r
def newWire (s : List Column) (g : Gate) := mix g.1 (wire s g.2.1) (wire s g.2.2)
def step (s : List Column) (g : Gate) := s ++ [newWire s g]
def live {m : Nat} (flag : Fin m → Nat) (t : Nat) (w : Column) : Prop :=
  w t = false ∧ ∃ i, w (flag i) = true
def useful {m : Nat} (flag : Fin m → Nat) (t : Nat) (s : List Column) (g : Gate) : Prop :=
  live flag t (wire s g.2.1) ∧ live flag t (wire s g.2.2)
noncomputable def charge {m : Nat} (flag : Fin m → Nat) (t : Nat) (s : List Column) (g : Gate) : Nat := by
  classical
  exact if g.1 = false ∧ useful flag t s g then 1 else 0
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
    Count flag t (step s g) (q+charge flag t s g) := by
  classical
  obtain ⟨op,i,j⟩ := g
  cases op
  · by_cases huse : useful flag t s (false,i,j)
    · simp only [charge,huse,and_self,ite_true]
      apply grow flag t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
      simpa [newWire,wire] using cutOr flag t (wire s i) (wire s j)
    · simp only [charge,huse,and_false,ite_false]
      have sub := cutOr flag t (wire s i) (wire s j)
      have empty (w : Column) (hw : ¬ live flag t w) : supp flag t w = ∅ := by
        cases ht : w t
        · have z : ∀ p, w (flag p) = false := fun p => Bool.eq_false_iff.mpr (fun k => hw ⟨ht,p,k⟩)
          simp [supp,ht,z]
        · simp [supp,ht]
      by_cases hx : live flag t (wire s i)
      · have ey := empty (wire s j) (fun z => huse ⟨hx,z⟩)
        apply grow flag t h _ {i} (by simp)
        simpa [newWire,wire,ey] using (show supp flag t (mix false (wire s i) (wire s j)) ⊆ supp flag t (wire s i) by simpa [ey] using sub)
      · apply grow flag t h _ {j} (by simp)
        simpa [newWire,wire] using (show supp flag t (mix false (wire s i) (wire s j)) ⊆ supp flag t (wire s j) by simpa [empty _ hx] using sub)
  · simp only [charge,Bool.true_eq_false,and_false,false_and,ite_false]
    let k := if wire s i t then j else i
    apply grow flag t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd flag t (wire s i) (wire s j)
    change _ ⊆ supp flag t (wire s k)
    cases e : wire s i t <;> simpa only [newWire,k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) (z : List Column × Nat) (h : Count flag t z.1 z.2) :
    Count flag t (gs.foldl step z.1)
      ((gs.foldl (fun z g => (step z.1 g,z.2 + charge flag t z.1 g)) z).2) := by
  induction gs generalizing z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (step z.1 g,z.2 + charge flag t z.1 g) (appendGate flag t h g)

private theorem packing : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (o : Nat),
    (∀ i : Nat, wire s i t = false → (Finset.univ.filter (fun p : Fin m => wire s i (flag p))).card ≤ 1) →
    (∀ p : Fin m, wire (gs.foldl step s) o (flag p) = true) →
    wire (gs.foldl step s) o t = false →
    m ≤ 1 + (gs.foldl (fun z g => (step z.1 g,z.2 + charge flag t z.1 g)) (s,0)).2 := by
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
  change (supp flag t (wire _ o)).card ≤ _ + 1 at bound
  rw [full] at bound
  simpa [Nat.add_comm] using bound

def allGood {m : Nat} (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) :=
  gs.foldr (fun g next state => (g.1 = false → useful flag t state g) ∧ next (step state g)) (fun _ => True) s
private theorem ledger {m} (f : Fin m → Nat) (t : Nat) (gs : List Gate) (s : List Column) (q : Nat) :
    let z := (gs.foldl (fun z g => (step z.1 g,z.2 + charge f t z.1 g)) (s,q)).2
    z ≤ q + gs.countP (fun g => !g.1) ∧ (z = q + gs.countP (fun g => !g.1) → allGood f t s gs) := by
  classical
  induction gs generalizing s q with
  | nil => simp [allGood]
  | cons g gs ih =>
    have h := ih (step s g) (q+charge f t s g)
    simp only [List.foldl_cons,List.countP_cons]
    change _ ≤ _ ∧ (_ → (g.1 = false → useful f t s g) ∧ allGood f t (step s g) gs)
    cases op : g.1 <;> by_cases u : useful f t s g <;>
      simp [op,u,charge] at h ⊢ <;> (first | exact h | exact ⟨by omega, fun e => h.2 (by omega)⟩ | omega)
private theorem inheritProp (s : List Column) (w : Column) (P : Column → Prop)
    (old : ∀ i, P (wire s i)) (hp : P w) : ∀ i, P (wire (s++[w]) i) := by
  intro i
  by_cases eq : i = s.length
  · subst i; simpa [wire] using hp
  by_cases lt : i < s.length
  · simpa only [wire,List.getD_append _ _ _ _ lt] using old i
  · have a := List.getD_eq_default (s++[w]) (fun _ : Nat => false) (show (s++[w]).length ≤ i by simp; omega)
    have b := List.getD_eq_default s (fun _ : Nat => false) (show s.length ≤ i by omega)
    simpa only [wire,a,b] using old i
private theorem trace {m : Nat} (F : Nat → Fin m → Nat) (T : Nat → Nat) (R : Column → Prop) (p : Nat)
    (closed : ∀ x y, R x → R y → R (mix true x y))
    (miss : ∀ w, R w → w p = true → ¬ (∀ k, live (F k) (T k) w))
    (gs : List Gate) (s : List Column) (start : ∀ i, wire s i p = true → R (wire s i))
    (ok : ∀ k, allGood (F k) (T k) s gs) : ∀ i, wire (gs.foldl step s) i p = true → R (wire (gs.foldl step s) i) := by
  induction gs generalizing s with
  | nil => exact start
  | cons g gs ih =>
    have good (k) : (g.1 = false → useful (F k) (T k) s g) ∧ allGood (F k) (T k) (step s g) gs := ok k
    apply ih (step s g) _ (fun k => (good k).2)
    apply inheritProp s (newWire s g) (fun w => w p = true → R w) start
    intro on
    cases op : g.1
    · have side : wire s g.2.1 p = true ∨ wire s g.2.2 p = true := by simpa [newWire,mix,op] using on
      rcases side with h|h
      · exact False.elim (miss _ (start _ h) h (fun k => ((good k).1 op).1))
      · exact False.elim (miss _ (start _ h) h (fun k => ((good k).1 op).2))
    · have both : wire s g.2.1 p = true ∧ wire s g.2.2 p = true := by simpa [newWire,mix,op] using on
      simpa only [newWire,op] using closed _ _ (start _ both.1) (start _ both.2)
end PEqualNP.Research.PlanePointSevenOrOutput.Core
open PEqualNP.Research.PlanePointSevenOrOutput.Core in
theorem PEqualNP.Research.PlanePointSevenOrOutput.tight : ∀ (m : Nat) (F : Nat → Fin m → Nat) (T : Nat → Nat) (R : Column → Prop)
    (s : List Column) (gs : List Gate) (o p : Nat),
    (∀ k i, wire s i (T k) = false → (Finset.univ.filter (fun a : Fin m => wire s i (F k a))).card ≤ 1) →
    (∀ i, R (wire s i)) →
    (∀ x y, R x → R y → R (mix true x y)) →
    (∀ w, R w → w p = true → ¬ (∀ k, live (F k) (T k) w)) →
    (∀ k a, wire (gs.foldl step s) o (F k a) = true) →
    (∀ k, wire (gs.foldl step s) o (T k) = false) →
    wire (gs.foldl step s) o p = true → 0 < m →
    m ≤ gs.countP (fun g => !g.1) := by
  intro m F T R s gs o p small init closed miss hp hn on pos
  by_contra h
  have good (k) : allGood (F k) (T k) s gs := by
    have pk := packing m (F k) (T k) s gs o (small k) (hp k) (hn k)
    have led := ledger (F k) (T k) gs s 0
    simp only [Nat.zero_add] at led
    exact led.2 (by omega)
  have final := trace F T R p closed miss gs s (fun i _ => init i) good o on
  exact miss _ final on (fun k => ⟨hn k,⟨0,pos⟩,hp k ⟨0,pos⟩⟩)
namespace PEqualNP.Research.PlanePointSevenOrOutput.Instance
open Core
def initial : List Column :=
  let raw := List.ofFn (fun i : Fin 26 => fun r : Nat => r.testBit i.val)
  ([(false,0,1), (false,3,9), (true,15,27), (true,17,26), (true,13,26), (true,13,27), (false,2,6), (true,1,24), (true,15,32), (true,25,32), (true,0,17), (true,0,23), (true,0,25), (false,17,19), (false,20,24), (false,39,40)] : List Gate).foldl step raw
def flags0 (i : Fin 19) : Nat := (#[8194, 16386, 32772, 65544, 65552, 65600, 69632, 131073, 131104, 131200, 262146, 524292, 1048832, 1049600, 2097664, 4194816, 8390656, 16777218, 33554436] : Array Nat)[i.val]!
def neg0 : Nat := 1247750
def flags1 (i : Fin 19) : Nat := (#[8194, 16386, 32772, 32776, 32800, 34816, 65600, 131073, 131088, 131200, 262146, 524352, 1048832, 1049600, 2097664, 4194816, 8388672, 16777218, 33558528] : Array Nat)[i.val]!
def neg1 : Nat := 1217090
def pivot : Nat := 34816
private def raw : Array Column := #[(fun t : Nat => t.testBit 0),
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
(mix false (mix false (fun t : Nat => t.testBit 17) (fun t : Nat => t.testBit 19)) (mix false (fun t : Nat => t.testBit 20) (fun t : Nat => t.testBit 24)))]
private def c (i : Fin 42) := raw[i.val]!
private theorem phys (i : Fin 42) : wire initial i.val = c i := by fin_cases i <;> rfl
private def F (k : Nat) := if k=0 then flags0 else flags1
private def T (k : Nat) := if k=0 then neg0 else neg1
private def R (w : Column) := w pivot = true → w = c 11 ∨ w = c 15 ∨ w = mix true (c 11) (c 15)
private theorem closed (x y : Column) (hx : R x) (hy : R y) : R (mix true x y) := by
  intro on
  have both : x pivot = true ∧ y pivot = true := by simpa [mix] using on
  rcases hx both.1 with a|a|a <;> rcases hy both.2 with b|b|b <;> rw [a,b] <;>
    first | (left; funext t; simp [mix,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]; done)
          | (right; left; funext t; simp [mix,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]; done)
          | (right; right; funext t; simp [mix,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]; done)
private theorem restricted (i : Fin 42) : R (c i) := by
  fin_cases i
  · have off : c 0 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 1 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 2 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 3 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 4 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 5 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 6 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 7 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 8 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 9 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 10 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · intro _; exact Or.inl rfl
  · have off : c 12 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 13 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 14 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · intro _; exact Or.inr (Or.inl rfl)
  · have off : c 16 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 17 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 18 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 19 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 20 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 21 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 22 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 23 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 24 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 25 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 26 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 27 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 28 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 29 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 30 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 31 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 32 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 33 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 34 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 35 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 36 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 37 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 38 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 39 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 40 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
  · have off : c 41 pivot = false := by decide +kernel
    intro on; exact False.elim (Bool.noConfusion (off.symm.trans on))
private theorem initialR (i : Nat) : R (wire initial i) := by
  by_cases hi : i < 42
  · have e : wire initial i = c ⟨i,hi⟩ := phys ⟨i,hi⟩
    rw [e]; exact restricted _
  · have e : wire initial i = fun _ => false := List.getD_eq_default initial (fun _ : Nat => false) (show initial.length ≤ i by change 42 ≤ i; omega)
    rw [e]; simp [R]
private theorem missing (w : Column) (h : R w) (on : w pivot = true) : ¬ (∀ k, live (F k) (T k) w) := by
  intro allk
  rcases h on with e|e|e
  · have contra : ¬ live flags0 neg0 (c 11) := by unfold live; decide +kernel
    rw [e] at allk; exact contra (allk 0)
  · have contra : ¬ live flags1 neg1 (c 15) := by unfold live; decide +kernel
    rw [e] at allk; exact contra (allk 1)
  · have contra : ¬ live flags0 neg0 (mix true (c 11) (c 15)) := by unfold live; decide +kernel
    rw [e] at allk; exact contra (allk 0)
private def valid (i : Fin 42) (f : Fin 19 → Nat) (t : Nat) := c i t = false → (Finset.univ.filter (fun a : Fin 19 => c i (f a))).card ≤ 1
private theorem cert0 : valid 0 flags0 neg0 ∧ valid 0 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert1 : valid 1 flags0 neg0 ∧ valid 1 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert2 : valid 2 flags0 neg0 ∧ valid 2 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert3 : valid 3 flags0 neg0 ∧ valid 3 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert4 : valid 4 flags0 neg0 ∧ valid 4 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert5 : valid 5 flags0 neg0 ∧ valid 5 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert6 : valid 6 flags0 neg0 ∧ valid 6 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert7 : valid 7 flags0 neg0 ∧ valid 7 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert8 : valid 8 flags0 neg0 ∧ valid 8 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert9 : valid 9 flags0 neg0 ∧ valid 9 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert10 : valid 10 flags0 neg0 ∧ valid 10 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert11 : valid 11 flags0 neg0 ∧ valid 11 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert12 : valid 12 flags0 neg0 ∧ valid 12 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert13 : valid 13 flags0 neg0 ∧ valid 13 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert14 : valid 14 flags0 neg0 ∧ valid 14 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert15 : valid 15 flags0 neg0 ∧ valid 15 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert16 : valid 16 flags0 neg0 ∧ valid 16 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert17 : valid 17 flags0 neg0 ∧ valid 17 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert18 : valid 18 flags0 neg0 ∧ valid 18 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert19 : valid 19 flags0 neg0 ∧ valid 19 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert20 : valid 20 flags0 neg0 ∧ valid 20 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert21 : valid 21 flags0 neg0 ∧ valid 21 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert22 : valid 22 flags0 neg0 ∧ valid 22 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert23 : valid 23 flags0 neg0 ∧ valid 23 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert24 : valid 24 flags0 neg0 ∧ valid 24 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert25 : valid 25 flags0 neg0 ∧ valid 25 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert26 : valid 26 flags0 neg0 ∧ valid 26 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert27 : valid 27 flags0 neg0 ∧ valid 27 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert28 : valid 28 flags0 neg0 ∧ valid 28 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert29 : valid 29 flags0 neg0 ∧ valid 29 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert30 : valid 30 flags0 neg0 ∧ valid 30 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert31 : valid 31 flags0 neg0 ∧ valid 31 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert32 : valid 32 flags0 neg0 ∧ valid 32 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert33 : valid 33 flags0 neg0 ∧ valid 33 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert34 : valid 34 flags0 neg0 ∧ valid 34 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert35 : valid 35 flags0 neg0 ∧ valid 35 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert36 : valid 36 flags0 neg0 ∧ valid 36 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert37 : valid 37 flags0 neg0 ∧ valid 37 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert38 : valid 38 flags0 neg0 ∧ valid 38 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert39 : valid 39 flags0 neg0 ∧ valid 39 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert40 : valid 40 flags0 neg0 ∧ valid 40 flags1 neg1 := by unfold valid; decide +kernel
private theorem cert41 : valid 41 flags0 neg0 ∧ valid 41 flags1 neg1 := by unfold valid; decide +kernel
private theorem casesSmall (i : Fin 42) : valid i flags0 neg0 ∧ valid i flags1 neg1 := by
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
  · exact cert41
private theorem small (k i : Nat) (off : wire initial i (T k) = false) :
    (Finset.univ.filter (fun a : Fin 19 => wire initial i (F k a))).card ≤ 1 := by
  by_cases hi : i < 42
  · have e : wire initial i = c ⟨i,hi⟩ := phys ⟨i,hi⟩
    rw [e] at off ⊢
    by_cases hk : k = 0
    · simp [F,T,hk] at off ⊢; exact (casesSmall ⟨i,hi⟩).1 off
    · simp [F,T,hk] at off ⊢; exact (casesSmall ⟨i,hi⟩).2 off
  · have e : wire initial i = fun _ => false := List.getD_eq_default initial (fun _ : Nat => false) (show initial.length ≤ i by change 42 ≤ i; omega)
    rw [e]; simp

private def shift (g : Gate) : Gate := (g.1,g.2.1+1,g.2.2+1)
private theorem lifted (v : Column) (ls : List Gate) (s : List Column) :
    (ls.map shift).foldl step (v::s) = v::ls.foldl step s := by
  induction ls generalizing s with
  | nil => rfl
  | cons g gs ih =>
    change (gs.map shift).foldl step (v :: step s g) = v :: gs.foldl step (step s g)
    exact ih _
private theorem shiftedCount (ls : List Gate) :
    (ls.map shift).countP (fun g => !g.1) = ls.countP (fun g => !g.1) := by
  induction ls with
  | nil => rfl
  | cons g gs ih => simp [List.countP_cons,shift,ih]

private theorem withFree (v : Column) (off : v pivot = false)
    (sm : ∀ k, v (T k) = false →
      (Finset.univ.filter (fun a : Fin 19 => v (F k a))).card ≤ 1)
    (gs : List Gate) (o : Nat)
    (hp : ∀ k a, wire (gs.foldl step (v::initial)) o (F k a) = true)
    (hn : ∀ k, wire (gs.foldl step (v::initial)) o (T k) = false)
    (on : wire (gs.foldl step (v::initial)) o pivot = true) :
    19 ≤ gs.countP (fun g => !g.1) := by
  apply PEqualNP.Research.PlanePointSevenOrOutput.tight 19 F T R (v::initial) gs o pivot _ _ closed missing hp hn on (by decide)
  · intro k i
    cases i with
    | zero => exact sm k
    | succ i => exact small k i
  · intro i
    cases i with
    | zero => change v pivot = true → _; simp [off]
    | succ i => exact initialR i

end PEqualNP.Research.PlanePointSevenOrOutput.Instance
open PEqualNP.Research.PlanePointSevenOrOutput.Core PEqualNP.Research.PlanePointSevenOrOutput.Instance in
theorem PEqualNP.Research.PlanePointSevenOrOutput : ∀ (pre post : List Gate) (a b o : Nat),
    let g : Gate := (false,a,b)
    let v := newWire (pre.foldl step initial) g
    let out := wire (post.foldl step (step (pre.foldl step initial) g)) o
    v pivot = false →
    (v neg0 = false → (Finset.univ.filter (fun i : Fin 19 => v (flags0 i))).card ≤ 1) →
    (v neg1 = false → (Finset.univ.filter (fun i : Fin 19 => v (flags1 i))).card ≤ 1) →
    (∀ i : Fin 19, out (flags0 i) = true) → (∀ i : Fin 19, out (flags1 i) = true) →
    out neg0 = false → out neg1 = false → out pivot = true →
    20 ≤ (pre ++ g :: post).countP (fun gate => !gate.1) := by
  intro pre post a b o g v out off sm0 sm1 hp0 hp1 hn0 hn1 on
  let cp : Gate := (true,0,0)
  let alt := pre.map shift ++ cp :: post.map shift
  have sim : alt.foldl step (v::initial) = v::post.foldl step (step (pre.foldl step initial) g) := by
    simp only [alt,List.foldl_append,List.foldl_cons,lifted]
    have head : step (v::pre.foldl step initial) cp = v :: step (pre.foldl step initial) g := by
      have e : newWire (v::pre.foldl step initial) cp = v := by
        funext r
        change (v r && v r) = v r
        simp
      simp only [step,e,List.cons_append]
      rfl
    rw [head,lifted]
  have eq : wire (alt.foldl step (v::initial)) (o+1) = out := by rw [sim]; rfl
  have low := withFree v off (by
    intro k
    by_cases h : k = 0
    · simpa only [F,T,h,ite_true] using sm0
    · simpa only [F,T,if_neg h] using sm1) alt (o+1)
      (by intro k i; rw [eq]; by_cases h : k = 0 <;> simp [F,h,hp0,hp1])
      (by intro k; rw [eq]; by_cases h : k = 0 <;> simp [T,h,hn0,hn1])
      (by rw [eq]; exact on)
  simp only [alt,List.countP_append,List.countP_cons,shiftedCount] at low ⊢
  simp [cp,g] at low ⊢
  omega
