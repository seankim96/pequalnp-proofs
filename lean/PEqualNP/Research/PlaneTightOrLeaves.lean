import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneTightOrLeaves.Core
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
end PEqualNP.Research.PlaneTightOrLeaves.Core
open PEqualNP.Research.PlaneTightOrLeaves.Core in
theorem PEqualNP.Research.PlaneTightOrLeaves : ∀ (m : Nat) (F : Nat → Fin m → Nat) (T : Nat → Nat) (R : Column → Prop)
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
