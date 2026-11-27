import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneOrTraceDensity.Core
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

end PEqualNP.Research.PlaneOrTraceDensity.Core
open PEqualNP.Research.PlaneOrTraceDensity.Core in
theorem PEqualNP.Research.PlaneOrTraceDensity.rowBound : ∀ (m : Nat) (flag : Fin m → Nat) (t : Nat) (s : List Column) (gs : List Gate) (o : Nat),
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
namespace PEqualNP.Research.PlaneOrTraceDensity.Mass
open Core
def orWires (s : List Column) (gs : List Gate) : List Column :=
  gs.foldr (fun g next state =>
    let rest := next (step state g)
    if g.1 then rest else newWire state g :: rest) (fun _ => []) s
private def truth (t : Nat) (ws : List Column) := (ws.map (fun w => (w t).toNat)).sum
private theorem ledger (t : Nat) (gs : List Gate) (s : List Column) (q : Nat) :
    ((gs.foldl (fun z g => (step z.1 g,z.2 + charge t z.1 g)) (s,q)).2) + truth t (orWires s gs)
      = q + (orWires s gs).length := by
  induction gs generalizing s q with
  | nil => simp [orWires,truth]
  | cons g gs ih =>
    have bound := ih (step s g) (q+charge t s g)
    simp only [List.foldl_cons]
    have cons : orWires s (g :: gs) = (if g.1 then orWires (step s g) gs else newWire s g :: orWires (step s g) gs) := rfl
    rw [cons]
    cases op : g.1 <;> cases bit : newWire s g t <;>
      simp [op,truth,charge,bit] at bound ⊢ <;> omega
private theorem sum_truth (ws : List Column) (t : Nat) :
    (∑ i : Fin ws.length, (ws[i.val] t).toNat) = truth t ws := by
  induction ws with
  | nil => simp [truth]
  | cons w ws ih =>
    change (∑ i : Fin (ws.length+1), ((w :: ws)[i.val] t).toNat) = _
    rw [Fin.sum_univ_succ]
    change (w t).toNat + (∑ i : Fin ws.length, (ws[i.val] t).toNat) = (w t).toNat + truth t ws
    rw [ih]

private theorem subSum {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (inj : Function.Injective f) (g : β → Nat) :
    (∑ a, g (f a)) ≤ ∑ b, g b := by
  classical
  calc
    (∑ a, g (f a)) = ∑ b ∈ Finset.univ.image f, g b :=
      (Finset.sum_image (fun _ _ _ _ e => inj e)).symm
    _ ≤ ∑ b, g b := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def weight (w : Fin 256) := ∑ i : Fin 8, (w.val.testBit i.val).toNat
private def ones (w : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ones w n + (w.testBit n).toNat
private theorem ones_eq (w n : Nat) : (∑ i : Fin n, (w.testBit i.val).toNat) = ones w n := by
  induction n with
  | zero => simp [ones]
  | succ n h => simpa only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,h,ones]
private def deficits : Nat → Nat
  | 0 => 0
  | n+1 => deficits n + (5 - ones n 8)
private theorem deficit_sum (n : Nat) : (∑ w : Fin n, (5 - ones w.val 8)) = deficits n := by
  induction n with
  | zero => simp [deficits]
  | succ n h => simpa only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,h,deficits]
set_option maxRecDepth 12000 in
private theorem numeric : deficits 256 = 303 := by rfl
private theorem allDeficits : (∑ w : Fin 256, (5 - weight w)) = 303 := by
  simp only [weight,ones_eq,deficit_sum,numeric]
private theorem heavy (f : Fin 218 → Fin 256) (inj : Function.Injective f) :
    787 ≤ ∑ j, weight (f j) := by
  have small := subSum f inj (fun w => 5 - weight w)
  rw [allDeficits] at small
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 218)))
    (f := fun _ => 5) (g := fun j => weight (f j) + (5 - weight (f j))) (fun i _ => by omega)
  rw [Finset.sum_add_distrib] at bound
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  omega
private theorem atRow (ws : List Column) (t : Nat) (port : Fin 2 × Fin 8 → Fin ws.length)
    (inj : Function.Injective port) (words : Fin 2 → Fin 256)
    (bits : ∀ b j, (words b).val.testBit j.val = ws[(port (b,j)).val] t) :
    weight (words 0) + weight (words 1) ≤ truth t ws := by
  have h := subSum port inj (fun i : Fin ws.length => (ws[i.val] t).toNat)
  rw [sum_truth] at h
  rw [Fintype.sum_prod_type,Fin.sum_univ_two] at h
  simpa only [weight,bits] using h
end PEqualNP.Research.PlaneOrTraceDensity.Mass
open PEqualNP.Research.PlaneOrTraceDensity.Core PEqualNP.Research.PlaneOrTraceDensity.Mass in
theorem PEqualNP.Research.PlaneOrTraceDensity : ∀ (s : List Column) (gs : List Gate) (o : Nat)
    (row width : Fin 218 → Nat) (flag : (k : Fin 218) → Fin (width k) → Nat),
    3862 ≤ ∑ k, width k →
    (∀ k i, wire s i (row k) = false →
      (Finset.univ.filter (fun p : Fin (width k) => wire s i (flag k p))).card ≤ 1) →
    (∀ k p, wire (gs.foldl step s) o (flag k p) = true) →
    (∀ k, wire (gs.foldl step s) o (row k) = false) →
    let ws := orWires s gs
    ∀ (port : Fin 2 × Fin 8 → Fin ws.length) (words : Fin 2 → Fin 218 → Fin 256),
    Function.Injective port → (∀ b, Function.Injective (words b)) →
    (∀ b i k, (words b k).val.testBit i.val = ws[(port (b,i)).val] (row k)) →
    24 ≤ ws.length := by
  intro s gs o row width flag lower small hp hn ws port words di wi bits
  have inc : (∑ k, width k) ≤ ∑ k, (1 + cost (row k) s gs) :=
    Finset.sum_le_sum (fun k _ => PEqualNP.Research.PlaneOrTraceDensity.rowBound _ (flag k)
      (row k) s gs o (small k) (hp k) (hn k))
  have per (k : Fin 218) :
      weight (words 0 k) + weight (words 1 k) + (1 + cost (row k) s gs) ≤
        ws.length+1 := by
    let t := row k
    have a := atRow ws t port di (fun b => words b k) (fun b i => bits b i k)
    have b : cost t s gs + truth t ws = ws.length := by
      simpa only [cost,Nat.zero_add,ws] using ledger t gs s 0
    change weight (words 0 k) + weight (words 1 k) + (1 + cost t s gs) ≤ _
    omega
  have tot := Finset.sum_le_sum (s := Finset.univ) (fun k _ => per k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at tot
  have incBound := le_trans lower inc
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at incBound
  have l := heavy (words 0) (wi 0)
  have r := heavy (words 1) (wi 1)
  omega
