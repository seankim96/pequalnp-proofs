import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Research.PlaneFlagOrTail

namespace PEqualNP.Research.PlaneAllFourthOrCount
open OrderThreePlanePrefixData PlaneFlagOrTail

def negs : Array Nat := #[5, 63, 159, 257, 166]
def flags : Array (Array Nat) := #[#[16, 4, 5, 9, 6, 10, 19, 7, 11, 3, 14, 22, 25, 30, 33, 37, 41, 47, 50],#[24, 12, 13, 14, 26, 30, 27, 31, 15, 0, 4, 10, 16, 20, 35, 36, 40, 44, 48],#[20, 32, 21, 22, 23, 34, 38, 35, 39, 0, 5, 8, 12, 16, 24, 28, 40, 45, 48],#[20, 8, 9, 10, 22, 45, 23, 11, 47, 0, 6, 13, 16, 27, 31, 32, 37, 40, 48],#[0, 1, 5, 2, 6, 41, 3, 7, 43, 10, 15, 18, 21, 26, 29, 33, 36, 45, 50]]
variable (sample : Fin 5)
def supp (x : Signature) : Finset (Fin 19) :=
  if x.2.getLsbD (negs[sample.val]!) then ∅ else Finset.univ.filter (fun i => x.1.getLsbD ((flags[sample.val]!)[i.val]!))
def Count (s : List Signature) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp sample (s.getD j (0,0)))).card ≤ q + W.card

def mix (s : List Signature) (g : Bool × Nat × Nat) : List Signature :=
  let x := s.getD g.2.1 (0,0)
  let y := s.getD g.2.2 (0,0)
  s ++ [if g.1 then joinCols x y else (x.1 &&& y.1,x.2 &&& y.2)]

private theorem cutOr (x y : Signature) : supp sample (joinCols x y) ⊆ supp sample x ∪ supp sample y := by
  cases hx : x.2.getLsbD (negs[sample.val]!) <;> cases hy : y.2.getLsbD (negs[sample.val]!) <;>
    simp [supp,joinCols,hx,hy,Finset.subset_iff] <;> grind
private theorem cutAnd (x y : Signature) : supp sample (x.1 &&& y.1,x.2 &&& y.2) ⊆
    supp sample (if x.2.getLsbD (negs[sample.val]!) then y else x) := by
  cases hx : x.2.getLsbD (negs[sample.val]!) <;> cases hy : y.2.getLsbD (negs[sample.val]!) <;>
    simp [supp,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Signature} {q c : Nat} (h : Count sample s q) (v : Signature)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp sample v ⊆ parents.biUnion (fun j => supp sample (s.getD j (0,0)))) : Count sample (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp sample ((s ++ [v]).getD j (0,0))) ⊆
        U.biUnion (fun j => supp sample (s.getD j (0,0))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp sample v := by simpa using hij
        obtain ⟨a,ha,hai⟩ := Finset.mem_biUnion.mp (sub hv)
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_right _ ha,hai⟩
      · have hd : (s ++ [v]).getD j (0,0) = s.getD j (0,0) := by
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
  · have eq : W.biUnion (fun j => supp sample ((s ++ [v]).getD j (0,0))) =
        W.biUnion (fun j => supp sample (s.getD j (0,0))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega

private theorem one {q : Nat} (s : List Signature) (h : Count sample s q) (g : Bool × Nat × Nat) :
    Count sample (mix s g) (q+g.1.toNat) := by
  rcases g with ⟨b,i,j⟩
  cases b
  · let k := if (s.getD i (0,0)).2.getLsbD (negs[sample.val]!) then j else i
    apply grow sample h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd sample (s.getD i (0,0)) (s.getD j (0,0))
    cases e : (s.getD i (0,0)).2.getLsbD (negs[sample.val]!) <;> simpa only [k,e,Bool.false_eq_true,ite_false,ite_true] using hh
  · apply grow sample h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
    simpa using cutOr sample (s.getD i (0,0)) (s.getD j (0,0))

private theorem run {q : Nat} (s : List Signature) (h : Count sample s q) (gs : List (Bool × Nat × Nat)) :
    Count sample (gs.foldl mix s) (q+gs.countP Prod.fst) := by
  induction gs generalizing s q with
  | nil => simpa using h
  | cons g gs ih =>
    have h' := ih _ (one sample s h g)
    simpa [List.countP_cons,Bool.toNat, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h'


private def picks : Array (Array Nat) := #[
#[0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[1, 1, 0, 2, 2, 1, 0, 2, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0],
#[1, 1, 2, 0, 2, 1, 0, 2, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0],
#[1, 1, 2, 2, 0, 1, 0, 2, 0, 0, 3, 1, 0, 3, 0, 0, 1, 0, 2, 1, 1, 2, 2, 3, 3, 3, 0, 0, 0],
#[1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[1, 1, 2, 2, 3, 1, 0, 2, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 2, 1, 1, 2, 2, 3, 3, 3, 0, 0, 0],
#[1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[1, 1, 2, 2, 3, 1, 0, 2, 0, 0, 3, 1, 0, 0, 0, 0, 1, 0, 2, 1, 1, 2, 2, 4, 3, 4, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[1, 1, 2, 2, 2, 1, 0, 2, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0],
#[1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0],
#[1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0],
#[1, 1, 2, 2, 2, 1, 0, 2, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 1, 0, 2, 2, 2, 2, 0, 0, 0],
#[1, 1, 2, 2, 2, 1, 0, 2, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 1, 2, 0, 2, 2, 2, 0, 0, 0],
#[1, 1, 2, 2, 3, 1, 0, 2, 0, 0, 3, 1, 0, 4, 0, 0, 1, 0, 2, 1, 1, 2, 2, 0, 3, 4, 0, 0, 0],
#[1, 1, 2, 2, 3, 1, 0, 2, 0, 0, 3, 1, 0, 3, 0, 0, 1, 0, 2, 1, 1, 2, 2, 3, 0, 3, 0, 0, 0],
#[1, 1, 2, 2, 3, 1, 0, 2, 0, 0, 3, 1, 0, 4, 0, 0, 1, 0, 2, 1, 1, 2, 2, 4, 3, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private def pick (k : Nat) : Fin 5 := ⟨((picks[k/29]!)[k%29]!)%5, by omega⟩
private theorem rawOK : ∀ (g : Fin 5) (i : Fin 29), (supp g (PlaneFlagFourth.col i.val)).card ≤ 1 := by decide +kernel
private def fourthOK (k : Nat) := decide ((supp (pick k) (PlaneFlagFourth.gate k [])).card ≤ 1)
set_option maxRecDepth 10000 in
private theorem row0 : ∀ j : Fin 29, fourthOK (0*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row1 : ∀ j : Fin 29, fourthOK (1*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row2 : ∀ j : Fin 29, fourthOK (2*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row3 : ∀ j : Fin 29, fourthOK (3*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row4 : ∀ j : Fin 29, fourthOK (4*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row5 : ∀ j : Fin 29, fourthOK (5*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row6 : ∀ j : Fin 29, fourthOK (6*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row7 : ∀ j : Fin 29, fourthOK (7*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row8 : ∀ j : Fin 29, fourthOK (8*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row9 : ∀ j : Fin 29, fourthOK (9*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row10 : ∀ j : Fin 29, fourthOK (10*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row11 : ∀ j : Fin 29, fourthOK (11*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row12 : ∀ j : Fin 29, fourthOK (12*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row13 : ∀ j : Fin 29, fourthOK (13*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row14 : ∀ j : Fin 29, fourthOK (14*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row15 : ∀ j : Fin 29, fourthOK (15*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row16 : ∀ j : Fin 29, fourthOK (16*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row17 : ∀ j : Fin 29, fourthOK (17*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row18 : ∀ j : Fin 29, fourthOK (18*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row19 : ∀ j : Fin 29, fourthOK (19*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row20 : ∀ j : Fin 29, fourthOK (20*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row21 : ∀ j : Fin 29, fourthOK (21*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row22 : ∀ j : Fin 29, fourthOK (22*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row23 : ∀ j : Fin 29, fourthOK (23*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row24 : ∀ j : Fin 29, fourthOK (24*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row25 : ∀ j : Fin 29, fourthOK (25*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row26 : ∀ j : Fin 29, fourthOK (26*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row27 : ∀ j : Fin 29, fourthOK (27*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row28 : ∀ j : Fin 29, fourthOK (28*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row29 : ∀ j : Fin 29, fourthOK (29*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row30 : ∀ j : Fin 29, fourthOK (30*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row31 : ∀ j : Fin 29, fourthOK (31*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row32 : ∀ j : Fin 29, fourthOK (32*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row33 : ∀ j : Fin 29, fourthOK (33*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row34 : ∀ j : Fin 29, fourthOK (34*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row35 : ∀ j : Fin 29, fourthOK (35*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row36 : ∀ j : Fin 29, fourthOK (36*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row37 : ∀ j : Fin 29, fourthOK (37*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row38 : ∀ j : Fin 29, fourthOK (38*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row39 : ∀ j : Fin 29, fourthOK (39*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row40 : ∀ j : Fin 29, fourthOK (40*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row41 : ∀ j : Fin 29, fourthOK (41*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row42 : ∀ j : Fin 29, fourthOK (42*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row43 : ∀ j : Fin 29, fourthOK (43*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row44 : ∀ j : Fin 29, fourthOK (44*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row45 : ∀ j : Fin 29, fourthOK (45*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row46 : ∀ j : Fin 29, fourthOK (46*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row47 : ∀ j : Fin 29, fourthOK (47*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row48 : ∀ j : Fin 29, fourthOK (48*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row49 : ∀ j : Fin 29, fourthOK (49*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row50 : ∀ j : Fin 29, fourthOK (50*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row51 : ∀ j : Fin 29, fourthOK (51*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row52 : ∀ j : Fin 29, fourthOK (52*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row53 : ∀ j : Fin 29, fourthOK (53*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row54 : ∀ j : Fin 29, fourthOK (54*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row55 : ∀ j : Fin 29, fourthOK (55*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row56 : ∀ j : Fin 29, fourthOK (56*29+j.val) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row57 : ∀ j : Fin 29, fourthOK (57*29+j.val) = true := by decide +kernel
private theorem gateOK (k : Nat) (hk : k < 1682) : (supp (pick k) (PlaneFlagFourth.gate k [])).card ≤ 1 := by
  have cover (i : Fin 58) : ∀ j : Fin 29, fourthOK (i.val*29+j.val) = true := by
    match i with
    | ⟨0,_⟩ => exact row0
    | ⟨1,_⟩ => exact row1
    | ⟨2,_⟩ => exact row2
    | ⟨3,_⟩ => exact row3
    | ⟨4,_⟩ => exact row4
    | ⟨5,_⟩ => exact row5
    | ⟨6,_⟩ => exact row6
    | ⟨7,_⟩ => exact row7
    | ⟨8,_⟩ => exact row8
    | ⟨9,_⟩ => exact row9
    | ⟨10,_⟩ => exact row10
    | ⟨11,_⟩ => exact row11
    | ⟨12,_⟩ => exact row12
    | ⟨13,_⟩ => exact row13
    | ⟨14,_⟩ => exact row14
    | ⟨15,_⟩ => exact row15
    | ⟨16,_⟩ => exact row16
    | ⟨17,_⟩ => exact row17
    | ⟨18,_⟩ => exact row18
    | ⟨19,_⟩ => exact row19
    | ⟨20,_⟩ => exact row20
    | ⟨21,_⟩ => exact row21
    | ⟨22,_⟩ => exact row22
    | ⟨23,_⟩ => exact row23
    | ⟨24,_⟩ => exact row24
    | ⟨25,_⟩ => exact row25
    | ⟨26,_⟩ => exact row26
    | ⟨27,_⟩ => exact row27
    | ⟨28,_⟩ => exact row28
    | ⟨29,_⟩ => exact row29
    | ⟨30,_⟩ => exact row30
    | ⟨31,_⟩ => exact row31
    | ⟨32,_⟩ => exact row32
    | ⟨33,_⟩ => exact row33
    | ⟨34,_⟩ => exact row34
    | ⟨35,_⟩ => exact row35
    | ⟨36,_⟩ => exact row36
    | ⟨37,_⟩ => exact row37
    | ⟨38,_⟩ => exact row38
    | ⟨39,_⟩ => exact row39
    | ⟨40,_⟩ => exact row40
    | ⟨41,_⟩ => exact row41
    | ⟨42,_⟩ => exact row42
    | ⟨43,_⟩ => exact row43
    | ⟨44,_⟩ => exact row44
    | ⟨45,_⟩ => exact row45
    | ⟨46,_⟩ => exact row46
    | ⟨47,_⟩ => exact row47
    | ⟨48,_⟩ => exact row48
    | ⟨49,_⟩ => exact row49
    | ⟨50,_⟩ => exact row50
    | ⟨51,_⟩ => exact row51
    | ⟨52,_⟩ => exact row52
    | ⟨53,_⟩ => exact row53
    | ⟨54,_⟩ => exact row54
    | ⟨55,_⟩ => exact row55
    | ⟨56,_⟩ => exact row56
    | ⟨57,_⟩ => exact row57
    | ⟨n+58,hn⟩ => omega
  have hc := cover ⟨k/29,by omega⟩ ⟨k%29,by omega⟩
  dsimp only at hc
  rw [show k/29*29 + k%29 = k by omega] at hc
  exact of_decide_eq_true hc

def initialPool (prefixed : Bool) (k : Nat) : List Signature :=
  if prefixed then start k else rawColumns.toList ++ [(0,0),(-1,-1)]

private theorem base (p : Bool) (k : Nat) (hk : k < 1682) : Count (pick k) (initialPool p k) 0 := by
  have zeros : ∀ g : Fin 5, (supp g (0,0)).card ≤ 1 ∧ (supp g (-1,-1)).card ≤ 1 := by decide +kernel
  have members : ∀ x ∈ initialPool p k, (supp (pick k) x).card ≤ 1 := by
    intro x hx
    cases p
    · rcases List.mem_append.mp hx with raw|rest
      · have hraw : ∀ g : Fin 5, rawColumns.toList.all (fun a => decide ((supp g a).card ≤ 1)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp (hraw (pick k)) x raw)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at rest
        rcases rest with rfl|rfl
        · exact (zeros _).1
        · exact (zeros _).2
    · rcases List.mem_append.mp hx with old|extra
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp old
        exact rawOK _ _
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
        rcases extra with rfl|rfl|rfl
        · exact gateOK k hk
        · exact (zeros _).1
        · exact (zeros _).2
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  rw [List.getD_eq_getElem?_getD]
  cases e : (initialPool p k)[j]? with
  | none => exact (zeros _).1
  | some a => exact members a (List.mem_of_getElem? e)

theorem bound (p : Bool) (k : Nat) (hk : k < 1682) (gs : List (Bool × Nat × Nat)) (i : Nat)
    (h : (gs.foldl mix (initialPool p k)).getD i (0,0) = (-1,0)) : 18 ≤ gs.countP Prod.fst := by
  have h' := run (pick k) _ (base p k hk) gs {i}
  simp only [Finset.singleton_biUnion,Finset.card_singleton,Nat.zero_add,h] at h'
  have full : ∀ g : Fin 5, (supp g (-1,0)).card = 19 := by decide +kernel
  rw [full] at h'
  omega
end PEqualNP.Research.PlaneAllFourthOrCount

open PEqualNP.Research.PlaneAllFourthOrCount in
theorem PEqualNP.Research.PlaneAllFourthOrCount : ∀ (p : Bool) (k : Nat), k < 1682 → ∀ (gs : List (Bool × Nat × Nat)) (i : Nat),
    (gs.foldl mix (initialPool p k)).getD i (0,0) = (-1,0) → 18 ≤ gs.countP Prod.fst := bound
