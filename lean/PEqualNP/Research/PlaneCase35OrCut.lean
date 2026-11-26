import PEqualNP.Research.PlaneCase35FourthOrBudget
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Research.PlaneCase35OrCut
open PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35FourthOrBudget

private def flags : Array (Fin 52) := #[20,32,21,22,23,34,38,35,39,0,5,8,12,16,24,28,40,45,48]
private def supp (x : Column) : Finset (Fin 19) :=
  if x (52+159) then ∅ else Finset.univ.filter (fun i => x (flags[i.val]!).val)
private def Count (s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp (s.getD j (fun _ => false)))).card ≤ q + W.card

private theorem cutOr (x y : Column) : supp (mix false x y) ⊆ supp x ∪ supp y := by
  cases hx : x (52+159) <;> cases hy : y (52+159) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp (mix true x y) ⊆ supp (if x (52+159) then y else x) := by
  cases hx : x (52+159) <;> cases hy : y (52+159) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Column} {q c : Nat} (h : Count s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp v ⊆ parents.biUnion (fun j => supp (s.getD j (fun _ => false)))) : Count (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp ((s ++ [v]).getD j (fun _ => false))) ⊆
        U.biUnion (fun j => supp (s.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp v := by simpa using hij
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
  · have eq : W.biUnion (fun j => supp ((s ++ [v]).getD j (fun _ => false))) =
        W.biUnion (fun j => supp (s.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega


private theorem appendGate {s : List Column} {q : Nat} (h : Count s q) (op : Bool) (i j : Nat) :
    Count (s ++ [mix op (wire s i) (wire s j)]) (q+(!op).toNat) := by
  cases op
  · apply grow h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
    simpa [wire] using cutOr (wire s i) (wire s j)
  · let k := if wire s i (52+159) then j else i
    apply grow h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd (wire s i) (wire s j)
    change _ ⊆ supp (wire s k)
    cases e : wire s i (52+159) <;> simpa only [k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) {s : List Column} {q : Nat} (h : Count s q) :
    Count (gs.foldl step s) (q+gs.countP (fun g => !g.1)) := by
  induction gs generalizing s q with
  | nil => simpa using h
  | cons g gs ih =>
    obtain ⟨op,i,j⟩ := g
    have next := appendGate h op i j
    have eq : step s (op,i,j) = s ++ [mix op (wire s i) (wire s j)] := by cases op <;> rfl
    simp only [List.foldl_cons,eq]
    cases op <;> simpa [List.countP_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih next

private def raw := List.ofFn (fun j : Fin 28 => input j.val)
private theorem rawRead (i : Fin 28) : wire raw i.val = input i.val := by
  change raw.getD i.val _ = _
  rw [List.getD_eq_getElem _ _ (by simpa only [raw,List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn ..
private theorem lookup (c : Column) (i : Fin 29) : wire (raw ++ [c]) i.val = source c i := by
  by_cases h : i.val < 28
  · rw [wire,List.getD_append _ _ _ _ (by simpa [raw] using h)]
    simpa [source,h,wire] using rawRead ⟨i.val,h⟩
  · have e : i.val = 28 := by omega
    simp [wire,raw,source,e,List.getD_eq_getElem?_getD]
private theorem start : Count raw 0 := by
  have small : ∀ i : Fin 28, (supp (input i.val)).card ≤ 1 := by decide +kernel
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i < 28
  · change (supp (wire raw i)).card ≤ 1
    rw [show wire raw i = input i from rawRead ⟨i,hi⟩]
    exact small ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simpa [raw] using Nat.le_of_not_gt hi)]
    simp [supp]
private theorem addConst {s : List Column} {q : Nat} (h : Count s q) (b : Bool) :
    Count (s ++ [fun _ => b]) q := by
  have empty : supp (fun _ => b) = ∅ := by cases b <;> simp [supp]
  exact grow (c := 0) h _ ∅ (by simp) (by simp [empty])

end PEqualNP.Research.PlaneCase35OrCut
open PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlaneFirstAndSeparation
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35OrCut in
theorem PEqualNP.Research.PlaneCase35OrCut : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29) (gs : List Gate) (o : Nat),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    18 ≤ (!op₃).toNat + (!op₄).toNat + gs.countP (fun g => !g.1) := by
  intro op₃ op₄ l r a b gs o c d pool hp hn
  have h₃ := appendGate start op₃ l.val r.val
  rw [rawRead,rawRead,Nat.zero_add] at h₃
  have h₄ := appendGate h₃ op₄ a.val b.val
  rw [lookup,lookup] at h₄
  have init : Count pool ((!op₃).toNat+(!op₄).toNat) := by
    simpa [pool,raw,c,d,List.append_assoc] using addConst (addConst h₄ false) true
  have cost := run gs init {o}
  have full : supp (wire (gs.foldl step pool) o) = Finset.univ := by
    have neg : wire (gs.foldl step pool) o (52+159) = false := hn (159 : Fin 468)
    simp only [supp,neg,Bool.false_eq_true,ite_false]
    exact Finset.filter_true_of_mem (fun i _ => hp (flags[i.val]!))
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at cost
  change (supp (wire _ o)).card ≤ _ at cost
  rw [full] at cost
  simp only [Finset.card_univ,Fintype.card_fin] at cost
  omega
