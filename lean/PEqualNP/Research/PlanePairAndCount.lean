import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Order.Basic

namespace PEqualNP.Research.PlanePairAndCount
abbrev Row := List Bool
abbrev Gate := Bool × Nat × Nat
def readWire (s : Row) (i : Nat) := s.getD i false
def step (s : Row) (g : Gate) : Row :=
  let x := readWire s g.2.1
  let y := readWire s g.2.2
  s ++ [if g.1 then x && y else x || y]
def ands : List Gate → Nat
  | [] => 0
  | g :: gs => if g.1 then ands gs + 1 else ands gs
def color : List Gate → Row → Nat
  | [], _ => 0
  | g :: gs, s =>
    let rest := color gs (step s g)
    if g.1 then 2*rest + (readWire s g.2.1).toNat else rest
private theorem bounded (gs : List Gate) (s : Row) : color gs s < 2^(ands gs) := by
  induction gs generalizing s with
  | nil => simp [color,ands]
  | cons g gs ih =>
    have h := ih (step s g)
    cases b : g.1
    · simpa only [color,ands,b,ite_false,Bool.false_eq_true] using h
    · simp only [color,ands,b,ite_true,Nat.pow_succ]
      cases hx : readWire s g.2.1 <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

def Rel (p a b : Row) := ∀ i, readWire p i = true → readWire a i = true ∨ readWire b i = true
private theorem preserve (gs : List Gate) (p a b : Row)
    (la : p.length = a.length) (lb : p.length = b.length) (r : Rel p a b)
    (eq : color gs a = color gs b) : Rel (gs.foldl step p) (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing p a b with
  | nil => exact r
  | cons g gs ih =>
    have he : color gs (step a g) = color gs (step b g) := by
      cases h : g.1 <;> simp [color,h] at eq <;>
        cases hx : readWire a g.2.1 <;> cases hy : readWire b g.2.1 <;> simp_all <;> omega
    apply ih _ _ _ (by simp [step,la]) (by simp [step,lb]) _ he
    intro i hi
    by_cases idx : i = p.length
    · subst i
      have aux (s : Row) : readWire (step s g) s.length =
          (if g.1 then readWire s g.2.1 && readWire s g.2.2 else readWire s g.2.1 || readWire s g.2.2) := by simp [readWire,step]
      rw [aux] at hi
      rw [la,aux,← la,lb,aux]
      have l := r g.2.1
      have rr := r g.2.2
      cases op : g.1
      · simp_all
        tauto
      · have same : readWire a g.2.1 = readWire b g.2.1 := by
          simp [color,op,he] at eq
          cases ha : readWire a g.2.1 <;> cases hb : readWire b g.2.1 <;> simp_all
        simp_all
    · have aux (s : Row) (ne : i ≠ s.length) : readWire (step s g) i = readWire s i := by
        unfold step readWire
        by_cases lt : i < s.length
        · exact List.getD_append _ _ _ _ lt
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
      rw [aux p idx] at hi
      rw [aux a (by omega),aux b (by omega)]
      exact r i hi

def row (x : BitVec 32) : Row := List.ofFn fun i : Fin 32 => x.getLsbD i.val
private theorem covers (p a b : BitVec 32) (h : p &&& (a ||| b) = p) : Rel (row p) (row a) (row b) := by
  intro i hi
  have get (x : BitVec 32) : readWire (row x) i = x.getLsbD i := by
    by_cases lt : i < 32
    · unfold readWire row
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using lt)]
      simp only [Option.getD_some,List.getElem_ofFn]
    · rw [show readWire (row x) i = false from List.getD_eq_default _ _ (by simpa [row] using Nat.le_of_not_gt lt)]
      exact (BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt lt)).symm
  simp only [get] at hi ⊢
  have hh := congrArg (fun x : BitVec 32 => x.getLsbD i) h
  change (p &&& (a ||| b)).getLsbD i = p.getLsbD i at hh
  simpa only [BitVec.getLsbD_and, BitVec.getLsbD_or, hi, Bool.true_and, Bool.or_eq_true] using hh

theorem bound (positives : Array (BitVec 32)) (negatives : Fin 257 → BitVec 32)
    (pairs : ∀ i j : Fin 257, i.val < j.val → ∃ p ∈ positives, p &&& (negatives i ||| negatives j) = p)
    (gs : List Gate) (o : Nat)
    (hp : ∀ p ∈ positives, readWire (gs.foldl step (row p)) o = true)
    (hn : ∀ j : Fin 257, readWire (gs.foldl step (row (negatives j))) o = false) : 9 ≤ ands gs := by
  let f (j : Fin 257) : Fin (2^(ands gs)) := ⟨_,bounded gs (row (negatives j))⟩
  have diff (i j : Fin 257) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,mem,cov⟩ := pairs i j lt
    have pr := preserve gs (row p) (row (negatives i)) (row (negatives j))
      (by simp [row]) (by simp [row]) (covers _ _ _ cov) (congrArg Fin.val eq)
    have := pr o (hp p mem)
    rw [hn i,hn j] at this
    simp at this
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Fin.ext e)) with h|h
    · exact diff i j h eq
    · exact diff j i h eq.symm
  have hc := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at hc
  by_contra h
  have small : ands gs ≤ 8 := by omega
  have upper := Nat.pow_le_pow_right (by decide : 0 < 2) small
  change 2 ^ ands gs ≤ 256 at upper
  omega
private theorem count_eq (gs : List Gate) : ands gs = gs.countP Prod.fst := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases h : g.1 <;> simp [ands,h,ih]
end PEqualNP.Research.PlanePairAndCount

open PEqualNP.Research.PlanePairAndCount in
theorem PEqualNP.Research.PlanePairAndCount : ∀ (positives : Array (BitVec 32)) (negatives : Fin 257 → BitVec 32),
    (∀ i j : Fin 257, i.val < j.val → ∃ p ∈ positives, p &&& (negatives i ||| negatives j) = p) →
    ∀ (gs : List Gate) (o : Nat),
    (∀ p ∈ positives, readWire (gs.foldl step (row p)) o = true) →
    (∀ j : Fin 257, readWire (gs.foldl step (row (negatives j))) o = false) → 9 ≤ gs.countP Prod.fst := by
  intro ps ns h gs o hp hn
  rw [← count_eq]
  exact bound ps ns h gs o hp hn
