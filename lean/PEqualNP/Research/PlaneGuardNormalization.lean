import Mathlib.Data.List.GetD
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Push
namespace PEqualNP.Research.PlaneGuardNormalization
abbrev Column := Nat → Bool
abbrev G := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def cheap (g : Bool × Nat × Nat) := g.1 && (g.2.1 == 32 || g.2.2 == 32)
def step (s : List Column) (g : Bool × Nat × Nat) :=
  if g.1 then s ++ [fun r => wire s g.2.1 r && wire s g.2.2 r]
  else s ++ [fun r => wire s g.2.1 r || wire s g.2.2 r]

def val (s : List Column) (g : G) (r : Nat) := if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def dominates (s : List Column) (g k : G) :=
  (∀ p : Fin 52, val s g p.val = true → val s k p.val = true) ∧
  (∀ j : Fin 468, val s k (52+j.val) = true → val s g (52+j.val) = true)


def legal (n : Nat) (g : G) := g.2.1 < n ∧ g.2.2 < n
def valid (n : Nat) (gs : List G) := ∀ i : Fin gs.length, legal (n+i.val) gs[i.val]
def wins (s : List Column) (gs : List G) (o : Nat) :=
  (∀ p : Fin 52, wire (gs.foldl step s) o p.val = true) ∧
  (∀ j : Fin 468, wire (gs.foldl step s) o (52+j.val) = false)
def normal (s : List Column) (gs : List G) := ∀ (pre : List G) (g : G) (tail : List G),
  gs = pre ++ g :: tail → cheap g = false →
  ∀ k : G, legal (s.length+pre.length) k → cheap k = true → ¬dominates (pre.foldl step s) g k
private abbrev rel (r : Nat) (a b : Column) := a r = true → b r = true
private theorem readRel {s t : List Column} {r : Nat} (h : List.Forall₂ (rel r) s t) (i : Nat) :
    rel r (wire s i) (wire t i) := by
  induction h generalizing i with
  | nil => exact id
  | cons ab _ ih => cases i with
    | zero => exact ab
    | succ i => exact ih i
private theorem pushRel {s t : List Column} {r : Nat} (g : G) (h : List.Forall₂ (rel r) s t) :
    List.Forall₂ (rel r) (step s g) (step t g) := by
  have a := readRel h g.2.1
  have b := readRel h g.2.2
  unfold step
  split <;> apply List.rel_append h <;> apply List.Forall₂.cons _ List.Forall₂.nil
  · intro hit
    obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp hit
    exact Bool.and_eq_true_iff.mpr ⟨a x,b y⟩
  · intro hit
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hit).imp a b)
private theorem transfer {s : List Column} {r : Nat} (g k : G) (gs : List G) (o : Nat)
    (h : val s g r = true → val s k r = true) :
    rel r (wire (gs.foldl step (step s g)) o) (wire (gs.foldl step (step s k)) o) := by
  have eqStep (z : G) : step s z = s ++ [val s z] := by cases z with
    | mk op ab => cases op <;> rfl
  have same (u : List Column) : List.Forall₂ (rel r) u u := by
    induction u with
    | nil => exact .nil
    | cons x _ ih => exact .cons id ih
  have init : List.Forall₂ (rel r) (step s g) (step s k) := by
    rw [eqStep,eqStep]; exact List.rel_append (same s) (.cons h .nil)
  suffices ∀ (u v : List Column), List.Forall₂ (rel r) u v →
      List.Forall₂ (rel r) (gs.foldl step u) (gs.foldl step v) from readRel (this _ _ init) o
  induction gs with
  | nil => exact fun _ _ h => h
  | cons x xs ih => exact fun _ _ h => ih _ _ (pushRel x h)
end PEqualNP.Research.PlaneGuardNormalization
open PEqualNP.Research.PlaneGuardNormalization in
theorem PEqualNP.Research.PlaneGuardNormalization : ∀ (s : List Column) (gs : List G) (o : Nat), valid s.length gs → wins s gs o →
  ∃ ys : List G, ys.length = gs.length ∧ valid s.length ys ∧ wins s ys o ∧
    gs.countP cheap ≤ ys.countP cheap ∧ normal s ys := by
  intro s gs o
  suffices aux : ∀ m (xs : List G), xs.length - xs.countP cheap = m →
      valid s.length xs → wins s xs o →
      ∃ ys : List G, ys.length = xs.length ∧ valid s.length ys ∧ wins s ys o ∧
        xs.countP cheap ≤ ys.countP cheap ∧ normal s ys from aux _ gs rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro xs measure hv hw
    by_cases done : normal s xs
    · exact ⟨xs,rfl,hv,hw,Nat.le_refl _,done⟩
    unfold normal at done
    push Not at done
    obtain ⟨pre,g,tail,rfl,ng,k,legalK,guardK,hp,hn⟩ := done
    let ys := pre ++ k :: tail
    have lengthEq : ys.length = (pre ++ g :: tail).length := by simp [ys]
    have up : ys.countP cheap = (pre ++ g :: tail).countP cheap + 1 := by
      simp [ys,List.countP_append,ng,guardK,Nat.add_assoc]
    have nextMeasure : ys.length - ys.countP cheap < m := by
      have := List.countP_le_length (p := cheap) (l := ys)
      omega
    have vh : valid s.length ys := by
      intro i
      let ii : Fin (pre ++ g :: tail).length := ⟨i.val,lengthEq ▸ i.isLt⟩
      have orig := hv ii
      dsimp [ii] at orig
      by_cases left : i.val < pre.length
      · simpa only [ys,List.getElem_append_left left] using orig
      · have le := Nat.le_of_not_gt left
        simp only [ys,List.getElem_append_right le]
        rw [List.getElem_append_right le] at orig
        have headOrTail (j : Nat) (h : j < tail.length + 1)
            (orig : legal (s.length+i.val) ((g :: tail)[j]'(by simpa using h)))
            (zero : j = 0 → legal (s.length+i.val) k) :
            legal (s.length+i.val) ((k :: tail)[j]'(by simpa using h)) := by
          cases j with
          | zero => exact zero rfl
          | succ j => exact orig
        apply headOrTail _ (by have := i.isLt; simp [ys] at this; omega) orig
        intro z
        have eq : i.val = pre.length := by omega
        simpa only [eq] using (show legal (s.length+i.val) k from eq ▸ legalK)
    have win : wins s ys o := by
      constructor
      · intro p
        simp only [ys,List.foldl_append,List.foldl_cons]
        exact transfer g k tail o (hp p) (by simpa only [List.foldl_append,List.foldl_cons] using hw.1 p)
      · intro j
        simp only [ys,List.foldl_append,List.foldl_cons]
        cases hit : wire (tail.foldl step (step (pre.foldl step s) k)) o (52+j.val) with
        | false => rfl
        | true =>
          have bad := transfer k g tail o (hn j) hit
          have neg := hw.2 j
          simp only [List.foldl_append,List.foldl_cons] at neg
          exact False.elim (Bool.noConfusion (bad.symm.trans neg))
    obtain ⟨zs,l,v,w,c,n⟩ := ih _ nextMeasure ys rfl vh win
    exact ⟨zs,l.trans lengthEq,v,w,by omega,n⟩
