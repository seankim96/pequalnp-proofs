import Mathlib.Data.List.GetD
namespace PEqualNP.Research.PlanePreloadedAnd
abbrev C := Nat → Bool
abbrev G := Bool × Nat × Nat
def wire (s : List C) (i : Nat) := s.getD i (fun _ => false)
def val (s : List C) (g : G) : C := fun r =>
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def step (s : List C) (g : G) := s ++ [val s g]
def paid (k : Nat) (g : G) := g.1 && !(g.2.1 == k || g.2.2 == k)
def hit (a b : Nat) (g : G) := g.1 && ((g.2.1 == a && g.2.2 == b) || (g.2.1 == b && g.2.2 == a))
def sep (s : List C) (o : Nat) := (∀ p : Fin 52, wire s o p.val = true) ∧
  (∀ j : Fin 468, wire s o (52+j.val) = false)

private def shift (a b : Nat) (g : G) : G :=
  if hit a b g then (false,0,0) else (g.1,g.2.1+1,g.2.2+1)
private theorem operands {a b : Nat} {g : G} (h : hit a b g = true) :
    g = (true,a,b) ∨ g = (true,b,a) := by
  rcases g with ⟨op,i,j⟩
  simp [hit] at h
  obtain ⟨rfl,h⟩ := h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
private theorem sim (s : List C) (a b : Nat) (ha : a < s.length) (hb : b < s.length)
    (v : C) (old : v = val s (true,a,b)) (gs : List G) :
    (gs.map (shift a b)).foldl step (v::s) = v::gs.foldl step s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have next : val (v::s) (shift a b g) = val s g := by
      funext r
      cases e : hit a b g with
      | false => simp only [shift,e,Bool.false_eq_true,ite_false]; rfl
      | true =>
        simp only [shift,e,ite_true]
        change (v r || v r) = val s g r
        rw [Bool.or_self,old]
        rcases operands e with eq | eq <;> rw [eq] <;> simp [val,Bool.and_comm]
    have stepEq : step (v::s) (shift a b g) = v :: step s g := by
      simp only [step,next,List.cons_append]
    simp only [List.map_cons,List.foldl_cons,stepEq]
    apply ih _ (by simp [step]; omega) (by simp [step]; omega)
    rw [old]
    funext r
    simp only [val,ite_true,step,wire,List.getD_append _ _ _ _ ha,List.getD_append _ _ _ _ hb]
private theorem counts (a b k : Nat) (ha : a ≠ k) (hb : b ≠ k) (gs : List G) :
    (gs.map (shift a b)).countP (paid (k+1)) + gs.countP (hit a b) = gs.countP (paid k) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.countP_cons]
    cases e : hit a b g with
    | true =>
      have yes : paid k g = true := by
        rcases operands e with eq | eq <;> simp [eq,paid,ha,hb]
      have no : paid (k+1) (shift a b g) = false := by simp [shift,e,paid]
      rw [no,yes]
      simp only [ite_true,ite_false,Bool.false_eq_true]; omega
    | false =>
      have eq : paid (k+1) (shift a b g) = paid k g := by simp [shift,e,paid]
      rw [eq]
      cases h : paid k g <;> simp only [ite_true,ite_false,Bool.false_eq_true] <;> omega
end PEqualNP.Research.PlanePreloadedAnd
open PEqualNP.Research.PlanePreloadedAnd in
theorem PEqualNP.Research.PlanePreloadedAnd : ∀ (s : List C) (a b k lower : Nat), a < s.length → b < s.length → a ≠ k → b ≠ k →
  (∀ (gs : List G) (o : Nat), sep (gs.foldl step (val s (true,a,b) :: s)) o →
    lower ≤ gs.countP (paid (k+1))) →
  ∀ (gs : List G) (o : Nat), sep (gs.foldl step s) o →
    lower + gs.countP (hit a b) ≤ gs.countP (paid k) := by
  intro s a b k lower ha hb ak bk bound gs o done
  let v := val s (true,a,b)
  have hs := sim s a b ha hb v rfl gs
  have copied : sep ((gs.map (shift a b)).foldl step (v::s)) (o+1) := by
    rw [hs]
    exact done
  have low := bound _ _ copied
  have tally := counts a b k ak bk gs
  omega
