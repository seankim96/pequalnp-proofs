import PEqualNP.Research.PlaneFlagOrTail

namespace PEqualNP.Research.PlaneFlagTwoAnd
open OrderThreePlanePrefixData PlaneFlagFourth PlaneFlagOrTail

def pack (a b u v w z : Bool) : BitVec 6 :=
  BitVec.ofBool z ++ BitVec.ofBool w ++ BitVec.ofBool v ++ BitVec.ofBool u ++ BitVec.ofBool b ++ BitVec.ofBool a

def view (g : Bool) (x : Signature) : BitVec 6 :=
  pack (x.1.getLsbD (if g then 18 else 8)) (x.1.getLsbD (if g then 25 else 13))
    (x.2.getLsbD (if g then 40 else 49)) (x.2.getLsbD (if g then 19 else 7))
    (x.2.getLsbD (if g then 3 else 9)) (x.2.getLsbD (if g then 25 else 2))

def pre (x : BitVec 6) : Bool :=
  (!x.getLsbD 0 || ((x.getLsbD 2 && x.getLsbD 3) || (x.getLsbD 4 && x.getLsbD 5))) &&
  (!x.getLsbD 1 || ((x.getLsbD 2 && x.getLsbD 4) || (x.getLsbD 3 && x.getLsbD 5)))

def post (c : Bool) (x : BitVec 6) : Bool :=
  !x.getLsbD (if c then 1 else 0) || (x &&& 60 != 0)

def meetCols (a b : Signature) : Signature := (a.1 &&& b.1,a.2 &&& b.2)

private theorem packOr : ∀ a b u v w z a' b' u' v' w' z' : Bool, pack (a || a') (b || b') (u || u') (v || v') (w || w') (z || z') = (pack a b u v w z ||| pack a' b' u' v' w' z') := by decide +kernel

private theorem packAnd : ∀ a b u v w z a' b' u' v' w' z' : Bool, pack (a && a') (b && b') (u && u') (v && v') (w && w') (z && z') = (pack a b u v w z &&& pack a' b' u' v' w' z') := by decide +kernel

private theorem joinView (g : Bool) (a b : Signature) :
    view g (joinCols a b) = (view g a ||| view g b) := by
  simp only [view,joinCols,BitVec.getLsbD_or]
  apply packOr
private theorem meetView (g : Bool) (a b : Signature) :
    view g (meetCols a b) = (view g a &&& view g b) := by
  simp only [view,meetCols,BitVec.getLsbD_and]
  apply packAnd

private theorem atomJoin : ∀ x y : BitVec 6, pre x = true → pre y = true → pre (x ||| y) = true := by decide +kernel
private theorem atomMeet : ∀ x y : BitVec 6, pre x = true → pre y = true →
    ∃ c : Bool, post c (x &&& y) = true := by decide +kernel
private theorem atomPost : ∀ (x : BitVec 6) (c : Bool), pre x = true → post c x = true := by decide +kernel
private theorem postJoin : ∀ (c : Bool) (x y : BitVec 6), post c x = true → post c y = true →
    post c (x ||| y) = true := by decide +kernel

private theorem readOK {P : Signature → Prop} {s : List Signature}
    (h : ∀ x ∈ s, P x) (z : P (0,0)) (i : Nat) : P (s.getD i (0,0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => exact z
  | some a => exact h a (List.mem_of_getElem? e)

private theorem foldOK {P : Signature → Prop} (z : P (0,0))
    (add : ∀ x y, P x → P y → P (joinCols x y)) (s : List Signature) (gs : List (Nat × Nat))
    (h : ∀ x ∈ s, P x) : ∀ x ∈ gs.foldl step s, P x := by
  induction gs generalizing s with
  | nil => exact h
  | cons f gs ih =>
    apply ih
    intro x hx
    rcases List.mem_append.mp hx with old|new
    · exact h x old
    · have eq := List.mem_singleton.mp new
      subst x
      exact add _ _ (readOK h z f.1) (readOK h z f.2)

private theorem oldOK : ∀ (g : Bool) (i : Fin 29), pre (view g (col i.val)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem fourthOK : ∀ (i : Fin 58) (j : Fin 29), ∃ g : Bool,
    pre (view g (gate (i.val*29+j.val) [])) = true := by decide +kernel

def insertMeet (s : List Signature) (f : Nat × Nat) : List Signature :=
  s ++ [meetCols (s.getD f.1 (0,0)) (s.getD f.2 (0,0))]

theorem obstruction (k : Nat) (hk : k < 1682) (before after : List (Nat × Nat)) (f : Nat × Nat) (i : Nat) :
    (after.foldl step (insertMeet (before.foldl step (start k)) f)).getD i (0,0) ≠ (-1,0) := by
  obtain ⟨g,hg⟩ := fourthOK ⟨k/29,by omega⟩ ⟨k%29,by omega⟩
  dsimp only at hg
  rw [show k/29*29+k%29 = k by omega] at hg
  have z : pre (view g (0,0)) = true := by cases g <;> decide +kernel
  have startOK : ∀ a ∈ start k, pre (view g a) = true := by
    intro a ha
    rcases List.mem_append.mp ha with old|extra
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp old
      exact oldOK g j
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
      rcases extra with rfl|rfl|rfl
      · exact hg
      · exact z
      · cases g <;> decide +kernel
  let s := before.foldl step (start k)
  have hs : ∀ a ∈ s, pre (view g a) = true := foldOK z (fun x y hx hy => by
    rw [joinView]; exact atomJoin _ _ hx hy) _ before startOK
  obtain ⟨c,hc⟩ := atomMeet _ _ (readOK hs z f.1) (readOK hs z f.2)
  have hpool : ∀ a ∈ insertMeet s f, post c (view g a) = true := by
    intro a ha
    rcases List.mem_append.mp ha with old|new
    · exact atomPost _ c (hs a old)
    · have e := List.mem_singleton.mp new
      subst a
      rw [meetView]
      exact hc
  have zz := atomPost _ c z
  have hr := readOK (foldOK zz (fun x y hx hy => by rw [joinView]; exact postJoin _ _ _ hx hy) _ after hpool) zz i
  intro eq
  change post c (view g ((after.foldl step (insertMeet (before.foldl step (start k)) f)).getD i (0,0))) = true at hr
  rw [eq] at hr
  have never : ∀ g c : Bool, post c (view g (-1,0)) = false := by decide +kernel
  rw [never] at hr
  contradiction
end PEqualNP.Research.PlaneFlagTwoAnd

open PEqualNP.Research.PlaneFlagTwoAnd PEqualNP.Research.PlaneFlagOrTail in
theorem PEqualNP.Research.PlaneFlagTwoAnd : ∀ k : Nat, k < 1682 → ∀ (before after : List (Nat × Nat)) (f : Nat × Nat) (i : Nat),
    (after.foldl step (insertMeet (before.foldl step (start k)) f)).getD i (0,0) ≠ (-1,0) := obstruction
