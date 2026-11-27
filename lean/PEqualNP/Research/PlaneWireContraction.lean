import Mathlib.Data.List.GetD
namespace PEqualNP.Research.PlaneWireContraction
abbrev C := Nat → Bool
abbrev G := Bool × Nat × Nat
def wire (s : List C) (j : Nat) := s.getD j (fun _ => false)
def eval (s : List C) (g : G) : C := fun r =>
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def step (s : List C) (g : G) := s ++ [eval s g]
def better (a b : C) :=
  (∀ p : Fin 52, a p.val = true → b p.val = true) ∧
  (∀ j : Fin 468, b (52+j.val) = true → a (52+j.val) = true)
def redirect (cut alt j : Nat) := if j < cut then j else if j = cut then alt else j-1
def rename (cut alt : Nat) (g : G) : G := (g.1,redirect cut alt g.2.1,redirect cut alt g.2.2)
def legal (n : Nat) (gs : List G) := ∀ i : Fin gs.length,
  let g := gs[i.val]'i.isLt
  g.2.1 < n+i.val ∧ g.2.2 < n+i.val
def guard (k : Nat) (g : G) := g.1 && (g.2.1 == k || g.2.2 == k)

private theorem reflB (a : C) : better a a := ⟨fun _ => id,fun _ => id⟩
private theorem snoc (s : List C) (x : C) (j : Nat) :
    wire (s ++ [x]) j = if j = s.length then x else wire s j := by
  by_cases h : j < s.length
  · rw [ite_eq_right (show j ≠ s.length by omega)]; exact List.getD_append _ _ _ _ h
  · rw [wire,List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : j = s.length
    · simp [e]
    · rw [ite_eq_right e,wire,List.getD_eq_default _ _ (show [x].length ≤ j-s.length by simp; omega),
          List.getD_eq_default _ _ (show s.length ≤ j by omega)]
private theorem combine {a b c d : Bool} (op : Bool) (h : a = true → c = true)
    (k : b = true → d = true) :
    (if op then a && b else a || b) = true → (if op then c && d else c || d) = true := by
  cases op <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.and_eq_true,Bool.or_eq_true]
  · exact Or.imp h k
  · exact fun z => ⟨h z.1,k z.2⟩
private theorem simulate (cut alt : Nat) (ha : alt < cut) (xs : List G) (s t : List C)
    (len : s.length = t.length+1) (lo : cut ≤ t.length)
    (h : ∀ j, better (wire s j) (wire t (redirect cut alt j))) :
    ∀ j, better (wire (xs.foldl step s) j)
      (wire ((xs.map (rename cut alt)).foldl step t) (redirect cut alt j)) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons g xs ih =>
    apply ih (step s g) (step t (rename cut alt g)) (by simp [step,len]) (by simp [step]; omega)
    intro j
    simp only [step,snoc]
    by_cases e : j = s.length
    · have eq : redirect cut alt j = t.length := by simp [redirect,show ¬j < cut by omega,show j ≠ cut by omega]; omega
      rw [ite_eq_left e,ite_eq_left eq]
      exact ⟨fun p => combine g.1 ((h g.2.1).1 p) ((h g.2.2).1 p),
             fun i => combine g.1 ((h g.2.1).2 i) ((h g.2.2).2 i)⟩
    · have ne : redirect cut alt j ≠ t.length := by unfold redirect; split <;> (try split) <;> omega
      simpa only [ite_eq_right e,ite_eq_right ne] using h j
private theorem counts (cut alt k : Nat) (hk : k < cut) (xs : List G) :
    xs.countP (guard k) ≤ (xs.map (rename cut alt)).countP (guard k) := by
  induction xs with
  | nil => simp
  | cons g gs ih =>
    have imp : guard k g = true → guard k (rename cut alt g) = true := by
      simp only [guard,rename,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
      rintro ⟨a,b|b⟩
      · exact ⟨a,Or.inl (by simp [b,redirect,hk])⟩
      · exact ⟨a,Or.inr (by simp [b,redirect,hk])⟩
    simp only [List.map_cons,List.countP_cons]
    split <;> split <;> simp_all <;> omega
end PEqualNP.Research.PlaneWireContraction
open PEqualNP.Research.PlaneWireContraction in
theorem PEqualNP.Research.PlaneWireContraction : ∀ (s : List C) (g : G) (tail : List G) (alt : Nat), alt < s.length →
  better (eval s g) (wire s alt) → legal (s.length+1) tail →
  let ys := tail.map (rename s.length alt)
  legal s.length ys ∧ ys.length + 1 = (g :: tail).length ∧
  (∀ o, better (wire (tail.foldl step (step s g)) o)
    (wire (ys.foldl step s) (redirect s.length alt o))) ∧
  ∀ k < s.length, tail.countP (guard k) ≤ ys.countP (guard k) := by
  intro s g tail alt ha dom hv ys
  refine ⟨?_,by simp [ys],?_,fun k hk => counts _ _ _ hk _⟩
  · intro i
    have hl := hv ⟨i.val,by simpa [ys] using i.isLt⟩
    have lift (j : Nat) (h : j < s.length+1+i.val) : redirect s.length alt j < s.length+i.val := by
      unfold redirect; split <;> (try split) <;> omega
    simp only [ys,List.getElem_map,rename]
    exact ⟨lift _ hl.1,lift _ hl.2⟩
  · apply simulate _ _ ha _ _ _ (by simp [step]) (by omega)
    intro j
    simp only [step,snoc]
    by_cases e : j = s.length
    · simpa [e,redirect] using dom
    · rw [ite_eq_right e]
      by_cases l : j < s.length
      · simpa [redirect,l] using reflB (wire s j)
      · simp only [redirect,ite_eq_right l,ite_eq_right e,wire,List.getD_eq_default _ _ (show s.length ≤ j by omega),
            List.getD_eq_default _ _ (show s.length ≤ j-1 by omega)]
        exact reflB _
