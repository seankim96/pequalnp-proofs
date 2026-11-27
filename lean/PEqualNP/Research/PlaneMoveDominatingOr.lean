import Mathlib.Data.List.GetD
namespace PEqualNP.Research.PlaneMoveDominatingOr
abbrev C := Nat → Bool
abbrev G := Bool × Nat × Nat
def wire (s : List C) (j : Nat) := s.getD j (fun _ => false)
def eval (s : List C) (g : G) : C := fun r =>
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def step (s : List C) (g : G) := s ++ [eval s g]
def better (a b : C) :=
  (∀ p : Fin 52, a p.val = true → b p.val = true) ∧
  (∀ j : Fin 468, b (52+j.val) = true → a (52+j.val) = true)
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

def bump (n j : Nat) := if j < n then j else j+1
def rotate (n e j : Nat) := if j < e then bump n j else if j = e then n else j
def relabel (f : Nat → Nat) (g : G) : G := (g.1,f g.2.1,f g.2.2)
private theorem size (gs : List G) (s : List C) : (gs.foldl step s).length = s.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih => simp [ih,step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem keep (gs : List G) (s : List C) (j : Nat) (h : j < s.length) :
    wire (gs.foldl step s) j = wire s j := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step s g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h
private theorem simulate (f : Nat → Nat) (xs : List G) (s t : List C)
    (sync : ∀ d j : Nat, f j = t.length + d ↔ j = s.length + d)
    (input : ∀ j, better (wire s j) (wire t (f j))) :
    ∀ j, better (wire (xs.foldl step s) j) (wire ((xs.map (relabel f)).foldl step t) (f j)) := by
  induction xs generalizing s t with
  | nil => exact input
  | cons g gs ih =>
    apply ih (step s g) (step t (relabel f g))
    · intro d j; simpa [step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using sync (d+1) j
    · intro j
      have h : f j = t.length ↔ j = s.length := by simpa using sync 0 j
      simp only [step,snoc]
      by_cases yes : j = s.length
      · rw [ite_eq_left yes,ite_eq_left (h.mpr yes)]
        exact ⟨fun p => combine g.1 ((input g.2.1).1 p) ((input g.2.2).1 p),
               fun i => combine g.1 ((input g.2.1).2 i) ((input g.2.2).2 i)⟩
      · simpa only [ite_eq_right yes,ite_eq_right (fun z => yes (h.mp z))] using input j

private theorem counts (f : Nat → Nat) (k : Nat) (fixed : ∀ j, f j = k ↔ j = k)
    (gs : List G) : (gs.map (relabel f)).countP (guard k) = gs.countP (guard k) := by
  have eq (g : G) : guard k (relabel f g) = guard k g := by
    apply Bool.eq_iff_iff.mpr
    simp only [guard,relabel,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,fixed]
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons,List.countP_cons,eq,ih]

private theorem legalMap (f : Nat → Nat) (old new : Nat) (gs : List G) (h : legal old gs)
    (lt : ∀ i j : Nat, j < old+i → f j < new+i) : legal new (gs.map (relabel f)) := by
  intro i
  have el := h ⟨i.val,by simpa using i.isLt⟩
  simp only [List.getElem_map,relabel]
  exact ⟨lt _ _ el.1,lt _ _ el.2⟩

end PEqualNP.Research.PlaneMoveDominatingOr
open PEqualNP.Research.PlaneMoveDominatingOr in
theorem PEqualNP.Research.PlaneMoveDominatingOr : ∀ (s : List C) (pre post : List G) (a b c d : Nat),
    let n := s.length
    let e := n+pre.length
    let chosen : G := (false,a,b)
    let early : G := (false,c,d)
    let left := pre.map (relabel (bump n))
    let right := post.map (relabel (rotate n e))
    c < n → d < n → legal n pre → legal (e+1) post →
    better (eval (pre.foldl step s) chosen) (eval s early) →
    legal (n+1) left ∧ legal (e+1) right ∧
    (early :: left ++ right).length = (pre ++ chosen :: post).length ∧
    (∀ k < n, (early :: left ++ right).countP (guard k) =
      (pre ++ chosen :: post).countP (guard k)) ∧
    ∀ o, better (wire ((pre ++ chosen :: post).foldl step s) o)
      (wire ((early :: left ++ right).foldl step s) (rotate n e o)) := by
  intro s pre post a b c d n e chosen early left right hc hd lp rp dom
  have en : n ≤ e := by dsimp [e]; omega
  have bl (i j : Nat) (h : j < n+i) : bump n j < n+1+i := by unfold bump; split <;> omega
  have rl (i j : Nat) (h : j < e+1+i) : rotate n e j < e+1+i := by
    unfold rotate bump; split <;> (try split) <;> omega
  refine ⟨legalMap _ _ _ _ lp bl, legalMap _ _ _ _ rp rl, by simp [left,right]; omega, ?_, ?_⟩
  · intro k hk
    have bx (j) : bump n j = k ↔ j = k := by unfold bump; split <;> omega
    have rx (j) : rotate n e j = k ↔ j = k := by unfold rotate bump; split <;> (try split) <;> omega
    simp only [List.countP_append,List.countP_cons,left,right,counts _ k bx,counts _ k rx]
    simp [early,chosen,PEqualNP.Research.PlaneMoveDominatingOr.guard]
  · let p := pre.foldl step s
    let q := left.foldl step (step s early)
    have plen : p.length = e := size pre s
    have qlen : q.length = e+1 := by simp [q,size,left,step,e,n]; omega
    have pref : ∀ j, better (wire p j) (wire q (bump n j)) := by
      apply simulate
      · intro z j; simp only [step,List.length_append,List.length_singleton]
        unfold bump n; split <;> omega
      · intro j
        change better (wire s j) (wire (s ++ [eval s early]) (bump n j))
        rw [snoc]
        by_cases lt : j < n
        · simpa [bump,lt,show j ≠ s.length by change j ≠ n; omega] using reflB (wire s j)
        · have x := List.getD_eq_default s (fun _ : Nat => false) (show s.length ≤ j by change n ≤ j; omega)
          have y := List.getD_eq_default s (fun _ : Nat => false) (show s.length ≤ j+1 by change n ≤ j+1; omega)
          simp only [bump,ite_eq_right lt,ite_eq_right (show j+1 ≠ s.length by change j+1 ≠ n; omega),wire,x,y]
          exact reflB _
    have earlyValue : wire q n = eval s early := by
      rw [show q = left.foldl step (step s early) by rfl,keep left _ _ (by simp [step,n])]
      simp [step,snoc,n]
    intro o
    change better (wire ((pre ++ chosen :: post).foldl step s) o)
      (wire ((early :: left ++ right).foldl step s) _)
    simp only [List.foldl_append,List.foldl_cons]
    apply simulate (rotate n e) post (step p chosen) q
    · intro z j
      simp only [step,List.length_append,List.length_singleton,plen,qlen]
      unfold rotate bump; split <;> (try split) <;> omega
    · intro j
      simp only [step,snoc,plen]
      by_cases lt : j < e
      · simpa [rotate,lt,show j ≠ e by omega] using pref j
      · by_cases eq : j = e
        · subst j; simpa [rotate,earlyValue] using dom
        · simp only [rotate,ite_eq_right lt,ite_eq_right eq,wire,
            List.getD_eq_default p (fun _ : Nat => false) (by omega : p.length ≤ j),
            List.getD_eq_default q (fun _ : Nat => false) (by omega : q.length ≤ j)]
          exact reflB _
