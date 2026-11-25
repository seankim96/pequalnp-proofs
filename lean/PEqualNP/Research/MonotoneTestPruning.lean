import PEqualNP.Defs.MetaComplexityLgpMono

/-! A wire may replace another wire if it keeps every already-correct
test bit. This rule works for arbitrary AND/OR tails, including shared
wires. A monotone circuit in the project's representation induces a
program on columns with the same gate count. -/

namespace PEqualNP.Research.MonotoneTestPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {R : Type}
abbrev Column (R : Type) := R → Bool

def combine (op : Bool) (a b : Column R) : Column R :=
  fun r => if op then a r && b r else a r || b r

def Better (goal a b : Column R) : Prop := ∀ r, b r = goal r → a r = goal r

theorem better_refl (goal x : Column R) : Better goal x x := fun _ h => h

theorem better_gate {goal a b c d : Column R} (ac : Better goal a c)
    (bd : Better goal b d) (op : Bool) : Better goal (combine op a b) (combine op c d) := by
  intro r
  have h := ac r
  have k := bd r
  cases op <;> cases hg : goal r <;> cases ha : a r <;> cases hb : b r <;>
    cases hc : c r <;> cases hd : d r <;> simp_all [combine]

inductive Separates (goal : Column R) : Nat → List (Column R) → Prop
  | stop {pool} : goal ∈ pool → Separates goal 0 pool
  | gate {k pool a b} (op : Bool) : a ∈ pool → b ∈ pool →
      Separates goal k (combine op a b :: pool) → Separates goal (k+1) pool

def Improves (goal : Column R) (new old : List (Column R)) : Prop :=
  ∀ b ∈ old, ∃ a ∈ new, Better goal a b

theorem simulate {goal : Column R} {n old} (run : Separates goal n old)
    {new} (sim : Improves goal new old) : Separates goal n new := by
  induction run generalizing new with
  | stop h =>
    obtain ⟨a,ha,improved⟩ := sim _ h
    have eq : a = goal := funext fun r => improved r rfl
    exact .stop (eq ▸ ha)
  | @gate k pool a b op ha hb tail ih =>
    obtain ⟨c,hc,ca⟩ := sim a ha
    obtain ⟨d,hd,db⟩ := sim b hb
    refine .gate op hc hd (ih ?_)
    intro x hx
    rcases List.mem_cons.mp hx with rfl|h
    · exact ⟨_,List.mem_cons_self,better_gate ca db op⟩
    · obtain ⟨y,hy,good⟩ := sim x h
      exact ⟨y,List.mem_cons_of_mem _ hy,good⟩

/-- If the next gate is dominated, omit it and keep the entire tail budget. -/
theorem discard {goal wire : Column R} {pool n}
    (improved : ∃ a ∈ pool, Better goal a wire) (tail : Separates goal n (wire::pool)) :
    Separates goal n pool := by
  apply simulate tail
  intro b hb
  rcases List.mem_cons.mp hb with rfl|h
  · exact improved
  · exact ⟨b,h,better_refl _ _⟩

theorem commute_independent {goal a b : Column R} {pool n} (tail : Separates goal n (b::a::pool)) :
    Separates goal n (a::b::pool) := by
  apply simulate tail
  intro v hv
  have h : v ∈ a::b::pool := by simpa [or_left_comm,or_comm,or_assoc] using hv
  exact ⟨v,h,better_refl _ _⟩

/-- Applying the same row relabeling to all wires transports an entire tail. -/
theorem relabel {goal : Column R} {n pool} (run : Separates goal n pool) (f : R → R) :
    Separates (goal ∘ f) n (pool.map (fun c => c ∘ f)) := by
  induction run with
  | stop h => exact .stop (List.mem_map_of_mem h)
  | gate op ha hb tail ih => exact .gate op (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) ih

private def low : Column R := fun _ => false
private def high : Column R := fun _ => true
private def base (w : List (Column R)) := low :: high :: w
private def read (w : List (Column R)) (i : Nat) := w.getD i low
private def signal (w : List (Column R)) (g : Gate) : Column R :=
  fun r => g.op.eval (g.inputs.map fun i => read w i r)
private def appendWire (w : List (Column R)) (g : Gate) := w ++ [signal w g]

private theorem read_mem (w : List (Column R)) (i : Nat) : read w i ∈ base w := by
  unfold read base
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => simp
  | some v => simp [List.mem_of_getElem? h]

private theorem represented (w : List (Column R)) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ (op : Bool) (a b : Column R), a ∈ base w ∧ b ∈ base w ∧ signal w g = combine op a b := by
  rcases legal with ⟨h,arity⟩
  have ops : g.op = GateOp.and ∨ g.op = GateOp.or := h
  cases ins : g.inputs with
  | nil =>
    rcases ops with andOp|orOp
    · exact ⟨true,high,high,by simp [base],by simp [base],by funext r; simp [signal,ins,andOp,GateOp.eval,combine,high]⟩
    · exact ⟨false,low,low,by simp [base],by simp [base],by funext r; simp [signal,ins,orOp,GateOp.eval,combine,low]⟩
  | cons i rest =>
    cases rest with
    | nil =>
      refine ⟨true,read w i,read w i,read_mem w i,read_mem w i,?_⟩
      funext r
      rcases ops with h|h <;> simp [signal,ins,h,GateOp.eval,combine]
    | cons j rem =>
      have empty : rem = [] := by simpa [ins] using arity
      subst rem
      rcases ops with andOp|orOp
      · exact ⟨true,_,_,read_mem w i,read_mem w j,by funext r; simp [signal,ins,andOp,GateOp.eval,combine]⟩
      · exact ⟨false,_,_,read_mem w i,read_mem w j,by funext r; simp [signal,ins,orOp,GateOp.eval,combine]⟩

private theorem lift_program (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List (Column R)) (goal : Column R) (h : goal ∈ base (gs.foldl appendWire w)) :
    Separates goal gs.length (base w) := by
  induction gs generalizing w with
  | nil => exact .stop h
  | cons g gs ih =>
    obtain ⟨op,a,b,ha,hb,eq⟩ := represented w g (mono g List.mem_cons_self)
    apply Separates.gate op ha hb
    have run := ih (fun t ht => mono t (List.mem_cons_of_mem _ ht)) (appendWire w g) h
    apply simulate run
    intro v hv
    refine ⟨v,?_,better_refl _ _⟩
    simpa [base,appendWire,eq,or_assoc,or_left_comm,or_comm] using hv

private theorem eval_read (w : List (Column R)) (r : R) (i : Nat) :
    read w i r = (w.map (fun x => x r)).getD i false := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem eval_run (gs : List Gate) (w : List (Column R)) (r : R) :
    (gs.foldl appendWire w).map (fun x => x r) =
      gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)])
        (w.map (fun x => x r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,appendWire,List.map_append,List.map_cons,List.map_nil,signal,eval_read]

theorem of_project_circuit (C : Circuit) (legal : Monotone2 C) (w : List (Column R))
    (goal : Column R) (ok : ∀ r, C.eval (w.map (fun x => x r)) = goal r) :
    Separates goal C.size (base w) := by
  apply lift_program C.gates legal
  have eq : read (C.gates.foldl appendWire w) C.output = goal := by
    funext r
    rw [eval_read,eval_run]
    exact ok r
  exact eq ▸ read_mem _ _

end PEqualNP.Research.MonotoneTestPruning
