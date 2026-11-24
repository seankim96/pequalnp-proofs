import Mathlib.Data.BitVec
import Mathlib.Data.List.FinRange

/-! The two free OR wires in the 24-row punctured Petersen test. Classify
exactly which raw coordinates remain essential when both OR wires are visible. -/

namespace PEqualNP.Research.PetersenTwoOrSeeds

abbrev Word := BitVec 9
abbrev Vertex := Fin 9
abbrev Case := Fin 20

def masks : List Word := [3,5,6,9,10,12,18,20,24,34,36,65,66,68,72,80,96,132,192,260]
def mask (a : Case) : Word := masks[a.val]!
def edges : List Word := [3,6,12,24,17,33,66,132,264,160,320,288]
def target (x : Word) : Bool := edges.any (fun e => (x &&& e) == e)
def active (x m : Word) : Bool := (x &&& m) != 0
def seeds (m x : Word) : Bool × Bool := (active x 17, active x m)
def unit (v : Vertex) : Word := (1 : Word) <<< v.val
def off (v : Vertex) (x : Word) := x &&& ~~~(unit v)
def on (v : Vertex) (x : Word) := x ||| unit v

def seesFlip (m : Word) (v : Vertex) (x : Word) : Bool :=
  seeds m (off v x) == seeds m (on v x) &&
  !target (off v x) && target (on v x)

private def examples : List (List Word) := [
  [18,1,2,4,1,1,2,4,8],
  [20,1,9,4,1,1,2,4,8],
  [16,4,2,4,1,1,2,4,8],
  [0,1,2,5,1,1,2,4,8],
  [16,9,2,18,1,1,2,4,8],
  [16,1,8,4,1,1,2,4,8],
  [16,20,2,4,0,1,2,4,8],
  [16,1,18,4,5,1,2,4,8],
  [16,1,2,16,9,1,2,4,8],
  [16,36,2,4,1,130,2,4,8],
  [16,1,34,4,1,5,2,4,8],
  [80,1,2,4,1,1,257,4,8],
  [16,64,2,4,1,1,2,4,8],
  [16,1,72,4,1,1,260,4,8],
  [16,1,2,68,1,1,10,4,8],
  [16,1,2,4,65,1,18,4,8],
  [16,1,2,4,1,65,34,4,8],
  [16,1,128,4,1,1,2,4,8],
  [16,1,2,4,1,1,130,68,8],
  [16,1,258,4,1,1,2,4,36]]
private def exampleRow (a : Case) (v : Vertex) : Word := (examples[a.val]!)[v.val]!

def exceptional (m : Word) (v : Vertex) : Bool :=
  (m == 9 && v == 0) || (m == 18 && v == 4)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem examples_work : ∀ a : Case, ∀ v : Vertex, exceptional (mask a) v = false →
    seesFlip (mask a) v (exampleRow a v) = true := by decide +kernel

private theorem normalize_off (v : Vertex) (x : Word) :
    off v (off v x) = off v x ∧ off v (on v x) = off v x := by
  simp [off,on,BitVec.and_assoc,BitVec.and_or_distrib_right]

/-- The graph factors through the other eight bits and the two OR wires. -/
def Eliminable (m : Word) (v : Vertex) : Prop :=
  ∃ h : Word → (Bool × Bool) → Bool, ∀ x, target x = h (off v x) (seeds m x)

private def recover (v : Vertex) (rest : Word) (both : Bool × Bool) : Bool :=
  if both.1 && both.2 then target (on v rest) else target rest

private def recoverAt (n : Nat) : Bool :=
  let x := BitVec.ofNat 9 n
  (target x == recover 0 (off 0 x) (seeds 9 x)) &&
  (target x == recover 4 (off 4 x) (seeds 18 x))

set_option maxRecDepth 8192 in
private theorem allRows (p : Nat → Bool) (h : (List.range 512).all p = true) (x : Word) :
    p x.toNat = true := List.all_eq_true.mp h _ (List.mem_range.mpr x.isLt)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem recover_rows (x : Word) :
    target x = recover 0 (off 0 x) (seeds 9 x) ∧
    target x = recover 4 (off 4 x) (seeds 18 x) := by
  have result := allRows recoverAt (by decide +kernel) x
  simpa only [recoverAt,BitVec.ofNat_toNat,BitVec.setWidth_eq,Bool.and_eq_true,beq_iff_eq] using result

private theorem exceptional_eliminable {m : Word} {v : Vertex} (h : exceptional m v = true) :
    Eliminable m v := by
  refine ⟨recover v,fun x => ?_⟩
  have r := recover_rows x
  simp only [exceptional,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact r.1
  · exact r.2

private theorem witness_precludes {m : Word} {v : Vertex} {x : Word}
    (hx : seesFlip m v x = true) : ¬ Eliminable m v := by
  rintro ⟨f,rep⟩
  simp only [seesFlip,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hx
  have clash := rep (off v x)
  rw [(normalize_off v x).1,hx.1.1,← (normalize_off v x).2,← rep (on v x)] at clash
  rw [(normalize_off v x).2,hx.1.2,hx.2] at clash
  contradiction

theorem exact_raw_support (a : Case) (v : Vertex) :
    (∃ x : Word, seesFlip (mask a) v x = true) ↔ exceptional (mask a) v = false := by
  constructor
  · rintro ⟨x,h⟩
    exact Bool.eq_false_of_not_eq_true (fun e => witness_precludes h (exceptional_eliminable e))
  · intro e
    exact ⟨exampleRow a v,examples_work a v e⟩

theorem exactly_two_eliminations (a : Case) (v : Vertex) :
    Eliminable (mask a) v ↔ exceptional (mask a) v = true := by
  constructor
  · intro h
    cases e : exceptional (mask a) v with
    | true => rfl
    | false => exact (witness_precludes (examples_work a v e) h).elim
  · exact exceptional_eliminable

/-- Exactly 178 of the 180 choices of mask and raw wire admit a flip. -/
theorem support_count :
    ((List.finRange 20).flatMap fun a => (List.finRange 9).filter
      fun v => !exceptional (mask a) v).length = 178 := by decide +kernel

def maxima : List Word := [42,50,69,104,116,138,201,208,261,276,385,402]
def below (x y : Word) : Prop := x &&& y = x
def Increasing (f : Word → Bool) : Prop := ∀ x y, below x y → f x = true → f y = true

private def extendsAt (i : Nat) : Bool :=
  let x := BitVec.ofNat 9 i
  target x || maxima.any (fun y => (x &&& y) == x)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem envelope (x : Word) (hx : target x = false) : ∃ y ∈ maxima, below x y := by
  have result := allRows extendsAt (by decide +kernel) x
  simpa only [extendsAt,BitVec.ofNat_toNat,BitVec.setWidth_eq,hx,Bool.false_or,
    List.any_eq_true,beq_iff_eq,below] using result

/-- The twelve edges and twelve maximal negatives suffice for every
monotone Boolean function on the nine original variables. -/
theorem twenty_four_complete (f : Word → Bool) (mono : Increasing f) :
    (∀ x ∈ edges ++ maxima, f x = target x) ↔ f = target := by
  constructor
  · intro rows
    funext x
    cases h : target x with
    | true =>
      obtain ⟨e,he,ex⟩ := List.any_eq_true.mp h
      have yes := List.all_eq_true.mp (show edges.all target = true from by decide +kernel) e he
      exact mono e x (by simpa only [below,beq_iff_eq,BitVec.and_comm e x] using ex)
        ((rows e (List.mem_append_left _ he)).trans yes)
    | false =>
      obtain ⟨y,hy,xy⟩ := envelope x h
      have no := List.all_eq_true.mp (show maxima.all (fun z => !target z) = true from by decide +kernel) y hy
      have fy : f y = false := (rows y (List.mem_append_right _ hy)).trans (by simpa using no)
      exact Bool.eq_false_of_not_eq_true (fun on => Bool.noConfusion ((mono x y xy on).symm.trans fy))
  · rintro rfl x _
    rfl

end PEqualNP.Research.PetersenTwoOrSeeds
