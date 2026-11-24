import PEqualNP.Outside.L_meta_2681

/-! The 14-unit signed-wire budget for the nine-vertex Petersen edge function.
The binary lower bound is the project's checked branch-group bound. A separate
sign argument rules out complemented outputs, including untrimmed circuits. -/

namespace PEqualNP.Research.SignedPetersenBudget

open PEqualNP.Outside.L_meta_2681_aux
open PetersenNine

abbrev Input := Fin 9 → Bool
abbrev Pin := Nat × Bool

structure Program (n : Nat) where
  op : Fin n → Bool
  left : Fin n → Pin
  right : Fin n → Pin
  value : Input → Nat → Bool
  earlier : ∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val
  inputs : ∀ x (i : Fin 9), value x i.val = x i
  zero : ∀ x, value x 9 = false
  step : ∀ x j, value x (10 + j.val) =
    if op j then (value x (left j).1 ^^ (left j).2) && (value x (right j).1 ^^ (right j).2)
    else (value x (left j).1 ^^ (left j).2) || (value x (right j).1 ^^ (right j).2)

def Allowed (paid : Finset Nat) (p : Pin) : Prop :=
  p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid

def Computes {n : Nat} (P : Program n) (out : Pin) : Prop :=
  ∀ x, (P.value x out.1 ^^ out.2) = petersenF x

theorem binary_floor {n : Nat} (P : Program n) (out : Pin) (bound : out.1 < 10+n)
    (correct : Computes P out) : 13 ≤ n := by
  obtain ⟨C,fan,cost,ev⟩ := SignedCircuit.compile_spec P.op P.left P.right out P.value
    P.earlier bound P.inputs P.zero P.step
  have lower := petersen_binary_lower C fan (fun x => (ev x).trans (correct x))
  omega

private theorem op_mono (op a b c d : Bool)
    (ac : a = true → c = true) (bd : b = true → d = true) :
    (if op then a && b else a || b) = true →
    (if op then c && d else c || d) = true := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- If complemented pins below a cut can refer only to the distinguished
input or the constant, every wire through the cut is monotone on each
fixed value of the distinguished input. -/
theorem monotone_to_cut {n cut : Nat} (P : Program n) (bound : cut < 10+n)
    (signs : ∀ j : Fin n, 10+j.val ≤ cut →
      ∀ p ∈ [P.left j, P.right j], p.2 = true → p.1 = 0 ∨ p.1 = 9)
    (x y : Input) (raw : ∀ i, x i = true → y i = true) (fixed : x 0 = y 0) :
    ∀ i ≤ cut, P.value x i = true → P.value y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro upto
    by_cases seed : i < 9
    · let a : Fin 9 := ⟨i,seed⟩
      simpa only [← show a.val = i from rfl, P.inputs] using raw a
    by_cases zero : i = 9
    · subst i
      simp [P.zero]
    let j : Fin n := ⟨i - 10, by omega⟩
    have atGate : 10 + j.val = i := by dsimp [j]; omega
    have pin (p : Pin) (member : p ∈ [P.left j, P.right j]) (lt : p.1 < i) :
        (P.value x p.1 ^^ p.2) = true → (P.value y p.1 ^^ p.2) = true := by
      cases phase : p.2 with
      | false => simpa using ih p.1 lt (by omega)
      | true =>
        have tag := signs j (atGate ▸ upto) p member phase
        rcases tag with free|const
        · have eq : P.value x 0 = P.value y 0 := (P.inputs x 0).trans (fixed.trans (P.inputs y 0).symm)
          rw [free,eq]
          exact id
        · simp [const,P.zero]
    rw [← atGate,P.step,P.step]
    apply op_mono
    · exact pin (P.left j) (by simp) (atGate ▸ (P.earlier j).1)
    · exact pin (P.right j) (by simp) (atGate ▸ (P.earlier j).2)

/-- With only one paid source, a complemented output is antitone in all
eight ordinary inputs when the distinguished input is fixed. -/
theorem output_antitone {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (only : paid.card ≤ 1) (bound : out.1 < 10+n) (outOK : Allowed paid out)
    (pins : ∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j))
    (sign : out.2 = true) (x y : Input)
    (xy : ∀ i, x i = true → y i = true) (fixed : x 0 = y 0) :
    (P.value y out.1 ^^ out.2) = true → (P.value x out.1 ^^ out.2) = true := by
  have rising : P.value x out.1 = true → P.value y out.1 = true := by
    by_cases seed : out.1 < 9
    · let i : Fin 9 := ⟨out.1,seed⟩
      have vx := P.inputs x i
      have vy := P.inputs y i
      change P.value x out.1 = x i at vx
      change P.value y out.1 = y i at vy
      simpa only [vx,vy] using xy i
    by_cases const : out.1 = 9
    · simp [const,P.zero]
    have late : 10 ≤ out.1 := by omega
    have used : out.1 ∈ paid := (outOK sign).resolve_left (by omega) |>.resolve_left (by omega)
    apply monotone_to_cut P bound ?_ x y xy fixed out.1 le_rfl
    intro j before p member phase
    have spec : Allowed paid p ∧ p.1 < 10+j.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact ⟨(pins j).1,(P.earlier j).1⟩
      · exact ⟨(pins j).2,(P.earlier j).2⟩
    rcases spec.1 phase with free|zero|other
    · exact Or.inl free
    · exact Or.inr zero
    · have eq := Finset.card_le_one.mp only _ other _ used
      have := spec.2
      omega
  rw [sign]
  cases hx : P.value x out.1 <;> cases hy : P.value y out.1 <;> simp_all

/-- A prescribed negative row and positive row separate the entire class
of complemented-output programs with at most one paid source. -/
def Separates (a b : Input) : Prop :=
  ∀ {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat), paid.card ≤ 1 →
    out.1 < 10+n → Allowed paid out →
    (∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j)) → out.2 = true →
    (P.value a out.1 ^^ out.2) ≠ false ∨ (P.value b out.1 ^^ out.2) ≠ true

private def projection (i : Fin 9) (invert : Bool) : Program 13 where
  op _ := false
  left _ := (i.val,invert)
  right _ := (i.val,invert)
  value x k := if h : k < 9 then x ⟨k,h⟩ else if k = 9 then false else x i ^^ invert
  earlier := by intro j; have := i.isLt; dsimp; omega
  inputs := by intro x k; simp [k.isLt]
  zero := by simp
  step := by
    intro x j
    have large : ¬10+j.val < 9 := by omega
    have later : 10+j.val ≠ 9 := by omega
    simp [large,later,i.isLt]

private theorem separating_projection {a b : Input} (h : Separates a b)
    (i : Fin 9) (invert : Bool) (canInvert : invert = false ∨ i.val = 0) :
    ((a i ^^ invert) ^^ true) ≠ false ∨ ((b i ^^ invert) ^^ true) ≠ true := by
  let P := projection i invert
  have allowed : ∀ j, Allowed {22} (P.left j) ∧ Allowed {22} (P.right j) := by
    rcases canInvert with none|free
    · simp [P,projection,Allowed,none]
    · simp [P,projection,Allowed,free]
  simpa [P,projection] using
    h P (22,true) {22} (by simp) (by decide) (by simp [Allowed]) allowed rfl

/-- This characterizes every ordered two-row test, including incomparable
rows. If the order or the fixed-coordinate condition fails, a signed input
projection on a thirteen-gate program passes both rows. -/
theorem separates_iff (a b : Input) :
    Separates a b ↔ a 0 = b 0 ∧ ∀ i, a i = true → b i = true := by
  constructor
  · intro h
    have order (i : Fin 9) (on : a i = true) : b i = true := by
      have v := separating_projection h i false (Or.inl rfl)
      cases eb : b i <;> simp_all
    refine ⟨?_,order⟩
    have forward := order 0
    have backward := separating_projection h 0 true (Or.inr rfl)
    cases ea : a 0 <;> cases eb : b 0 <;> simp_all
  · rintro ⟨fixed,order⟩ _ P out paid one bound ok pins sign
    by_contra! both
    have h := output_antitone P out paid one bound ok pins sign a b order fixed both.2
    simp_all

def zeroInput : Input := fun _ => false
def edgeInput : Input := fun i => decide (i = 1 ∨ i = 2)

/-- With at most one paid source, a complemented output must fail on one of
two fixed test inputs, for every circuit length. -/
theorem complemented_pair {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (only : paid.card ≤ 1) (bound : out.1 < 10+n) (outOK : Allowed paid out)
    (pins : ∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j))
    (sign : out.2 = true) :
    (P.value zeroInput out.1 ^^ out.2) ≠ petersenF zeroInput ∨
    (P.value edgeInput out.1 ^^ out.2) ≠ petersenF edgeInput := by
  by_contra! both
  have zero := both.1
  have edge := both.2
  rw [show petersenF zeroInput = false from by decide +kernel] at zero
  rw [show petersenF edgeInput = true from by decide +kernel] at edge
  have h := output_antitone P out paid only bound outOK pins sign zeroInput edgeInput
    (by simp [zeroInput]) (by decide +kernel) edge
  simp_all

/-- A single test never suffices: a thirteen-gate signed circuit with a
complemented last output and exactly one paid source can pass any one row. -/
theorem each_row_attainable (row : Input) : ∃ (P : Program 13) (paid : Finset Nat),
    paid.card = 1 ∧ Allowed paid (22,true) ∧
    (∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j)) ∧
    (P.value row 22 ^^ true) = petersenF row := by
  let goal := petersenF row
  let P : Program 13 := {
    op := fun _ => goal
    left := fun _ => (0,false)
    right := fun _ => (0,true)
    value := fun x k => if h : k < 9 then x ⟨k,h⟩ else if k = 9 then false else !goal
    earlier := fun _ => by simp
    inputs := fun _ i => by simp [i.isLt]
    zero := fun _ => by simp
    step := by
      intro x j
      have large : ¬10+j.val < 9 := by omega
      have later : 10+j.val ≠ 9 := by omega
      simp [large,later] }
  refine ⟨P,{22},by simp,by simp [Allowed],fun _ => by simp [P,Allowed],?_⟩
  simp [P,goal]

/-- The thirteen-binary-gate floor leaves at most one paid source in the
fourteen-unit budget, so every correct program has a positive output. -/
theorem output_positive {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (cost : n + paid.card ≤ 14) (bound : out.1 < 10+n)
    (outOK : Allowed paid out)
    (pins : ∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j))
    (correct : Computes P out) : out.2 = false := by
  by_contra neg
  have floor := binary_floor P out bound correct
  rcases complemented_pair P out paid (by omega) bound outOK pins (Bool.eq_true_of_not_eq_false neg) with h|h
  · exact h (correct _)
  · exact h (correct _)

theorem remaining_budgets {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (cost : n + paid.card ≤ 14) (bound : out.1 < 10+n) (correct : Computes P out) :
    (n = 13 ∧ paid.card ≤ 1) ∨ (n = 14 ∧ paid.card = 0) := by
  have := binary_floor P out bound correct
  omega

/-- Both terminal orientations are allowed by the input language. Under this
budget a complemented output always has an explicit existential error. -/
theorem complemented_mismatch {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (cost : n + paid.card ≤ 14) (bound : out.1 < 10+n)
    (outOK : Allowed paid out) (pins : ∀ j, Allowed paid (P.left j) ∧ Allowed paid (P.right j))
    (neg : out.2 = true) :
    ∃ x, (P.value x out.1 ^^ out.2) ≠ petersenF x := by
  by_contra! correct
  have sign := output_positive P out paid cost bound outOK pins correct
  simp_all

/-- Two paid negated sources leave at most twelve binary gates. The checked
lower bound for arbitrary signed operands already rules out this case. -/
theorem two_paid_mismatch {n : Nat} (P : Program n) (out : Pin) (paid : Finset Nat)
    (cost : n + paid.card ≤ 14) (bound : out.1 < 10+n) (two : 2 ≤ paid.card) :
    ∃ x, (P.value x out.1 ^^ out.2) ≠ petersenF x := by
  by_contra! correct
  have lower := binary_floor P out bound correct
  omega

/-- Fixing any other variable to either bit leaves the output sensitive to
the chosen variable. A singleton, or a pair containing the fixed vertex,
suffices as the negative input. -/
private theorem cofactor_witnesses : ∀ i j : Fin 9, i ≠ j → ∀ b : Bool,
    ∃ w : Fin 9,
      let x : Input := fun k => decide (k = w ∨ (b = true ∧ k = j))
      x j = b ∧ x i = false ∧ petersenF x = false ∧
        petersenF (Function.update x i true) = true := by decide +kernel

theorem robust_influence (i j : Fin 9) (different : i ≠ j) (b : Bool) :
    ∃ x y : Input, x j = b ∧ y j = b ∧ (∀ k, k ≠ i → x k = y k) ∧
      petersenF x = false ∧ petersenF y = true := by
  obtain ⟨w,h⟩ := cofactor_witnesses i j different b
  let x : Input := fun k => decide (k = w ∨ (b = true ∧ k = j))
  obtain ⟨fixed,_,lo,hi⟩ := h
  exact ⟨x,Function.update x i true,fixed,by rw [Function.update_of_ne (Ne.symm different)]; exact fixed,
    fun k hk => by simp [Function.update_of_ne hk],lo,hi⟩

private theorem computed_output_late {n : Nat} (P : Program n) (out : Pin)
    (correct : Computes P out) : 10 ≤ out.1 := by
  by_contra low
  by_cases seed : out.1 < 9
  · let i : Fin 9 := ⟨out.1,seed⟩
    have noEdge : ∀ j : Fin 9, petersenF (fun k => decide (k = j)) = false := by decide +kernel
    have h := correct (fun k => decide (k = i))
    have z := correct zeroInput
    rw [noEdge] at h
    have empty : petersenF zeroInput = false := by decide +kernel
    rw [empty] at z
    have hpin := P.inputs (fun k => decide (k = i)) i
    have zpin := P.inputs zeroInput i
    change P.value (fun k => decide (k = i)) out.1 = decide (i = i) at hpin
    change P.value zeroInput out.1 = false at zpin
    rw [hpin] at h
    rw [zpin] at z
    cases out.2 <;> simp_all
  · have eq : out.1 = 9 := by omega
    have z := correct zeroInput
    have e := correct edgeInput
    rw [eq,P.zero,show petersenF zeroInput = false from by decide +kernel] at z
    rw [eq,P.zero,show petersenF edgeInput = true from by decide +kernel] at e
    simp_all

/-- Take any binary gate that reads a raw variable j. For every other raw
variable i that this gate reads, a correct circuit must read i in another
gate too. The assertion permits arbitrary signs on both operands and output. -/
theorem raw_partner_requires_other_reader {n : Nat} (P : Program n) (out : Pin)
    (bound : out.1 < 10+n) (correct : Computes P out)
    (gate : Fin n) (i j : Fin 9) (different : i ≠ j)
    (partner : (P.left gate).1 = j.val ∨ (P.right gate).1 = j.val) :
    ∃ other : Fin n, other ≠ gate ∧ ((P.left other).1 = i.val ∨ (P.right other).1 = i.val) := by
  by_contra! exclusive
  let side := if (P.left gate).1 = j.val then (P.left gate).2 else (P.right gate).2
  let fixed := (!P.op gate) ^^ side
  obtain ⟨x,y,xj,yj,agree,lo,hi⟩ := robust_influence i j different fixed
  have cut : P.value x (10 + gate.val) = P.value y (10 + gate.val) := by
    rw [P.step,P.step]
    by_cases left : (P.left gate).1 = j.val
    · have fx : ((P.value x (P.left gate).1) ^^ (P.left gate).2) = !P.op gate := by
        rw [left,P.inputs,xj]
        simp [fixed,side,left]
      have fy : ((P.value y (P.left gate).1) ^^ (P.left gate).2) = !P.op gate := by
        rw [left,P.inputs,yj]
        simp [fixed,side,left]
      rw [fx,fy]
      cases P.op gate <;> simp
    · have right := partner.resolve_left left
      have fx : ((P.value x (P.right gate).1) ^^ (P.right gate).2) = !P.op gate := by
        rw [right,P.inputs,xj]
        simp [fixed,side,left]
      have fy : ((P.value y (P.right gate).1) ^^ (P.right gate).2) = !P.op gate := by
        rw [right,P.inputs,yj]
        simp [fixed,side,left]
      rw [fx,fy]
      cases P.op gate <;> simp
  have same : ∀ k < 10+n, k ≠ i.val → P.value x k = P.value y k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk diff
      by_cases input : k < 9
      · let v : Fin 9 := ⟨k,input⟩
        have val : v ≠ i := fun h => diff (congrArg Fin.val h)
        exact (P.inputs x v).trans ((agree v val).trans (P.inputs y v).symm)
      by_cases zero : k = 9
      · simp [zero,P.zero]
      let g : Fin n := ⟨k-10,by omega⟩
      have pos : 10+g.val = k := by dsimp [g]; omega
      by_cases hit : g = gate
      · rw [← pos,hit]
        exact cut
      have unused := exclusive g hit
      have ltL := pos ▸ (P.earlier g).1
      have ltR := pos ▸ (P.earlier g).2
      have vl := ih (P.left g).1 ltL (by omega) unused.1
      have vr := ih (P.right g).1 ltR (by omega) unused.2
      rw [← pos,P.step,P.step,vl,vr]
  have late := computed_output_late P out correct
  have io := i.isLt
  have outEq := same out.1 bound (by omega)
  have fEq := (correct x).symm.trans ((congrArg (fun b => b ^^ out.2) outEq).trans (correct y))
  simp_all

end PEqualNP.Research.SignedPetersenBudget
