import PEqualNP.Research.OrderThreePlanePrefixData

/-! Eliminate incident-pair prefix outputs on samples where those outputs are zero.
A fresh wire is represented by none; some embeds every wire already in scope.
This permits arbitrary fan-out. False constants are available without a gate. -/
namespace PEqualNP.Research.OrderThreePlanePinElimination

inductive Wire (α : Type) where
  | zero
  | var (a : α)

def Wire.read (x : α → Bool) : Wire α → Bool
  | .zero => false
  | .var a => x a

def Wire.bind (f : α → Wire β) : Wire α → Wire β
  | .zero => .zero
  | .var a => f a

theorem read_bind (f : α → Wire β) (x : β → Bool) (w : Wire α) :
    (w.bind f).read x = w.read (fun a => (f a).read x) := by cases w <;> rfl

inductive Net : Type → Type 1 where
  | out {α} (w : Wire α) : Net α
  | gate {α} (isAnd : Bool) (a b : Wire α) (tail : Net (Option α)) : Net α

def extend (v : β) (f : α → β) : Option α → β
  | none => v
  | some a => f a

def op (isAnd a b : Bool) := if isAnd then a && b else a || b

def Net.eval : Net α → (α → Bool) → Bool
  | .out w,x => w.read x
  | .gate k a b t,x => t.eval (extend (op k (a.read x) (b.read x)) x)

def Net.size : Net α → Nat
  | .out _ => 0
  | .gate _ _ _ t => 1+t.size

/-- Each gate is counted once even if both of its wires read a pin. -/
def Net.consumers : Net α → (α → Bool) → Nat
  | .out _,_ => 0
  | .gate _ a b t,h =>
    (a.read h || b.read h).toNat + t.consumers (extend false h)

private theorem zero_of_hit (h : α → Bool) (f : α → Wire β)
    (hz : ∀ a, h a = true → f a = .zero) (w : Wire α) (hit : w.read h = true) :
    w.bind f = .zero := by
  cases w with
  | zero => contradiction
  | var a => exact hz a hit

private def weaken (w : Wire β) : Wire (Option β) := w.bind (fun b => .var (some b))

private theorem read_weaken (w : Wire β) (x : β → Bool) (v : Bool) :
    (weaken w).read (extend v x) = w.read x := by cases w <;> rfl

theorem eliminate (p : Net α) (h : α → Bool) (f : α → Wire β)
    (hz : ∀ a, h a = true → f a = .zero) :
    ∃ q : Net β, q.size + p.consumers h = p.size ∧
      ∀ x, q.eval x = p.eval (fun a => (f a).read x) := by
  induction p generalizing β with
  | out w => exact ⟨.out (w.bind f),rfl,fun x => read_bind f x w⟩
  | gate k a b t ih =>
    by_cases hit : (a.read h || b.read h) = true
    · let alias : Wire β := if k then .zero else if a.read h then b.bind f else a.bind f
      have sem (x : β → Bool) : alias.read x =
          op k (a.read (fun i => (f i).read x)) (b.read (fun i => (f i).read x)) := by
        rw [← read_bind,← read_bind]
        cases ha : a.read h with
        | true =>
          rw [zero_of_hit h f hz a ha]
          dsimp only [alias]
          rw [ha]
          cases k <;> simp [op,Wire.read]
        | false =>
          have hb : b.read h = true := by simpa [ha] using hit
          rw [zero_of_hit h f hz b hb]
          dsimp only [alias]
          rw [ha]
          cases k <;> simp [op,Wire.read]
      obtain ⟨q,count,ev⟩ := ih (extend false h) (extend alias f) (by
        intro i hi; cases i with
        | none => contradiction
        | some a => exact hz a hi)
      refine ⟨q,?_,?_⟩
      · simp only [Net.size,Net.consumers,hit]
        change q.size + (1 + t.consumers (extend false h)) = 1 + t.size
        omega
      · intro x
        rw [ev]
        apply congrArg t.eval
        funext i
        cases i with
        | none => exact sem x
        | some _ => rfl
    · let f' : Option _ → Wire (Option β) := extend (.var none) (fun i => weaken (f i))
      obtain ⟨q,count,ev⟩ := ih (extend false h) f' (by
        intro i hi; cases i with
        | none => contradiction
        | some a => simp [f',extend,hz a hi,weaken,Wire.bind])
      refine ⟨.gate k (a.bind f) (b.bind f) q,?_,?_⟩
      · have no : (a.read h || b.read h) = false := by simpa using hit
        simp only [Net.size,Net.consumers,no]
        change (1 + q.size) + (0 + t.consumers (extend false h)) = 1 + t.size
        omega
      · intro x
        simp only [Net.eval,ev,read_bind]
        apply congrArg t.eval
        funext i
        cases i with
        | none => rfl
        | some j => exact read_weaken (f j) x _

abbrev Raw := Fin 26
abbrev WithPins := Sum Raw Bool

def pin : WithPins → Bool
  | .inl _ => false
  | .inr _ => true

def erase : WithPins → Wire Raw
  | .inl i => .var i
  | .inr _ => .zero

def sampleInputs (r : Nat) (i : Raw) : Bool := r.testBit i.val

/-- Case 2 fixes AND(0,13) and AND(2,14) before the 61-gate tail. -/
def withPins (r : Nat) : WithPins → Bool
  | .inl i => sampleInputs r i
  | .inr false => r.testBit 0 && r.testBit 13
  | .inr true => r.testBit 2 && r.testBit 14

open OrderThreePlanePrefixData

def Quiet (r : Nat) : Prop :=
  withPins r (.inr false) = false ∧ withPins r (.inr true) = false

private instance (r : Nat) : Decidable (Quiet r) := by unfold Quiet; infer_instance

theorem pin_rows :
    (∀ i : Fin 52, Quiet positive[i.val]! ↔ i.val ≠ 0 ∧ i.val ≠ 5) ∧
    (∀ i : Fin 468, Quiet negative[i.val]!) := by decide +kernel

private theorem quiet_eq (r : Nat) (quiet : Quiet r) :
    (fun a => (erase a).read (sampleInputs r)) = withPins r := by
  funext a
  cases a with
  | inl _ => rfl
  | inr b =>
    cases b with
    | false => exact quiet.1.symm
    | true => exact quiet.2.symm

theorem case_two_residual (p : Net WithPins) (size : p.size = 61)
    (yes : ∀ i : Fin 52, p.eval (withPins positive[i.val]!) = true)
    (no : ∀ i : Fin 468, p.eval (withPins negative[i.val]!) = false) :
    ∃ q : Net Raw, q.size + p.consumers pin = 61 ∧
      (∀ i : Fin 52, i.val ≠ 0 → i.val ≠ 5 → q.eval (sampleInputs positive[i.val]!) = true) ∧
      (∀ i : Fin 468, q.eval (sampleInputs negative[i.val]!) = false) := by
  obtain ⟨q,count,ev⟩ := eliminate p pin erase (by
    intro a ha; cases a with
    | inl _ => contradiction
    | inr _ => rfl)
  refine ⟨q,count.trans size,?_,?_⟩
  · intro i h0 h5
    rw [ev,quiet_eq _ ((pin_rows.1 i).mpr ⟨h0,h5⟩)]
    exact yes i
  · intro i
    rw [ev,quiet_eq _ (pin_rows.2 i)]
    exact no i

end PEqualNP.Research.OrderThreePlanePinElimination
