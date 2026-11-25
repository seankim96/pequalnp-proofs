import PEqualNP.Research.OrderThreePlanePrefixData

namespace PEqualNP.Research.PlanePinProbe
open OrderThreePlanePrefixData

def tested (r : Nat) : Prop :=
  (∃ i : Fin 52, r = positive[i.val]!) ∨ (∃ i : Fin 468, r = negative[i.val]!)

def pin (r : Nat) : Bool := r.testBit 0 && r.testBit 13

private theorem uniqueHit :
    (∀ i : Fin 52, pin positive[i.val]! = true → positive[i.val]! = 8193) ∧
    (∀ i : Fin 468, pin negative[i.val]! = false) := by decide +kernel

/- The tested column of an AND reading wire 26 and an arbitrary other wire is
determined by evaluating that other wire on just the incident flag (0,0). -/
set_option maxRecDepth 8192 in
theorem probe (r : Nat) (hr : tested r) (wire : Nat → Bool) :
    (pin r && wire r) = (if wire 8193 then pin r else false) := by
  cases hp : pin r with
  | false => simp
  | true =>
    have e : r = 8193 := by
      rcases hr with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact uniqueHit.1 i hp
      · rw [uniqueHit.2 i] at hp
        contradiction
    simp [e]

end PEqualNP.Research.PlanePinProbe

open PEqualNP.Research.PlanePinProbe in
theorem PEqualNP.Research.PlanePinProbe :
    ∀ (r : Nat), tested r → ∀ (wire : Nat → Bool) (suffix : Bool → Bool),
      suffix (pin r && wire r) = suffix (if wire 8193 then pin r else false) := by
  intro r hr wire suffix
  exact congrArg suffix (probe r hr wire)
