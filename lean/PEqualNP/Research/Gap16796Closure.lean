import PEqualNP.Research.LiveWireBounds
import PEqualNP.Research.Gap16796Witness

namespace PEqualNP.Research.Gap16796Closure
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.LiveWireBounds PEqualNP.Research.Gap16796Witness

def mask : Nat := 2^64 - 1
def table : Nat := 4277071584 * 2^32 + 4276808928
def offsets : List (Nat × Nat) :=
  (List.range 63).map fun d =>
    (d+1, (table ^^^ (table >>> (d+1))) &&& (mask >>> (d+1)))
def negatives : List (Nat × Nat) :=
  ((List.range 64).filter fun r => !(table.testBit r)).map fun r => (r, table)
def inputs : List Nat :=
  (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
    (fun a => encL a (List.range 64))

/- A finite closure, once checked, proves the positive twin of L-meta-16796. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sufficient (T : BT)
    (closed : ∀ x, T.mem x = true → ∃ h, stepOK mask table offsets negatives [] T x h = true)
    (roots : inputs.sublists.all (rootOK table offsets negatives [] T 10) = true) :
    ∀ s : Nat, HasCircuitSize 6 target s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  have lb : ∀ s, HasCircuitSize 6 target s → 11 ≤ s :=
    lb_cert target (List.range 64) mask table inputs offsets negatives [] T 10 11
      rfl (by decide +kernel) (by decide +kernel) rfl
      ⟨fun _ => false,fun _ => true,by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) closed roots
  intro s hs
  exact ⟨⟨gates,16⟩,monotone,lb s hs,computes⟩
end PEqualNP.Research.Gap16796Closure
