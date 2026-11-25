import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Research.OrderThreePlanePrefixData

namespace PEqualNP.Research.PlaneThirdGate
open PEqualNP.CircuitLowerBounds OrderThreePlanePrefixData

def Tested (r : Nat) := (∃ i : Fin 52, r = positive[i.val]!) ∨
  (∃ i : Fin 468, r = negative[i.val]!)

def pin (r : Nat) := r.testBit 0 && r.testBit 13

private theorem mask_unique :
    (∀ i : Fin 52, pin positive[i.val]! = true → positive[i.val]! = 8193) ∧
    (∀ i : Fin 468, pin negative[i.val]! = false) := by decide +kernel

set_option maxRecDepth 8192 in
theorem collapse (r : Nat) (h : Tested r) (j : Fin 26) (h0 : j.val ≠ 0) (h13 : j.val ≠ 13) :
    (pin r && r.testBit j.val) = false := by
  by_cases v : pin r = true
  · have eqr : r = 8193 := by
      rcases h with ⟨i,rfl⟩|⟨i,rfl⟩
      · exact mask_unique.1 i v
      · rw [mask_unique.2 i] at v
        contradiction
    have off : ∀ k : Fin 26, k.val ≠ 0 → k.val ≠ 13 → (8193 : Nat).testBit k.val = false := by decide +kernel
    rw [v,eqr,off j h0 h13]
    rfl
  · simp [Bool.eq_false_iff.mpr v]

def input (r : Nat) := List.ofFn (fun j : Fin 26 => r.testBit j.val)

def twoGates : List Gate := [⟨.and,[0,13]⟩,⟨.or,[0,1]⟩]

private theorem read_input (r : Nat) (j : Fin 26) : (input r).getD j.val false = r.testBit j.val := by
  rw [input,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

private theorem starts (r : Nat) :
    (Circuit.mk twoGates 0).wires (input r) =
      input r ++ [pin r, r.testBit 0 || r.testBit 1] := by
  have len : (input r).length = 26 := by simp [input]
  have e0 := read_input r (0 : Fin 26)
  have e1 := read_input r (1 : Fin 26)
  have e13 := read_input r (13 : Fin 26)
  change (input r).getD 0 false = _ at e0
  change (input r).getD 1 false = _ at e1
  change (input r).getD 13 false = _ at e13
  simp only [Circuit.wires,twoGates,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,
    GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false]
  simp only [List.getD_append _ _ _ _ (show 0 < (input r).length by omega),
    List.getD_append _ _ _ _ (show 1 < (input r).length by omega), e0,e13,e1]
  simp [pin,List.append_assoc]


def head3 (j : Fin 26) : List Gate := twoGates ++ [⟨.and,[26,j.val]⟩]

private theorem third (r : Nat) (j : Fin 26) (hr : Tested r) (h0 : j.val ≠ 0) (h13 : j.val ≠ 13) :
    (Circuit.mk (head3 j) 0).wires (input r) =
      (Circuit.mk twoGates 0).wires (input r) ++ [false] := by
  let w := (Circuit.mk twoGates 0).wires (input r)
  have len : (input r).length = 26 := by simp [input]
  have earlier : w.getD j.val false = r.testBit j.val := by
    dsimp [w]
    rw [starts,List.getD_append _ _ _ _ (by rw [len]; exact j.isLt),read_input]
  have at26 : w.getD 26 false = pin r := by
    dsimp [w]
    rw [starts,← len]
    simp [List.getD_eq_getElem?_getD]
  unfold Circuit.wires head3
  rw [List.foldl_append]
  change w ++ [GateOp.and.eval [w.getD 26 false,w.getD j.val false]] = w ++ [false]
  simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,at26,earlier,collapse r hr j h0 h13]

/-- After these three gates the complete wire pools agree. All subsequent gates may
read any wire repeatedly, and the output wire is arbitrary. -/
theorem same_tail (r : Nat) (hr : Tested r) (j : Fin 26) (h0 : j.val ≠ 0) (h13 : j.val ≠ 13)
    (tail : List Gate) (out : Nat) :
    (Circuit.mk (head3 j ++ tail) out).eval (input r) =
    (Circuit.mk (head3 1 ++ tail) out).eval (input r) := by
  have eq := (third r j hr h0 h13).trans (third r 1 hr (by decide) (by decide)).symm
  unfold Circuit.eval Circuit.wires
  simp only [List.foldl_append]
  exact congrArg (fun pool => (tail.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) pool).getD out false) eq

end PEqualNP.Research.PlaneThirdGate

open PEqualNP.CircuitLowerBounds PEqualNP.Research.PlaneThirdGate in
theorem PEqualNP.Research.PlaneThirdGate :
    ∀ (r : Nat), Tested r → ∀ j : Fin 26, j.val ≠ 0 → j.val ≠ 13 →
    ∀ (tail : List Gate) (out : Nat),
      (Circuit.mk (head3 j ++ tail) out).eval (input r) =
      (Circuit.mk (head3 1 ++ tail) out).eval (input r) := same_tail
