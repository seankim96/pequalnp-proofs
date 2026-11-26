import PEqualNP.Research.Plane975SixthAndCodes
import PEqualNP.Research.Plane975AdditionalSixthAnd
import PEqualNP.Research.Plane975Family2Codes
import PEqualNP.Research.Plane975Family3Codes
import PEqualNP.Research.Plane975Family4Codes
import PEqualNP.Research.Plane975Family5Codes
import PEqualNP.Research.Plane975FinalResidual
import PEqualNP.Research.Plane975SixthAndOrBudget

namespace PEqualNP.Research.Plane975AllSixthAndBudget
private def covered (k : Nat) : Prop :=
  (Plane975SixthAndCodes.codeMask k &&& Plane975Mask.omittedFlags == Plane975SixthAndCodes.codeMask k) = true ∨
  ((Plane975AdditionalSixthAnd.codeMask k &&& Plane975AdditionalMask.omittedFlags == Plane975AdditionalSixthAnd.codeMask k) && !(Plane975AdditionalSixthAnd.codeMask k &&& 0x10100001103f3 == Plane975AdditionalSixthAnd.codeMask k)) = true ∨
  ((Plane975Family2Codes.codeMask k &&& Plane975Family2Mask.omittedFlags == Plane975Family2Codes.codeMask k) && [81, 170, 205, 224, 234, 236, 237, 241, 298, 470, 534, 591, 595, 596, 598, 608, 627, 751].contains k) = true ∨
  ((Plane975Family3Codes.codeMask k &&& Plane975Family3Mask.omittedFlags == Plane975Family3Codes.codeMask k) && [173, 177, 204, 266, 301, 332, 365, 394, 563, 564, 566, 576, 687, 691, 692, 694, 704, 755].contains k) = true ∨
  ((Plane975Family4Codes.codeMask k &&& Plane975Family4Mask.omittedFlags == Plane975Family4Codes.codeMask k) && [106, 113, 268, 292, 330, 356, 406, 412, 416, 476, 623, 628, 630, 640].contains k) = true ∨
  ((Plane975Family5Codes.codeMask k &&& Plane975Family5Mask.omittedFlags == Plane975Family5Codes.codeMask k) && [209, 333, 364, 384, 396, 397, 719, 723, 724, 736, 756, 787].contains k) = true ∨
  k ∈ [32, 55, 64, 87, 96, 128, 141, 160, 172, 192, 256, 273, 288, 320, 352, 480, 531, 532, 544, 745, 768, 777, 783, 800]
private instance (k : Nat) : Decidable (covered k) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coversAll : ∀ k : Fin 961, covered k.val := by decide +kernel
end PEqualNP.Research.Plane975AllSixthAndBudget

open PEqualNP.Research PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.Plane975Mask PEqualNP.Research.Plane975AllSixthAndBudget in
theorem PEqualNP.Research.Plane975AllSixthAndBudget : ∀ (k : Fin 961) (tail : List Gate) (out : Nat),
    let f := both (wire base (k.val/31)) (wire base (k.val%31))
    let final := tail.foldl step (base ++ [f])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst ∧ 6 ≤ tail.countP (fun g => !g.1) ∧ 15 ≤ tail.length := by
  intro k tail out
  dsimp only
  intro hp hn
  have a : 9 ≤ tail.countP Prod.fst := by
    rcases coversAll k with h | h | h | h | h | h | h
    · exact PEqualNP.Research.Plane975SixthAndCodes.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975AdditionalSixthAnd.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975Family2Codes.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975Family3Codes.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975Family4Codes.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975Family5Codes.2 k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,h⟩) tail out hp hn
    · exact PEqualNP.Research.Plane975FinalResidual k.val h tail out hp hn
  have b := PEqualNP.Research.Plane975SixthAndOrBudget (k.val/31) (k.val%31) tail out hp hn
  have parts (xs : List Gate) : xs.countP Prod.fst + xs.countP (fun g => !g.1) = xs.length := by
    induction xs with
    | nil => rfl
    | cons g xs ih => cases h : g.1 <;> simp [List.countP_cons,h] <;> omega
  exact ⟨a,b,by have := parts tail; omega⟩
