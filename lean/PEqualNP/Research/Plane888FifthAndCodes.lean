import PEqualNP.Research.Plane888NineFlags

namespace PEqualNP.Research.Plane888FifthAndCodes
open PlaneFirstAndSeparation PlaneFirstAndBudget Plane888NineFlags
def columns : Array Nat := #[0x1010000010001, 0x100000100012, 0x2000001000120, 0x10001204, 0x100022040, 0x1000240400, 0x20002404000, 0x200024080000, 0x4000240800000, 0x2408000008, 0x44080000080, 0x480800000800, 0x8808000008000, 0xf, 0xf0, 0xf00, 0xf000, 0xf0000, 0xf00000, 0xf000000, 0xf0000000, 0xf00000000, 0xf000000000, 0xf0000000000, 0xf00000000000, 0xf000000000000, 0x1, 0x10100000100f1, 0x2, 0x100000]
def codeMask (k : Nat) := columns[k / 30]! &&& columns[k % 30]!
def codes := (List.range 900).filter fun k => codeMask k &&& omittedFlags == codeMask k

private theorem columnOK : ∀ i : Fin 30, ∀ p : Fin 52,
    columns[i.val]!.testBit p.val = wire base i.val p.val := by decide +kernel
end PEqualNP.Research.Plane888FifthAndCodes

open PEqualNP.Research.Plane888FifthAndCodes PEqualNP.Research.Plane888NineFlags
  PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane888FifthAndCodes : codes.length = 775 ∧ ∀ k ∈ codes, ∀ (tail : List Gate) (out : Nat),
    let f := both (wire base (k/30)) (wire base (k%30))
    let final := tail.foldl step (base ++ [f])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  refine ⟨by decide +kernel,?_⟩
  intro k hk tail out
  dsimp only
  intro hp hn
  obtain ⟨mem,good⟩ := List.mem_filter.mp hk
  have hlt := List.mem_range.mp mem
  have mask := eq_of_beq good
  apply PEqualNP.Research.Plane888NineFlags [] (k/30) (k%30) tail out _ hp hn
  intro p on
  have l : k / 30 < 30 := by omega
  have r : k % 30 < 30 := by omega
  have x := columnOK ⟨k/30,l⟩ p
  have y := columnOK ⟨k%30,r⟩ p
  change (wire base (k/30) p.val && wire base (k%30) p.val) = true at on
  have v : (codeMask k).testBit p.val = true := by
    simpa only [codeMask,Nat.testBit_and,x,y] using on
  have he := congrArg (fun m : Nat => m.testBit p.val) mask
  change (codeMask k &&& omittedFlags).testBit p.val = (codeMask k).testBit p.val at he
  simpa only [Nat.testBit_and,v,Bool.true_and] using he
