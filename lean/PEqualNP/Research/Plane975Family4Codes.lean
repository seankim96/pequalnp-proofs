import PEqualNP.Research.Plane975Family4Mask

namespace PEqualNP.Research.Plane975Family4Codes
open PlaneFirstAndSeparation PlaneFirstAndBudget Plane975Family4Mask
def columns : Array Nat := #[0x1010000010001, 0x100000100012, 0x2000001000120, 0x10001204, 0x100022040, 0x1000240400, 0x20002404000, 0x200024080000, 0x4000240800000, 0x2408000008, 0x44080000080, 0x480800000800, 0x8808000008000, 0xf, 0xf0, 0xf00, 0xf000, 0xf0000, 0xf00000, 0xf000000, 0xf0000000, 0xf00000000, 0xf000000000, 0xf0000000000, 0xf00000000000, 0xf000000000000, 0x1, 0x10100000100f1, 0x2, 0x100000, 0x100]
def codeMask (k : Nat) := columns[k / 31]! &&& columns[k % 31]!
def codes := (List.range 961).filter fun k => (codeMask k &&& omittedFlags == codeMask k) && [106, 113, 268, 292, 330, 356, 406, 412, 416, 476, 623, 628, 630, 640].contains k

private theorem inputWire (i : Fin 31) : wire base i.val = input i.val := by
  unfold wire base
  rw [List.getD_eq_getElem?_getD]
  have h : i.val < (List.ofFn (fun j : Fin 31 => input j.val)).length := by
    rw [List.length_ofFn]
    exact i.isLt
  rw [List.getElem?_append_left h, List.getElem?_eq_getElem h, List.getElem_ofFn]
  rfl

private theorem col0 : ∀ p : Fin 52, columns[0]!.testBit p.val = (pos p.val).testBit 0 := by decide +kernel
private theorem col1 : ∀ p : Fin 52, columns[1]!.testBit p.val = (pos p.val).testBit 1 := by decide +kernel
private theorem col2 : ∀ p : Fin 52, columns[2]!.testBit p.val = (pos p.val).testBit 2 := by decide +kernel
private theorem col3 : ∀ p : Fin 52, columns[3]!.testBit p.val = (pos p.val).testBit 3 := by decide +kernel
private theorem col4 : ∀ p : Fin 52, columns[4]!.testBit p.val = (pos p.val).testBit 4 := by decide +kernel
private theorem col5 : ∀ p : Fin 52, columns[5]!.testBit p.val = (pos p.val).testBit 5 := by decide +kernel
private theorem col6 : ∀ p : Fin 52, columns[6]!.testBit p.val = (pos p.val).testBit 6 := by decide +kernel
private theorem col7 : ∀ p : Fin 52, columns[7]!.testBit p.val = (pos p.val).testBit 7 := by decide +kernel
private theorem col8 : ∀ p : Fin 52, columns[8]!.testBit p.val = (pos p.val).testBit 8 := by decide +kernel
private theorem col9 : ∀ p : Fin 52, columns[9]!.testBit p.val = (pos p.val).testBit 9 := by decide +kernel
private theorem col10 : ∀ p : Fin 52, columns[10]!.testBit p.val = (pos p.val).testBit 10 := by decide +kernel
private theorem col11 : ∀ p : Fin 52, columns[11]!.testBit p.val = (pos p.val).testBit 11 := by decide +kernel
private theorem col12 : ∀ p : Fin 52, columns[12]!.testBit p.val = (pos p.val).testBit 12 := by decide +kernel
private theorem col13 : ∀ p : Fin 52, columns[13]!.testBit p.val = (pos p.val).testBit 13 := by decide +kernel
private theorem col14 : ∀ p : Fin 52, columns[14]!.testBit p.val = (pos p.val).testBit 14 := by decide +kernel
private theorem col15 : ∀ p : Fin 52, columns[15]!.testBit p.val = (pos p.val).testBit 15 := by decide +kernel
private theorem col16 : ∀ p : Fin 52, columns[16]!.testBit p.val = (pos p.val).testBit 16 := by decide +kernel
private theorem col17 : ∀ p : Fin 52, columns[17]!.testBit p.val = (pos p.val).testBit 17 := by decide +kernel
private theorem col18 : ∀ p : Fin 52, columns[18]!.testBit p.val = (pos p.val).testBit 18 := by decide +kernel
private theorem col19 : ∀ p : Fin 52, columns[19]!.testBit p.val = (pos p.val).testBit 19 := by decide +kernel
private theorem col20 : ∀ p : Fin 52, columns[20]!.testBit p.val = (pos p.val).testBit 20 := by decide +kernel
private theorem col21 : ∀ p : Fin 52, columns[21]!.testBit p.val = (pos p.val).testBit 21 := by decide +kernel
private theorem col22 : ∀ p : Fin 52, columns[22]!.testBit p.val = (pos p.val).testBit 22 := by decide +kernel
private theorem col23 : ∀ p : Fin 52, columns[23]!.testBit p.val = (pos p.val).testBit 23 := by decide +kernel
private theorem col24 : ∀ p : Fin 52, columns[24]!.testBit p.val = (pos p.val).testBit 24 := by decide +kernel
private theorem col25 : ∀ p : Fin 52, columns[25]!.testBit p.val = (pos p.val).testBit 25 := by decide +kernel
private theorem col26 : ∀ p : Fin 52, columns[26]!.testBit p.val = (pos p.val).testBit 26 := by decide +kernel
private theorem col27 : ∀ p : Fin 52, columns[27]!.testBit p.val = (pos p.val).testBit 27 := by decide +kernel
private theorem col28 : ∀ p : Fin 52, columns[28]!.testBit p.val = (pos p.val).testBit 28 := by decide +kernel
private theorem col29 : ∀ p : Fin 52, columns[29]!.testBit p.val = (pos p.val).testBit 29 := by decide +kernel
private theorem col30 : ∀ p : Fin 52, columns[30]!.testBit p.val = (pos p.val).testBit 30 := by decide +kernel
private theorem columnOK (i : Fin 31) (p : Fin 52) :
    columns[i.val]!.testBit p.val = wire base i.val p.val := by
  rw [inputWire]
  simp only [input,if_pos p.isLt]
  match i with
  | ⟨0,_⟩ => exact col0 p
  | ⟨1,_⟩ => exact col1 p
  | ⟨2,_⟩ => exact col2 p
  | ⟨3,_⟩ => exact col3 p
  | ⟨4,_⟩ => exact col4 p
  | ⟨5,_⟩ => exact col5 p
  | ⟨6,_⟩ => exact col6 p
  | ⟨7,_⟩ => exact col7 p
  | ⟨8,_⟩ => exact col8 p
  | ⟨9,_⟩ => exact col9 p
  | ⟨10,_⟩ => exact col10 p
  | ⟨11,_⟩ => exact col11 p
  | ⟨12,_⟩ => exact col12 p
  | ⟨13,_⟩ => exact col13 p
  | ⟨14,_⟩ => exact col14 p
  | ⟨15,_⟩ => exact col15 p
  | ⟨16,_⟩ => exact col16 p
  | ⟨17,_⟩ => exact col17 p
  | ⟨18,_⟩ => exact col18 p
  | ⟨19,_⟩ => exact col19 p
  | ⟨20,_⟩ => exact col20 p
  | ⟨21,_⟩ => exact col21 p
  | ⟨22,_⟩ => exact col22 p
  | ⟨23,_⟩ => exact col23 p
  | ⟨24,_⟩ => exact col24 p
  | ⟨25,_⟩ => exact col25 p
  | ⟨26,_⟩ => exact col26 p
  | ⟨27,_⟩ => exact col27 p
  | ⟨28,_⟩ => exact col28 p
  | ⟨29,_⟩ => exact col29 p
  | ⟨30,_⟩ => exact col30 p
  | ⟨v+31,hv⟩ => omega
end PEqualNP.Research.Plane975Family4Codes

open PEqualNP.Research.Plane975Family4Codes PEqualNP.Research.Plane975Family4Mask
  PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Family4Codes : codes.length = 14 ∧ ∀ k ∈ codes, ∀ (tail : List Gate) (out : Nat),
    let f := both (wire base (k/31)) (wire base (k%31))
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
  have mask := eq_of_beq (Bool.and_eq_true_iff.mp good).1
  apply PEqualNP.Research.Plane975Family4Mask [] (k/31) (k%31) tail out _ hp hn
  intro p on
  have l : k / 31 < 31 := by omega
  have r : k % 31 < 31 := by omega
  have x := columnOK ⟨k/31,l⟩ p
  have y := columnOK ⟨k%31,r⟩ p
  change (wire base (k/31) p.val && wire base (k%31) p.val) = true at on
  have v : (codeMask k).testBit p.val = true := by
    simpa only [codeMask,Nat.testBit_and,x,y] using on
  have he := congrArg (fun m : Nat => m.testBit p.val) mask
  change (codeMask k &&& omittedFlags).testBit p.val = (codeMask k).testBit p.val at he
  simpa only [Nat.testBit_and,v,Bool.true_and] using he
