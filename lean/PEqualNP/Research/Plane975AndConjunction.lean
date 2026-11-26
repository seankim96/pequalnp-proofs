import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.Plane975AndConjunction
def positive : Array Nat := #[
    8193, 8194, 8200, 8704, 16386, 16388, 16400, 17408, 32772, 32776, 32800, 34816, 65544, 65552,
    65600, 69632, 131073, 131088, 131104, 131200, 262146, 262176, 262208, 262400, 524292, 524352, 524416, 524800,
    1048584, 1048704, 1048832, 1049600, 2097168, 2097408, 2097664, 2099200, 4194336, 4194816, 4195328, 4198400, 8388609, 8388672,
    8389632, 8390656, 16777218, 16777344, 16779264, 16781312, 33554433, 33554436, 33554688, 33558528]

def wire (x : Nat) (w : Fin 31) : Bool :=
  if w.val < 26 then x.testBit w.val
  else if w.val = 26 then x.testBit 0 && x.testBit 13
  else if w.val = 27 then x.testBit 0 || x.testBit 14
  else if w.val = 28 then x.testBit 1 && x.testBit 13
  else if w.val = 29 then x.testBit 1 && x.testBit 18
  else x.testBit 2 && x.testBit 15
def product (a : Fin 31) (rest : List (Fin 31)) (x : Nat) :=
  wire x a && rest.all (wire x)

private def columns : Array Nat := #[0x1010000010001, 0x100000100012, 0x2000001000120, 0x10001204, 0x100022040, 0x1000240400, 0x20002404000, 0x200024080000, 0x4000240800000, 0x2408000008, 0x44080000080, 0x480800000800, 0x8808000008000, 0xf, 0xf0, 0xf00, 0xf000, 0xf0000, 0xf00000, 0xf000000, 0xf0000000, 0xf00000000, 0xf000000000, 0xf0000000000, 0xf00000000000, 0xf000000000000, 0x1, 0x10100000100f1, 0x2, 0x100000, 0x100]
private def mask (a b : Fin 31) := columns[a.val]! &&& columns[b.val]!
private abbrev dup (a b : Fin 31) :=
  a = b ∨ (a.val = 0 ∨ a.val = 14) ∧ b.val = 27 ∨ (b.val = 0 ∨ b.val = 14) ∧ a.val = 27
private abbrev shape (a b : Fin 31) :=
  dup a b ∨ mask a b = 0 ∨ (mask a b).log2 < 52 ∧ mask a b = 2^(mask a b).log2
private theorem shape0 : ∀ b : Fin 31, shape ⟨0,by decide⟩ b := by decide +kernel
private theorem col0 : ∀ p : Fin 52, columns[0]!.testBit p.val = wire positive[p.val]! ⟨0,by decide⟩ := by decide +kernel
private theorem shape1 : ∀ b : Fin 31, shape ⟨1,by decide⟩ b := by decide +kernel
private theorem col1 : ∀ p : Fin 52, columns[1]!.testBit p.val = wire positive[p.val]! ⟨1,by decide⟩ := by decide +kernel
private theorem shape2 : ∀ b : Fin 31, shape ⟨2,by decide⟩ b := by decide +kernel
private theorem col2 : ∀ p : Fin 52, columns[2]!.testBit p.val = wire positive[p.val]! ⟨2,by decide⟩ := by decide +kernel
private theorem shape3 : ∀ b : Fin 31, shape ⟨3,by decide⟩ b := by decide +kernel
private theorem col3 : ∀ p : Fin 52, columns[3]!.testBit p.val = wire positive[p.val]! ⟨3,by decide⟩ := by decide +kernel
private theorem shape4 : ∀ b : Fin 31, shape ⟨4,by decide⟩ b := by decide +kernel
private theorem col4 : ∀ p : Fin 52, columns[4]!.testBit p.val = wire positive[p.val]! ⟨4,by decide⟩ := by decide +kernel
private theorem shape5 : ∀ b : Fin 31, shape ⟨5,by decide⟩ b := by decide +kernel
private theorem col5 : ∀ p : Fin 52, columns[5]!.testBit p.val = wire positive[p.val]! ⟨5,by decide⟩ := by decide +kernel
private theorem shape6 : ∀ b : Fin 31, shape ⟨6,by decide⟩ b := by decide +kernel
private theorem col6 : ∀ p : Fin 52, columns[6]!.testBit p.val = wire positive[p.val]! ⟨6,by decide⟩ := by decide +kernel
private theorem shape7 : ∀ b : Fin 31, shape ⟨7,by decide⟩ b := by decide +kernel
private theorem col7 : ∀ p : Fin 52, columns[7]!.testBit p.val = wire positive[p.val]! ⟨7,by decide⟩ := by decide +kernel
private theorem shape8 : ∀ b : Fin 31, shape ⟨8,by decide⟩ b := by decide +kernel
private theorem col8 : ∀ p : Fin 52, columns[8]!.testBit p.val = wire positive[p.val]! ⟨8,by decide⟩ := by decide +kernel
private theorem shape9 : ∀ b : Fin 31, shape ⟨9,by decide⟩ b := by decide +kernel
private theorem col9 : ∀ p : Fin 52, columns[9]!.testBit p.val = wire positive[p.val]! ⟨9,by decide⟩ := by decide +kernel
private theorem shape10 : ∀ b : Fin 31, shape ⟨10,by decide⟩ b := by decide +kernel
private theorem col10 : ∀ p : Fin 52, columns[10]!.testBit p.val = wire positive[p.val]! ⟨10,by decide⟩ := by decide +kernel
private theorem shape11 : ∀ b : Fin 31, shape ⟨11,by decide⟩ b := by decide +kernel
private theorem col11 : ∀ p : Fin 52, columns[11]!.testBit p.val = wire positive[p.val]! ⟨11,by decide⟩ := by decide +kernel
private theorem shape12 : ∀ b : Fin 31, shape ⟨12,by decide⟩ b := by decide +kernel
private theorem col12 : ∀ p : Fin 52, columns[12]!.testBit p.val = wire positive[p.val]! ⟨12,by decide⟩ := by decide +kernel
private theorem shape13 : ∀ b : Fin 31, shape ⟨13,by decide⟩ b := by decide +kernel
private theorem col13 : ∀ p : Fin 52, columns[13]!.testBit p.val = wire positive[p.val]! ⟨13,by decide⟩ := by decide +kernel
private theorem shape14 : ∀ b : Fin 31, shape ⟨14,by decide⟩ b := by decide +kernel
private theorem col14 : ∀ p : Fin 52, columns[14]!.testBit p.val = wire positive[p.val]! ⟨14,by decide⟩ := by decide +kernel
private theorem shape15 : ∀ b : Fin 31, shape ⟨15,by decide⟩ b := by decide +kernel
private theorem col15 : ∀ p : Fin 52, columns[15]!.testBit p.val = wire positive[p.val]! ⟨15,by decide⟩ := by decide +kernel
private theorem shape16 : ∀ b : Fin 31, shape ⟨16,by decide⟩ b := by decide +kernel
private theorem col16 : ∀ p : Fin 52, columns[16]!.testBit p.val = wire positive[p.val]! ⟨16,by decide⟩ := by decide +kernel
private theorem shape17 : ∀ b : Fin 31, shape ⟨17,by decide⟩ b := by decide +kernel
private theorem col17 : ∀ p : Fin 52, columns[17]!.testBit p.val = wire positive[p.val]! ⟨17,by decide⟩ := by decide +kernel
private theorem shape18 : ∀ b : Fin 31, shape ⟨18,by decide⟩ b := by decide +kernel
private theorem col18 : ∀ p : Fin 52, columns[18]!.testBit p.val = wire positive[p.val]! ⟨18,by decide⟩ := by decide +kernel
private theorem shape19 : ∀ b : Fin 31, shape ⟨19,by decide⟩ b := by decide +kernel
private theorem col19 : ∀ p : Fin 52, columns[19]!.testBit p.val = wire positive[p.val]! ⟨19,by decide⟩ := by decide +kernel
private theorem shape20 : ∀ b : Fin 31, shape ⟨20,by decide⟩ b := by decide +kernel
private theorem col20 : ∀ p : Fin 52, columns[20]!.testBit p.val = wire positive[p.val]! ⟨20,by decide⟩ := by decide +kernel
private theorem shape21 : ∀ b : Fin 31, shape ⟨21,by decide⟩ b := by decide +kernel
private theorem col21 : ∀ p : Fin 52, columns[21]!.testBit p.val = wire positive[p.val]! ⟨21,by decide⟩ := by decide +kernel
private theorem shape22 : ∀ b : Fin 31, shape ⟨22,by decide⟩ b := by decide +kernel
private theorem col22 : ∀ p : Fin 52, columns[22]!.testBit p.val = wire positive[p.val]! ⟨22,by decide⟩ := by decide +kernel
private theorem shape23 : ∀ b : Fin 31, shape ⟨23,by decide⟩ b := by decide +kernel
private theorem col23 : ∀ p : Fin 52, columns[23]!.testBit p.val = wire positive[p.val]! ⟨23,by decide⟩ := by decide +kernel
private theorem shape24 : ∀ b : Fin 31, shape ⟨24,by decide⟩ b := by decide +kernel
private theorem col24 : ∀ p : Fin 52, columns[24]!.testBit p.val = wire positive[p.val]! ⟨24,by decide⟩ := by decide +kernel
private theorem shape25 : ∀ b : Fin 31, shape ⟨25,by decide⟩ b := by decide +kernel
private theorem col25 : ∀ p : Fin 52, columns[25]!.testBit p.val = wire positive[p.val]! ⟨25,by decide⟩ := by decide +kernel
private theorem shape26 : ∀ b : Fin 31, shape ⟨26,by decide⟩ b := by decide +kernel
private theorem col26 : ∀ p : Fin 52, columns[26]!.testBit p.val = wire positive[p.val]! ⟨26,by decide⟩ := by decide +kernel
private theorem shape27 : ∀ b : Fin 31, shape ⟨27,by decide⟩ b := by decide +kernel
private theorem col27 : ∀ p : Fin 52, columns[27]!.testBit p.val = wire positive[p.val]! ⟨27,by decide⟩ := by decide +kernel
private theorem shape28 : ∀ b : Fin 31, shape ⟨28,by decide⟩ b := by decide +kernel
private theorem col28 : ∀ p : Fin 52, columns[28]!.testBit p.val = wire positive[p.val]! ⟨28,by decide⟩ := by decide +kernel
private theorem shape29 : ∀ b : Fin 31, shape ⟨29,by decide⟩ b := by decide +kernel
private theorem col29 : ∀ p : Fin 52, columns[29]!.testBit p.val = wire positive[p.val]! ⟨29,by decide⟩ := by decide +kernel
private theorem shape30 : ∀ b : Fin 31, shape ⟨30,by decide⟩ b := by decide +kernel
private theorem col30 : ∀ p : Fin 52, columns[30]!.testBit p.val = wire positive[p.val]! ⟨30,by decide⟩ := by decide +kernel
private theorem shapes (a : Fin 31) (b : Fin 31) : shape a b := by
  match a with
  | ⟨0,_⟩ => exact shape0 b
  | ⟨1,_⟩ => exact shape1 b
  | ⟨2,_⟩ => exact shape2 b
  | ⟨3,_⟩ => exact shape3 b
  | ⟨4,_⟩ => exact shape4 b
  | ⟨5,_⟩ => exact shape5 b
  | ⟨6,_⟩ => exact shape6 b
  | ⟨7,_⟩ => exact shape7 b
  | ⟨8,_⟩ => exact shape8 b
  | ⟨9,_⟩ => exact shape9 b
  | ⟨10,_⟩ => exact shape10 b
  | ⟨11,_⟩ => exact shape11 b
  | ⟨12,_⟩ => exact shape12 b
  | ⟨13,_⟩ => exact shape13 b
  | ⟨14,_⟩ => exact shape14 b
  | ⟨15,_⟩ => exact shape15 b
  | ⟨16,_⟩ => exact shape16 b
  | ⟨17,_⟩ => exact shape17 b
  | ⟨18,_⟩ => exact shape18 b
  | ⟨19,_⟩ => exact shape19 b
  | ⟨20,_⟩ => exact shape20 b
  | ⟨21,_⟩ => exact shape21 b
  | ⟨22,_⟩ => exact shape22 b
  | ⟨23,_⟩ => exact shape23 b
  | ⟨24,_⟩ => exact shape24 b
  | ⟨25,_⟩ => exact shape25 b
  | ⟨26,_⟩ => exact shape26 b
  | ⟨27,_⟩ => exact shape27 b
  | ⟨28,_⟩ => exact shape28 b
  | ⟨29,_⟩ => exact shape29 b
  | ⟨30,_⟩ => exact shape30 b
  | ⟨i+31,h⟩ => omega
private theorem col (a : Fin 31) (p : Fin 52) : columns[a.val]!.testBit p.val = wire positive[p.val]! a := by
  match a with
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
  | ⟨i+31,h⟩ => omega
private theorem pair (a b : Fin 31) :
    (∃ w : Fin 31, ∀ x : Nat, (wire x a && wire x b) = wire x w) ∨
    ∃ e : Fin 52, ∀ p : Fin 52, (wire positive[p.val]! a && wire positive[p.val]! b) = true → p = e := by
  rcases shapes a b with dup | zero | ⟨lt,h⟩
  · left
    rcases dup with rfl | ⟨k,j⟩ | ⟨k,j⟩
    · exact ⟨a,fun _ => Bool.and_self _⟩
    · refine ⟨a,?_⟩
      intro x
      rcases k with k | k <;> simp [wire,k,j] <;> tauto
    · refine ⟨b,?_⟩
      intro x
      rcases k with k | k <;> simp [wire,k,j] <;> tauto
  · refine Or.inr ⟨0,?_⟩
    intro p on
    have bit := congrArg (fun m : Nat => m.testBit p.val) zero
    exact Bool.noConfusion (show true = false by simpa only [mask,Nat.testBit_and,col,Nat.zero_testBit,on] using bit)
  · refine Or.inr ⟨⟨_,lt⟩,?_⟩
    intro p on
    have bit := congrArg (fun m : Nat => m.testBit p.val) h
    simp only [Nat.testBit_two_pow] at bit
    have yes : (mask a b).testBit p.val = true := by simpa only [mask,Nat.testBit_and,col] using on
    rw [yes] at bit
    exact Fin.ext (of_decide_eq_true bit.symm).symm
end PEqualNP.Research.Plane975AndConjunction

open PEqualNP.Research.Plane975AndConjunction in
theorem PEqualNP.Research.Plane975AndConjunction : ∀ (a : Fin 31) (rest : List (Fin 31)),
    (∃ w : Fin 31, ∀ x : Nat, product a rest x = wire x w) ∨
    ∃ e : Fin 52, ∀ p : Fin 52, product a rest positive[p.val]! = true → p = e := by
  intro a rest
  induction rest generalizing a with
  | nil => exact Or.inl ⟨a,by simp [product]⟩
  | cons b rest ih =>
    have rearrange (x : Nat) : product a (b :: rest) x = ((wire x a && wire x b) && rest.all (wire x)) := by
      simp [product,Bool.and_assoc]
    rcases pair a b with ⟨w,eq⟩ | ⟨e,only⟩
    · have same (x : Nat) : product a (b :: rest) x = product w rest x := by rw [rearrange,eq]; rfl
      simp only [same]
      exact ih w
    · refine Or.inr ⟨e,?_⟩
      intro p on
      rw [rearrange,Bool.and_eq_true] at on
      exact only p on.1
