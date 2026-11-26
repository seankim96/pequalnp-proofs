import PEqualNP.Research.Plane888FifthAndCodes
import PEqualNP.Research.Plane888SingleDeletion

namespace PEqualNP.Research.Plane888AllFifthAnd
open PlaneFirstAndSeparation PlaneFirstAndBudget Plane888NineFlags Plane888FifthAndCodes

private def gate (k : Nat) := both (wire base (k / 30)) (wire base (k % 30))
private abbrev duplicate (a b : Nat) : Prop :=
  a = b ∨ (a = 0 ∨ a = 14) ∧ b = 27 ∨ (b = 0 ∨ b = 14) ∧ a = 27

private abbrev group (e : Nat) : Prop :=
  (0xf5048ff40f800 : Nat).testBit e = true ∨ (0xafb700a9031c : Nat).testBit e = true

private abbrev classOf (k : Nat) : Prop :=
  codeMask k &&& omittedFlags = codeMask k ∨ duplicate (k / 30) (k % 30) ∨
    let e := (codeMask k).log2
    e < 52 ∧ codeMask k = 2^e ∧ group e

-- The split is over ordered operand pairs, including repeated indices.
set_option maxRecDepth 16000 in
private theorem classes : ∀ k : Fin 900, classOf k.val := by decide +kernel

private theorem columnsOK : ∀ i : Fin 30, ∀ p : Fin 52,
    columns[i.val]!.testBit p.val = wire base i.val p.val := by decide +kernel

-- Wire 27 is the disjunction of inputs 0 and 14 on all 520 specified rows.
private theorem absorbs : ∀ r : Fin 520,
    (wire base 0 r.val && wire base 27 r.val) = wire base 0 r.val ∧
    (wire base 14 r.val && wire base 27 r.val) = wire base 14 r.val := by decide +kernel

private theorem duplicateWire {a b : Nat} (dup : duplicate a b) :
    ∃ t, ∀ r : Fin 520, both (wire base a) (wire base b) r.val = wire base t r.val := by
  rcases dup with rfl | ⟨h,rfl⟩ | ⟨h,rfl⟩
  · exact ⟨a,fun r => Bool.and_self _⟩
  · rcases h with rfl | rfl
    · exact ⟨0,fun r => (absorbs r).1⟩
    · exact ⟨14,fun r => (absorbs r).2⟩
  · rcases h with rfl | rfl
    · exact ⟨0,fun r => (Bool.and_comm _ _).trans (absorbs r).1⟩
    · exact ⟨14,fun r => (Bool.and_comm _ _).trans (absorbs r).2⟩

private theorem readGood {p a b : Nat} {s : List Column} (h : ∀ v ∈ s, good p a b v) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases e : s[j]? with
  | none => simp [good]
  | some v => exact h v (List.mem_of_getElem? e)

private theorem separatedDuplicate {k : Nat} (dup : duplicate (k/30) (k%30)) :
    separated (base ++ [gate k]) := by
  obtain ⟨t,eq⟩ := duplicateWire dup
  obtain ⟨n,pairs⟩ := PEqualNP.Research.Plane888SingleDeletion ⟨2,by decide⟩ (fun _ => false)
    (by decide) (by simp)
  refine ⟨n,?_⟩
  intro i j lt
  obtain ⟨p,h⟩ := pairs i j lt
  have baseH : ∀ w ∈ base, good p.val (52+(n i).val) (52+(n j).val) w :=
    fun w hw => h w (List.mem_append_left _ hw)
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact baseH w old
  · obtain rfl := List.mem_singleton.mp last
    have ep := eq ⟨p.val,by omega⟩
    have ei := eq ⟨52+(n i).val,by have := (n i).isLt; omega⟩
    have ej := eq ⟨52+(n j).val,by have := (n j).isLt; omega⟩
    unfold good gate
    rw [ep,ei,ej]
    exact readGood baseH t

private theorem single {k : Fin 900} (e : Fin 52) (mask : codeMask k.val = 2^e.val) (grp : group e.val) :
    separated (base ++ [gate k.val]) := by
  apply PEqualNP.Research.Plane888SingleDeletion e _ grp
  intro p on
  have l := columnsOK ⟨k.val/30,by omega⟩ p
  have r := columnsOK ⟨k.val%30,by omega⟩ p
  change (wire base (k.val/30) p.val && wire base (k.val%30) p.val) = true at on
  have yes : (codeMask k.val).testBit p.val = true := by
    simpa only [codeMask,Nat.testBit_and,l,r] using on
  rw [mask,Nat.testBit_two_pow] at yes
  exact (of_decide_eq_true yes).symm
end PEqualNP.Research.Plane888AllFifthAnd

open PEqualNP.Research.Plane888AllFifthAnd PEqualNP.Research.Plane888NineFlags
  PEqualNP.Research.Plane888FifthAndCodes PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneFirstAndSeparation in
theorem PEqualNP.Research.Plane888AllFifthAnd : ∀ (k : Fin 900) (tail : List Gate) (out : Nat),
    let f := both (wire base (k.val/30)) (wire base (k.val%30))
    let final := tail.foldl step (base ++ [f])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro k tail out
  dsimp only
  intro hp hn
  rcases classes k with fits | dup | ⟨bound,mask,grp⟩
  · have hk : k.val ∈ codes := List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,beq_iff_eq.mpr fits⟩
    exact PEqualNP.Research.Plane888FifthAndCodes.2 k.val hk tail out hp hn
  · exact separated_bound _ tail out (separatedDuplicate dup) hp hn
  · exact separated_bound _ tail out (single ⟨_,bound⟩ mask grp) hp hn
