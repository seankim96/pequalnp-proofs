import PEqualNP.Research.OrderThreePlaneControls

/-! A 63-gate control for each of the 52 possible omitted incident pairs.
Thus every infeasible subset of the tests at that gate budget must include
all 52 positive rows. The full 63-gate question remains separate. -/

namespace PEqualNP.Research.OrderThreePlaneOmissions

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open OrderThreePlanePrefixData OrderThreePlaneControls

private def joinLines (next head : Nat) : List Nat → List BinGate
  | [] => []
  | j :: js => (false,head,j) :: joinLines (next+1) next js

private def addStar (omitted : Nat) (state : List BinGate × List Nat) (point : Nat) :
    List BinGate × List Nat :=
  let lines := (List.range 13).filter (fun w =>
    [0,1,3,9].contains ((point+13-w)%13) && ((2^point ||| 2^(13+w)) != omitted))
  match lines.map (13+·) with
  | [] => state
  | head :: rest =>
    let next := 26+state.1.length
    let chain := joinLines next head rest
    let union := if rest.isEmpty then head else next+chain.length-1
    (state.1 ++ chain ++ [(true,point,union)],state.2 ++ [next+chain.length])

def omitting (i : Fin 52) : List BinGate :=
  let (gates,stars) := (List.range 13).foldl (addStar positive[i.val]!) ([],[])
  match stars with
  | [] => gates
  | head :: rest => gates ++ joinLines (26+gates.length) head rest

private def expected (i : Fin 52) : Signature := (~~~((1 : BitVec 52) <<< i.val),0)

private def summary (i : Fin 52) : Prop :=
  (circuit (omitting i)).size = 63 ∧ output (omitting i) = expected i

private instance (i : Fin 52) : Decidable (summary i) := by unfold summary; infer_instance

set_option maxRecDepth 10000 in
private theorem row0 : summary 0 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row1 : summary 1 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row2 : summary 2 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row3 : summary 3 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row4 : summary 4 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row5 : summary 5 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row6 : summary 6 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row7 : summary 7 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row8 : summary 8 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row9 : summary 9 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row10 : summary 10 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row11 : summary 11 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row12 : summary 12 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row13 : summary 13 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row14 : summary 14 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row15 : summary 15 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row16 : summary 16 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row17 : summary 17 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row18 : summary 18 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row19 : summary 19 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row20 : summary 20 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row21 : summary 21 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row22 : summary 22 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row23 : summary 23 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row24 : summary 24 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row25 : summary 25 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row26 : summary 26 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row27 : summary 27 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row28 : summary 28 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row29 : summary 29 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row30 : summary 30 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row31 : summary 31 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row32 : summary 32 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row33 : summary 33 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row34 : summary 34 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row35 : summary 35 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row36 : summary 36 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row37 : summary 37 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row38 : summary 38 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row39 : summary 39 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row40 : summary 40 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row41 : summary 41 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row42 : summary 42 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row43 : summary 43 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row44 : summary 44 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row45 : summary 45 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row46 : summary 46 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row47 : summary 47 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row48 : summary 48 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row49 : summary 49 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row50 : summary 50 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem row51 : summary 51 := by decide +kernel

private theorem checked (i : Fin 52) : summary i := by
  have cases' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 := by omega
  rcases cases' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51

private theorem read_bit (i j : Fin 52) :
    (expected i).1.getLsbD j.val = decide (j ≠ i) := by
  have bits : ∀ a b : Fin 52, (expected a).1.getLsbD b.val = decide (b ≠ a) := by decide +kernel
  exact bits i j

theorem omit_one (i : Fin 52) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 63 ∧
      (∀ j : Fin 52, C.eval (input (.inl j)) = decide (j ≠ i)) ∧
      (∀ j : Fin 468, C.eval (input (.inr j)) = false) := by
  obtain ⟨size,values⟩ := checked i
  refine ⟨circuit (omitting i),legal_control _,size,?_,?_⟩
  · intro j
    rw [physical_eval,values]
    exact read_bit i j
  · intro j
    rw [physical_eval,values]
    simp [view,expected]

theorem every_positive_is_necessary (S : Set (Fin 52)) (T : Set (Fin 468))
    (infeasible : ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      (∀ j ∈ S, C.eval (input (.inl j)) = true) ∧
      (∀ j ∈ T, C.eval (input (.inr j)) = false)) : ∀ i, i ∈ S := by
  intro i
  by_contra missing
  obtain ⟨C,legal,size,pos,neg⟩ := omit_one i
  apply infeasible
  refine ⟨C,legal,size.le,?_,fun j _ => neg j⟩
  intro j present
  have different : j ≠ i := fun eq => missing (eq ▸ present)
  simpa [different] using pos j

end PEqualNP.Research.OrderThreePlaneOmissions
