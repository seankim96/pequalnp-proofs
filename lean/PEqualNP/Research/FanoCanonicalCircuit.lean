import PEqualNP.Defs

/-! A 27-gate monotone circuit for Fano incidence. Its first two gates
use the lexicographically least possible distinct input pairs even under
all permutations of the fourteen inputs. -/

namespace PEqualNP.Research.FanoCanonicalCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Input := Fin 14 → Bool
def flags : List (Fin 14 × Fin 14) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def target (x : Input) := flags.any fun e => x e.1 && x e.2

def tail : Circuit := ⟨[
  ⟨.or,[14,3]⟩,
  ⟨.and,[16,7]⟩,
  ⟨.or,[15,6]⟩,
  ⟨.and,[18,8]⟩,
  ⟨.or,[1,5]⟩,
  ⟨.or,[20,6]⟩,
  ⟨.and,[21,9]⟩,
  ⟨.or,[0,4]⟩,
  ⟨.or,[23,5]⟩,
  ⟨.and,[24,10]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[26,6]⟩,
  ⟨.and,[27,11]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[29,5]⟩,
  ⟨.and,[30,12]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[32,4]⟩,
  ⟨.and,[33,13]⟩,
  ⟨.or,[17,19]⟩,
  ⟨.or,[35,22]⟩,
  ⟨.or,[36,25]⟩,
  ⟨.or,[37,28]⟩,
  ⟨.or,[38,31]⟩,
  ⟨.or,[39,34]⟩],40⟩

def augmented (x : Input) : List Bool :=
  List.ofFn x ++ [GateOp.or.eval [x 0,x 1], GateOp.or.eval [x 0,x 2]]

theorem size_tail : tail.size = 25 := rfl

theorem monotone_tail : Monotone2 tail := by
  intro g hg
  simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

def rank (a b c d : ℕ) :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

/-- The least pair ranks are one and two. The second pair cannot repeat
the first because the first three variables are different. -/
theorem least_rank (π : Equiv.Perm (Fin 14)) :
    rank 0 1 0 2 ≤ rank (π 0).val (π 1).val (π 0).val (π 2).val := by
  have ab : (π 0).val ≠ (π 1).val := fun h => (by decide : (0:Fin 14) ≠ 1) (π.injective (Fin.ext h))
  have ac : (π 0).val ≠ (π 2).val := fun h => (by decide : (0:Fin 14) ≠ 2) (π.injective (Fin.ext h))
  have bc : (π 1).val ≠ (π 2).val := fun h => (by decide : (1:Fin 14) ≠ 2) (π.injective (Fin.ext h))
  change 227 ≤ (15 * min _ _ + max _ _) * 225 + (15 * min _ _ + max _ _)
  omega

theorem evaluates (x : Input) : tail.eval (augmented x) = target x := by
  have raw : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13] := rfl
  simp only [augmented,raw,tail,Circuit.eval,Circuit.wires,List.foldl_cons,List.foldl_nil,
    List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
    id_eq,Bool.and_true,Bool.or_false,List.cons_append,List.nil_append,List.getD_cons_succ,
    List.getD_cons_zero, target,flags]
  change (((((((((x 0 || x 1) || x 3) && x 7) || (((x 0 || x 2) || x 6) && x 8)) || (((x 1 || x 5) || x 6) && x 9)) || (((x 0 || x 4) || x 5) && x 10)) || (((x 3 || x 4) || x 6) && x 11)) || (((x 2 || x 3) || x 5) && x 12)) || (((x 1 || x 2) || x 4) && x 13)) = ((x 0 && x 7) || ((x 0 && x 8) || ((x 0 && x 10) || ((x 1 && x 7) || ((x 1 && x 9) || ((x 1 && x 13) || ((x 2 && x 8) || ((x 2 && x 12) || ((x 2 && x 13) || ((x 3 && x 7) || ((x 3 && x 11) || ((x 3 && x 12) || ((x 4 && x 10) || ((x 4 && x 11) || ((x 4 && x 13) || ((x 5 && x 9) || ((x 5 && x 10) || ((x 5 && x 12) || ((x 6 && x 8) || ((x 6 && x 9) || (x 6 && x 11)))))))))))))))))))))
  simp only [Bool.and_or_distrib_right]
  ac_rfl


def natFlags : List (Nat × Nat) := flags.map fun e => (e.1.val,e.2.val)

theorem target_spec (x : Input) : target x = decide (∃ i j : Fin 14,
    (i.val,j.val) ∈ natFlags ∧ x i = true ∧ x j = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [target,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨e,he,ha,hb⟩
    exact ⟨e.1,e.2,List.mem_map.mpr ⟨e,he,rfl⟩,ha,hb⟩
  · rintro ⟨i,j,member,hi,hj⟩
    obtain ⟨⟨a,b⟩,he,eq⟩ := List.mem_map.mp member
    have ai : a = i := Fin.ext (congrArg Prod.fst eq)
    have bj : b = j := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(a,b),he,ai ▸ hi,bj ▸ hj⟩

end PEqualNP.Research.FanoCanonicalCircuit
