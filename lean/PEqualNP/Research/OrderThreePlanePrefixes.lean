import PEqualNP.Research.OrderThreePlaneGates

namespace PEqualNP.Research.OrderThreePlanePrefixes

open OrderThreePlanePrefixData

def correctStage (i : Fin 5) : Bool :=
  let s := table i
  ((pack s.nodes.toList == pack (candidates (bank i))) &&
    (List.range s.nodes.size).all (witnessOk s)) &&
    s.permutations.all (fun p => (initial i).all (fun g => move p g == g))

private def checkBlock (f : Nat → Bool) : Nat → Nat → Bool
  | 0, i => f i
  | d+1, i => checkBlock f d i && checkBlock f d (i+2^d)

private theorem checkBlockJoin {f d i} (lo : checkBlock f d i = true)
    (hi : checkBlock f d (i+2^d) = true) : checkBlock f (d+1) i = true :=
  Bool.and_eq_true_iff.mpr ⟨lo,hi⟩

private theorem checkBlockSound {f : Nat → Bool} (d i j : Nat) (lo : i ≤ j) (hi : j < i+2^d)
    (h : checkBlock f d i = true) : f j = true := by
  induction d generalizing i with
  | zero =>
    have eq : i = j := by omega
    simpa [checkBlock,eq] using h
  | succ d ih =>
    rw [Nat.pow_succ] at hi
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    by_cases early : j < i+2^d
    · exact ih i lo early left
    · exact ih (i+2^d) (by omega) (by omega) right


private def edgeAt (s : Stage) (i : Nat) : Bool :=
  if i < s.nodes.size then witnessOk s i else true

private theorem checked_witnesses (s : Stage) (limit : s.nodes.size ≤ 512)
    (checked : checkBlock (edgeAt s) 9 0 = true) :
    (List.range s.nodes.size).all (witnessOk s) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have bound := List.mem_range.mp hi
  have valid := checkBlockSound 9 0 i (Nat.zero_le _) (by omega) checked
  simpa [edgeAt,bound] using valid

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem edges0 : (List.range (table 0).nodes.size).all (witnessOk (table 0)) = true := by
  apply checked_witnesses
  · decide +kernel
  · iterate 5 (all_goals apply checkBlockJoin)
    all_goals as_aux_lemma => decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem edges1 : (List.range (table 1).nodes.size).all (witnessOk (table 1)) = true := by
  apply checked_witnesses
  · decide +kernel
  · iterate 5 (all_goals apply checkBlockJoin)
    all_goals as_aux_lemma => decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem edges2 : (List.range (table 2).nodes.size).all (witnessOk (table 2)) = true := by
  apply checked_witnesses
  · decide +kernel
  · iterate 5 (all_goals apply checkBlockJoin)
    all_goals as_aux_lemma => decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem edges3 : (List.range (table 3).nodes.size).all (witnessOk (table 3)) = true := by
  apply checked_witnesses
  · decide +kernel
  · iterate 5 (all_goals apply checkBlockJoin)
    all_goals as_aux_lemma => decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem edges4 : (List.range (table 4).nodes.size).all (witnessOk (table 4)) = true := by
  apply checked_witnesses
  · decide +kernel
  · iterate 5 (all_goals apply checkBlockJoin)
    all_goals as_aux_lemma => decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
private theorem checked0 : correctStage 0 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨by decide +kernel,edges0⟩
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
private theorem checked1 : correctStage 1 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨by decide +kernel,edges1⟩
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
private theorem checked2 : correctStage 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨by decide +kernel,edges2⟩
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
private theorem checked3 : correctStage 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨by decide +kernel,edges3⟩
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
private theorem checked4 : correctStage 4 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨by decide +kernel,edges4⟩
  · decide +kernel

theorem checked_stages (i : Fin 5) : correctStage i = true := by
  have alternatives : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases alternatives with rfl|rfl|rfl|rfl|rfl
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4

theorem canonical_coverage (i : Fin 5) (g : Nat) (h : g ∈ candidates (bank i)) :
    Reachable (table i) g := by
  have ok := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (checked_stages i)).1
  have eq := beq_iff_eq.mp ok.1
  have hi := (bit_pack _ _).mpr h
  rw [← eq] at hi
  have mem := (bit_pack _ _).mp hi
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp mem)
  exact nodes_sound _ ok.2 j hj

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem count0 : (candidates (bank 0)).length = 377 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem count1 : (candidates (bank 1)).length = 400 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem count2 : (candidates (bank 2)).length = 407 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem count3 : (candidates (bank 3)).length = 406 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem count4 : (candidates (bank 4)).length = 408 := by decide +kernel

theorem counts :
    ((List.finRange 5).map (fun i => (candidates (bank i)).length)) = [377,400,407,406,408] ∧
    ((List.finRange 5).map (fun i => (table i).representatives.size)) = [4,19,39,20,23] ∧
    (table 0).representatives = #[code true 0 13,code false 0 1,code false 0 13,code false 0 14] := by
  refine ⟨?_,by decide +kernel,by decide +kernel⟩
  change [(candidates (bank 0)).length, (candidates (bank 1)).length,
    (candidates (bank 2)).length, (candidates (bank 3)).length,
    (candidates (bank 4)).length] = _
  rw [count0,count1,count2,count3,count4]

end PEqualNP.Research.OrderThreePlanePrefixes
