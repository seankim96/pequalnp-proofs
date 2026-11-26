import PEqualNP.Research.PlanePairAndCount
import PEqualNP.Research.PlaneFlagOrTail
import Mathlib.Data.List.Forall2

namespace PEqualNP.Research.PlaneSingleFlagBound
open PlanePairAndCount

abbrev Sig := OrderThreePlanePrefixData.Signature
def pool (x : Sig) : List Sig := List.ofFn (fun j : Fin 29 => PlaneFlagFourth.col j.val) ++ [x,(0,0),(-1,-1)]
def evalRow (x : Sig) (pos : Bool) (i : Nat) : Row :=
  (pool x).map fun v => if pos then v.1.getLsbD i else v.2.getLsbD i
private abbrev Up (s t : Row) := List.Forall₂ (fun a b : Bool => a = true → b = true) s t
private theorem readUp {s t : Row} (h : Up s t) (i : Nat) : readWire s i = true → readWire t i = true := by
  induction h generalizing i with
  | nil => exact id
  | cons pair rest ih => cases i with
    | zero => exact pair
    | succ j => exact ih j

private theorem memo (gs : List Gate) {s t : Row} (h : Up s t) : Up (gs.foldl step s) (gs.foldl step t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    have hl := readUp h g.2.1
    have hr := readUp h g.2.2
    cases q : g.1 <;> simp_all <;> (try tauto)

private theorem pref (pos : Bool) (i : Nat) (x y : Sig)
    (h : (if pos then x.1.getLsbD i else x.2.getLsbD i) = true →
      (if pos then y.1.getLsbD i else y.2.getLsbD i) = true) : Up (evalRow x pos i) (evalRow y pos i) := by
  simp only [evalRow,pool,List.map_append,List.map_cons,List.map_nil]
  apply List.rel_append _ (List.Forall₂.cons h (List.Forall₂.cons id (List.Forall₂.cons id List.Forall₂.nil)))
  generalize List.map _ (List.ofFn _) = common
  induction common with
  | nil => exact List.Forall₂.nil
  | cons _ _ ih => exact List.Forall₂.cons id ih


-- Rows are bit-packed only for the finite separating-pair test.
def hit (ps : Array (BitVec 32)) (u : BitVec 32) (j : Fin 52) : Bool :=
  ps[j.val]! &&& u == ps[j.val]!
def robust (ps : Array (BitVec 32)) (u : BitVec 32) (group : BitVec 52) : Bool :=
  let all := List.finRange 52
  match all.find? (hit ps u) with
  | none => false
  | some t => !group.getLsbD t.val || all.any (fun j => decide (j ≠ t) && hit ps u j)

private theorem chooseRow {ps u group} (ok : robust ps u group = true) (e : Fin 52)
    (he : group.getLsbD e.val = true) :
    ∃ t : Fin 52, t ≠ e ∧ ps[t.val]! &&& u = ps[t.val]! := by
  unfold robust at ok
  cases h : (List.finRange 52).find? (hit ps u) with
  | none => simp [h] at ok
  | some t =>
    have ht := List.find?_some h
    by_cases same : t = e
    · subst t
      simp only [h,he,Bool.not_true,Bool.false_or,List.any_eq_true] at ok
      obtain ⟨j,_,hj⟩ := ok
      obtain ⟨neq,good⟩ := Bool.and_eq_true_iff.mp hj
      exact ⟨j,of_decide_eq_true neq,eq_of_beq good⟩
    · exact ⟨t,same,eq_of_beq ht⟩

theorem bound (ps ns : Array (BitVec 32)) (ix : Array Nat) (group : BitVec 52)
    (pRows : ∀ j : Fin 52, row ps[j.val]! = evalRow (0,0) true j.val)
    (nRows : ∀ i : Fin 257, ix[i.val]! < 468 ∧ row ns[i.val]! = evalRow (0,0) false ix[i.val]!)
    (cert : ∀ i j : Fin 257, i.val < j.val → robust ps (ns[i.val]! ||| ns[j.val]!) group = true)
    (x : Sig) (e : Fin 52) (gs : List Gate) (o : Nat) (he : group.getLsbD e.val = true)
    (sub : ∀ j : Fin 52, j ≠ e → x.1.getLsbD j.val = false)
    (hp : ∀ j : Fin 52, readWire (gs.foldl step (evalRow x true j.val)) o = true)
    (hn : ∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) :
    9 ≤ gs.countP Prod.fst := by
  let rows := ((List.finRange 52).filter (fun j => decide (j ≠ e))).map (fun j => ps[j.val]!)
  have pair (i j : Fin 257) (lt : i.val < j.val) : ∃ p ∈ rows.toArray, p &&& (ns[i.val]! ||| ns[j.val]!) = p := by
    obtain ⟨t,ne,h⟩ := chooseRow (cert i j lt) e he
    refine ⟨ps[t.val]!,?_,h⟩
    simp only [List.mem_toArray,rows,List.mem_map,List.mem_filter]
    exact ⟨t,⟨by simp,decide_eq_true ne⟩,rfl⟩
  apply PEqualNP.Research.PlanePairAndCount rows.toArray (fun i => ns[i.val]!) pair gs o
  · intro p mem
    have hmem : p ∈ rows := by simpa using mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp hmem
    obtain ⟨_,ne⟩ := List.mem_filter.mp hj
    rw [← eq,pRows j]
    apply readUp (memo gs (pref true j.val x (0,0) _)) o (hp j)
    intro hj
    change x.1.getLsbD j.val = true at hj
    rw [sub j (of_decide_eq_true ne)] at hj
    contradiction
  · intro i
    rw [(nRows i).2]
    cases h : readWire (gs.foldl step (evalRow (0,0) false ix[i.val]!)) o
    · rfl
    · have up := readUp (memo gs (pref false ix[i.val]! (0,0) x (by simp))) o h
      have hh := hn ⟨_,(nRows i).1⟩
      rw [hh] at up
      contradiction


end PEqualNP.Research.PlaneSingleFlagBound
