import PEqualNP.Research.OrderThreePlaneGates
import PEqualNP.Research.MonotoneTestPruning

/-! Connect the finite signatures to the project's Circuit.eval. The
64-gate control passes all rows. The 63-gate control misses only the
incident pair consisting of point zero and line zero. -/

namespace PEqualNP.Research.OrderThreePlaneControls

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open OrderThreePlanePrefixData OrderThreePlanePrefixes MonotoneTestPruning

abbrev Row := Sum (Fin 52) (Fin 468)
def label : Row → Bool
  | .inl _ => true
  | .inr _ => false

def view (s : Signature) : Row → Bool
  | .inl i => s.1.getLsbD i.val
  | .inr i => s.2.getLsbD i.val

def mask : Row → Nat
  | .inl i => positive[i.val]!
  | .inr i => negative[i.val]!

def input (r : Row) := (List.range 26).map (fun i => (mask r).testBit i)

theorem view_binary (op : Bool) (a b : Signature) (r : Row) :
    view (binary op a b) r = combine op (view a) (view b) r := by
  cases op <;> cases r <;> simp [view,binary,combine]

private theorem subset_bits {n : Nat} (a b : BitVec n) :
    a &&& b = a ↔ ∀ i : Fin n, a.getLsbD i.val = true → b.getLsbD i.val = true := by
  constructor
  · intro h i hi
    have e := congrArg (fun z : BitVec n => z.getLsbD i.val) h
    change (a &&& b).getLsbD i.val = a.getLsbD i.val at e
    simpa [hi] using e
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    cases ha : a.getLsbD i with
    | false => rfl
    | true => simp [h ⟨i,hi⟩ ha]

theorem dominance_exact (a b : Signature) :
    dominates a b = true ↔ Better label (view a) (view b) := by
  simp only [dominates,Bool.and_eq_true,beq_iff_eq,subset_bits]
  constructor
  · rintro ⟨pos,neg⟩ r h
    cases r with
    | inl i => exact pos i h
    | inr i =>
      change b.2.getLsbD i.val = false at h
      change a.2.getLsbD i.val = false
      cases v : a.2.getLsbD i.val with
      | false => rfl
      | true => exact Bool.noConfusion ((neg i v).symm.trans h)
  · intro h
    refine ⟨fun i => h (.inl i),?_⟩
    intro i hi
    cases v : b.2.getLsbD i.val with
    | true => rfl
    | false => exact Bool.noConfusion (hi.symm.trans (h (.inr i) v))

def pool (w : Array Signature) : List (Column Row) :=
  (fun _ => false) :: (fun _ => true) :: w.toList.map view

theorem omit_dominated (w : Array Signature) (g : Nat) (n : Nat)
    (h : admissible w g = false)
    (tail : Separates label n (view (value w g) :: pool w)) : Separates label n (pool w) := by
  refine MonotoneTestPruning.discard ?_ tail
  have no : (dominates (0,0) (value w g) || w.any (fun a => dominates a (value w g))) = true := by
    cases e : (dominates (0,0) (value w g) || w.any (fun a => dominates a (value w g))) <;> simp_all [admissible]
  rcases Bool.or_eq_true_iff.mp no with zero|old
  · have eq : view (0,0) = (fun _ => false) := by funext r; cases r <;> simp [view]
    exact ⟨_,List.mem_cons_self,eq ▸ (dominance_exact _ _).mp zero⟩
  · have h' : w.toList.any (fun a => dominates a (value w g)) = true := by simpa only [Array.any_toList] using old
    obtain ⟨a,ha,good⟩ := List.any_eq_true.mp h'
    exact ⟨view a,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ha)),
      (dominance_exact _ _).mp good⟩

private theorem bits_input (r : Row) : rawColumns.toList.map (fun s => view s r) = input r := by
  apply List.ext_getElem
  · simp [input,raw_correct.1]
  · intro i hi hj
    have small : i < 26 := by simpa [raw_correct.1] using hi
    have ir : i < rawColumns.size := raw_correct.1.symm ▸ small
    have ok := List.all_eq_true.mp raw_correct.2 i (List.mem_range.mpr small)
    simp only [input,List.getElem_map,List.getElem_range,Array.getElem_toList]
    cases r with
    | inl j =>
      have jc : j.val < positive.size := row_counts.1.symm ▸ j.isLt
      have chk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).1 j.val (List.mem_range.mpr jc)
      simpa [view,mask,ir,jc] using beq_iff_eq.mp chk
    | inr j =>
      have jc : j.val < negative.size := row_counts.2.symm ▸ j.isLt
      have chk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 j.val (List.mem_range.mpr jc)
      simpa [view,mask,ir,jc] using beq_iff_eq.mp chk

theorem from_project (C : Circuit) (legal : Monotone2 C) (ok : ∀ r : Row, C.eval (input r) = label r) :
    Separates label C.size (pool rawColumns) := by
  apply of_project_circuit C legal (rawColumns.toList.map view)
  intro r
  simpa [List.map_map,Function.comp_def,← bits_input r] using ok r

abbrev BinGate := Bool × Nat × Nat
def realGate (g : BinGate) : Gate := ⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩
def execute (w : List Signature) (g : BinGate) : List Signature :=
  w ++ [binary g.1 (w.getD g.2.1 (0,0)) (w.getD g.2.2 (0,0))]

def circuit (gs : List BinGate) : Circuit := ⟨gs.map realGate,26+gs.length-1⟩
def output (gs : List BinGate) := (gs.foldl execute rawColumns.toList).getD (26+gs.length-1) (0,0)

theorem legal_control (gs : List BinGate) : Monotone2 (circuit gs) := by
  intro g hg
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
  cases op : a.1 <;> simp [realGate,op]

private theorem read_view (ws : List Signature) (i : Nat) (r : Row) :
    view (ws.getD i (0,0)) r = (ws.map (fun s => view s r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => cases r <;> simp [view]
  | some s => rfl

private theorem fold_view (gs : List BinGate) (ws : List Signature) (r : Row) :
    (gs.foldl execute ws).map (fun s => view s r) =
      (gs.map realGate).foldl
        (fun old g => old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)])
        (ws.map (fun s => view s r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons,ih,execute,List.map_append,List.map_nil,view_binary]
    simp only [combine,read_view]
    cases op : g.1 <;> simp [realGate,op,GateOp.eval]

theorem physical_eval (gs : List BinGate) (r : Row) :
    (circuit gs).eval (input r) = view (output gs) r := by
  rw [output,read_view,fold_view,bits_input]
  rfl

def full : List BinGate := [(false, 13, 17), (false, 26, 23), (false, 27, 25), (true, 0, 28), (false, 13, 14),
  (false, 30, 18), (false, 31, 24), (true, 1, 32), (false, 14, 15), (false, 34, 19),
  (false, 35, 25), (true, 2, 36), (false, 13, 15), (false, 38, 16), (false, 39, 20),
  (true, 3, 40), (false, 14, 16), (false, 42, 17), (false, 43, 21), (true, 4, 44),
  (false, 15, 17), (false, 46, 18), (false, 47, 22), (true, 5, 48), (false, 16, 18),
  (false, 50, 19), (false, 51, 23), (true, 6, 52), (false, 17, 19), (false, 54, 20),
  (false, 55, 24), (true, 7, 56), (false, 18, 20), (false, 58, 21), (false, 59, 25),
  (true, 8, 60), (false, 13, 19), (false, 62, 21), (false, 63, 22), (true, 9, 64),
  (false, 14, 20), (false, 66, 22), (false, 67, 23), (true, 10, 68), (false, 15, 21),
  (false, 70, 23), (false, 71, 24), (true, 11, 72), (false, 16, 22), (false, 74, 24),
  (false, 75, 25), (true, 12, 76), (false, 29, 33), (false, 78, 37), (false, 79, 41),
  (false, 80, 45), (false, 81, 49), (false, 82, 53), (false, 83, 57), (false, 84, 61),
  (false, 85, 65), (false, 86, 69), (false, 87, 73), (false, 88, 77)]

def near : List BinGate := [(false, 17, 23), (false, 26, 25), (true, 0, 27), (false, 13, 14), (false, 29, 18),
  (false, 30, 24), (true, 1, 31), (false, 14, 15), (false, 33, 19), (false, 34, 25),
  (true, 2, 35), (false, 13, 15), (false, 37, 16), (false, 38, 20), (true, 3, 39),
  (false, 14, 16), (false, 41, 17), (false, 42, 21), (true, 4, 43), (false, 15, 17),
  (false, 45, 18), (false, 46, 22), (true, 5, 47), (false, 16, 18), (false, 49, 19),
  (false, 50, 23), (true, 6, 51), (false, 17, 19), (false, 53, 20), (false, 54, 24),
  (true, 7, 55), (false, 18, 20), (false, 57, 21), (false, 58, 25), (true, 8, 59),
  (false, 13, 19), (false, 61, 21), (false, 62, 22), (true, 9, 63), (false, 14, 20),
  (false, 65, 22), (false, 66, 23), (true, 10, 67), (false, 15, 21), (false, 69, 23),
  (false, 70, 24), (true, 11, 71), (false, 16, 22), (false, 73, 24), (false, 74, 25),
  (true, 12, 75), (false, 28, 32), (false, 77, 36), (false, 78, 40), (false, 79, 44),
  (false, 80, 48), (false, 81, 52), (false, 82, 56), (false, 83, 60), (false, 84, 64),
  (false, 85, 68), (false, 86, 72), (false, 87, 76)]

set_option maxRecDepth 12000 in
theorem control_outputs :
    (circuit full).size = 64 ∧ output full = (BitVec.allOnes 52,0) ∧
    (circuit near).size = 63 ∧ output near = (~~~(1 : BitVec 52),0) ∧
    positive[0]! = 8193 := by decide +kernel

theorem full_correct (r : Row) : (circuit full).eval (input r) = label r := by
  rw [physical_eval,control_outputs.2.1]
  cases r with
  | inl i =>
    change (BitVec.allOnes 52).getLsbD i.val = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  | inr i => simp [view,label]

theorem near_negative (i : Fin 468) : (circuit near).eval (input (.inr i)) = false := by
  rw [physical_eval,control_outputs.2.2.2.1]
  simp [view]

theorem near_positive (i : Fin 52) :
    (circuit near).eval (input (.inl i)) = decide (i.val ≠ 0) := by
  rw [physical_eval,control_outputs.2.2.2.1]
  change (~~~(1 : BitVec 52)).getLsbD i.val = decide (i.val ≠ 0)
  have bits : ∀ j : Fin 52, (~~~(1 : BitVec 52)).getLsbD j.val = decide (j.val ≠ 0) := by
    decide +kernel
  exact bits i

end PEqualNP.Research.OrderThreePlaneControls
