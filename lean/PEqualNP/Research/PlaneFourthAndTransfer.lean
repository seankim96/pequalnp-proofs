import PEqualNP.Research.PlaneCode84AndCount

namespace PEqualNP.Research.PlaneFourthAndTransfer
open PlanePairAndCount PlaneFlagFourth

def remap (i : Nat) := if i < 29 then i else if i = 29 then 32 else if i < 32 then i else i+1
def liftGate (g : Gate) : Gate := (g.1,remap g.2.1,remap g.2.2)

private theorem read_eq (pre tail : Row) (a b : Bool) (hlen : pre.length = 29) (i : Nat) :
    readWire (pre ++ a::false::true::tail) i =
    readWire (pre ++ b::false::true::a::tail) (remap i) := by
  by_cases h : i < 29
  · simp only [remap,h,ite_true,readWire,List.getD_eq_getElem?_getD,List.getElem?_append_left (show i < pre.length by omega)]
  · have hi : pre.length ≤ i := by omega
    have hj : pre.length ≤ remap i := by unfold remap; split_ifs <;> omega
    simp only [readWire,List.getD_eq_getElem?_getD,List.getElem?_append_right hi,List.getElem?_append_right hj,hlen]
    obtain ⟨r,rfl⟩ : ∃ r, i = 29+r := ⟨i-29,by omega⟩
    rcases r with _ | _ | _ | r
    · rfl
    · rfl
    · rfl
    · have eq : remap (29+(r+1+1+1)) = 29+(r+1+1+1)+1 := by unfold remap; split_ifs <;> omega
      rw [eq,show 29+(r+1+1+1)-29 = r+3 by omega,show 29+(r+1+1+1)+1-29 = r+4 by omega]
      rfl

private theorem replay (gs : List Gate) (pre tail : Row) (a b : Bool) (len : pre.length = 29) (o : Nat) :
    readWire (gs.foldl step (pre ++ a::false::true::tail)) o =
    readWire ((gs.map liftGate).foldl step (pre ++ b::false::true::a::tail)) (remap o) := by
  induction gs generalizing tail with
  | nil => exact read_eq pre tail a b len o
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons,step,liftGate]
    rw [← read_eq pre tail a b len g.2.1, ← read_eq pre tail a b len g.2.2]
    simpa only [List.append_assoc,List.cons_append] using ih (tail ++ [_])

def testRow (k : Nat) (pos : Bool) (i : Nat) : Row :=
  (PlaneFlagOrTail.start k).map fun x => if pos then x.1.getLsbD i else x.2.getLsbD i
private def bit (pos : Bool) (i : Nat) (x : OrderThreePlanePrefixData.Signature) :=
  if pos then x.1.getLsbD i else x.2.getLsbD i
private def pre (pos : Bool) (i : Nat) : Row := List.ofFn (fun j : Fin 29 => bit pos i (col j.val))
set_option exponentiation.threshold 512 in
private theorem shape (k : Nat) (pos : Bool) (i : Nat) (hi : i < (if pos then 52 else 468)) :
    testRow k pos i = pre pos i ++ [bit pos i (gate k []),false,true] := by
  cases pos <;> simp [testRow,PlaneFlagOrTail.start,pre,bit] at *
  · exact (BitVec.getLsbD_allOnes (v := 468) (i := i)).trans (decide_eq_true hi)
  · exact (BitVec.getLsbD_allOnes (v := 52) (i := i)).trans (decide_eq_true hi)

private def fourth (k : Nat) : Gate := (decide (841 ≤ k), k/29%29, k%29)
private theorem initialStep (k : Nat) (pos : Bool) (i : Nat) (hi : i < (if pos then 52 else 468)) :
    step (testRow 84 pos i) (fourth k) =
    pre pos i ++ [bit pos i (gate 84 []),false,true,bit pos i (gate k [])] := by
  rw [shape _ _ _ hi]
  have get (j : Nat) (hj : j < 29) :
      readWire (pre pos i ++ [bit pos i (gate 84 []),false,true]) j = bit pos i (col j) := by
    have lt : j < (pre pos i).length := by simpa [pre] using hj
    unfold readWire
    rw [List.getD_append _ _ _ _ lt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt]
    simp only [Option.getD_some,pre,List.getElem_ofFn]
  simp only [step,fourth,get _ (Nat.mod_lt _ (by decide : 0 < 29)),List.append_assoc]
  cases pos <;> by_cases op : 841 ≤ k <;> simp [gate,ren,bit,op]

private theorem simOutput (k : Nat) (gs : List Gate) (o : Nat) (pos : Bool) (i : Nat) (hi : i < (if pos then 52 else 468)) :
    readWire (gs.foldl step (testRow k pos i)) o =
    readWire (((fourth k)::gs.map liftGate).foldl step (PlaneCode84AndCount.testRow pos i)) (remap o) := by
  change _ = readWire ((gs.map liftGate).foldl step (step (testRow 84 pos i) (fourth k))) _
  rw [initialStep k pos i hi,shape k pos i hi]
  exact replay gs _ [] _ _ (by simp [pre]) o
end PEqualNP.Research.PlaneFourthAndTransfer

open PEqualNP.Research.PlaneFourthAndTransfer PEqualNP.Research.PlanePairAndCount in
theorem PEqualNP.Research.PlaneFourthAndTransfer : ∀ (k : Nat) (gs : List Gate) (o : Nat),
    (∀ i : Fin 52, readWire (gs.foldl step (testRow k true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (testRow k false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst + (if 841 ≤ k then 1 else 0) := by
  intro k gs o hp hn
  have h := PEqualNP.Research.PlaneCode84AndCount ((fourth k)::gs.map liftGate) (remap o)
    (fun i => (simOutput k gs o true i.val i.isLt).symm.trans (hp i))
    (fun i => (simOutput k gs o false i.val i.isLt).symm.trans (hn i))
  simpa [List.countP_cons,List.countP_map,Function.comp_def,liftGate,fourth] using h
