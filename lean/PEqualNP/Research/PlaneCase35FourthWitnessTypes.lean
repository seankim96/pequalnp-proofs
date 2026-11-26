import Mathlib.Tactic.FinCases
import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35FourthWitnessTypes
open PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
private def pts : Array Nat := #[0,1,3,9,1,2,4,10,2,3,5,11,3,4,6,12,0,4,5,7,1,5,6,8,2,6,7,9,3,7,8,10,4,8,9,11,5,9,10,12,0,6,10,11,1,7,11,12,0,2,8,12]
private def point (p : Fin 52) := pts[p.val]!
private def anchor (line : Bool) (p : Fin 52) := if line then 13+p.val/4 else point p
private def posWord (i : Fin 52) := (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i.val)) &&& 0xfffffff
set_option maxRecDepth 16000 in
private theorem posMatch : ∀ i : Fin 52, posWord i = pos i.val := by decide +kernel
private theorem posBit (p : Fin 52) (j : Nat) : input j p.val = (posWord p).testBit j := by
  simp only [input,ite_eq_left p.isLt,posMatch]
private theorem valid : ∀ (m : Bool) (p : Fin 52), anchor m p < 28 ∧ input (anchor m p) p.val = true  := by
  simp only [posBit]
  decide +kernel
private def tag (k : Fin 28) := decide (13 ≤ k.val ∧ k.val < 26)
private theorem lineShape : ∀ (k : Fin 28) (p : Fin 52), tag k = true → input k.val p.val = true →
    k.val = 13+p.val/4 ∧ p.val/4 = k.val%13  := by
  simp only [posBit]
  intro k
  fin_cases k <;> as_aux_lemma => decide +kernel
private theorem pointShape : ∀ (k : Fin 28) (p : Fin 52), tag k = false → input k.val p.val = true →
    k.val = point p ∨ (k.val=26 ∧ (point p=0 ∨ point p=1)) ∨
    (k.val=27 ∧ (point p=3 ∨ point p=9))  := by
  simp only [posBit]
  intro k
  fin_cases k <;> as_aux_lemma => decide +kernel
private theorem wordOr (x : Nat) :
    (extend x).testBit 26 = (x.testBit 26 || (extend x).testBit 0 || (extend x).testBit 1) ∧
    (extend x).testBit 27 = (x.testBit 27 || (extend x).testBit 3 || (extend x).testBit 9) := by
  have hi (v : Nat) : (v%2).testBit 1 = false := by
    have cases : v%2=0 ∨ v%2=1 := by omega
    rcases cases with h|h <;> rw [h] <;> decide
  simp [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_assoc,hi]
private theorem negOr (n : Fin 468) : let r := 52+n.val
    input 26 r = (negative[n.val]!.testBit 26 || input 0 r || input 1 r) ∧
    input 27 r = (negative[n.val]!.testBit 27 || input 3 r || input 9 r) := by
  simpa [input,neg,show ¬52+n.val < 52 by omega] using wordOr negative[n.val]!

private def Pure (S : Fin 52 → Prop) (m : Bool) (w : Column) :=
  ∀ p : Fin 52, S p → w p.val = true → ∀ n : Fin 468, input (anchor m p) (52+n.val) = true → w (52+n.val) = true
private theorem rawPure (S : Fin 52 → Prop) (k : Fin 28) : Pure S (tag k) (input k.val) := by
  intro p _ on n hit
  cases e : tag k
  · simp only [anchor,e,Bool.false_eq_true,ite_false] at hit
    rcases pointShape k p e on with eq | ⟨eq,a|a⟩ | ⟨eq,a|a⟩
    · simpa [eq] using hit
    all_goals rw [a] at hit
    all_goals simp [eq,(negOr n).1,(negOr n).2,hit]
  · simpa [anchor,e,(lineShape k p e on).1] using hit
private theorem mixPure {S m x y} (op : Bool) (hx : Pure S m x) (hy : Pure S m y) : Pure S m (mix op x y) := by
  intro p hp on n hit
  cases op
  · change (x p.val || y p.val) = true at on
    rcases Bool.or_eq_true_iff.mp on with h | h
    · simp [mix,hx p hp h n hit]
    · simp [mix,hy p hp h n hit]
  · change (x p.val && y p.val) = true at on
    obtain ⟨u,v⟩ := Bool.and_eq_true_iff.mp on
    simp [mix,hx p hp u n hit,hy p hp v n hit]

private def allowed (line : Bool) (slot i j : Fin 4) (mode : Bool) :=
  line = mode ∨ line = true ∧ (slot=i ∨ slot=j)
private instance (t : Bool) (k i j : Fin 4) (m : Bool) : Decidable (allowed t k i j m) := inferInstanceAs (Decidable (_ ∨ _ ∧ (_ ∨ _)))
-- Only leaf types and references to gate three enter this selection.
set_option maxRecDepth 8192 in
private theorem plan : ∀ (x y z t da db : Bool), ∃ i j : Fin 4, ∃ m n : Bool,
    allowed x 0 i j m ∧ allowed y 1 i j m ∧
    (if da then m=n else allowed z 2 i j n) ∧
    (if db then m=n else allowed t 3 i j n) := by
  intro x y z t da db
  match x,y,z,t,da,db with
  | false,false,false,false,false,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,false,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,true,false,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,false,true,false,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,false,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,false,false,false => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,false,false,true => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,true,false,false => exact ⟨0,0,false,true,by decide⟩
  | false,false,true,true,false,true => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,true,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,true,false,false,false,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,false,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,true,false,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,false,true,false,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,true,true,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,false,true,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,false,false,false => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,false,false,true => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,false,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,true,false,false => exact ⟨0,1,false,true,by decide⟩
  | false,true,true,true,false,true => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,true,true,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,true,true,true,true => exact ⟨0,1,false,false,by decide⟩
  | true,false,false,false,false,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,false,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,true,false,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,false,true,false,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,false,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,false,false,false => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,false,false,true => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,true,false,false => exact ⟨0,0,false,true,by decide⟩
  | true,false,true,true,false,true => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,true,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,true,false,false,false,false => exact ⟨0,0,true,false,by decide⟩
  | true,true,false,false,false,true => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,false,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,false,true,false,false => exact ⟨0,3,true,false,by decide⟩
  | true,true,false,true,false,true => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,true,true,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,false,true,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,false,false,false => exact ⟨0,2,true,false,by decide⟩
  | true,true,true,false,false,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | true,true,true,false,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,false,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,false,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,true,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,true,true => exact ⟨0,0,true,true,by decide⟩
private def rawIndex (k : Fin 29) := Fin.ofNat 28 k.val
private def indices (l r : Fin 28) (a b : Fin 29) (k : Fin 4) : Fin 28 :=
  if k=0 then l else if k=1 then r else if k=2 then rawIndex a else rawIndex b
private theorem choose (i j : Fin 13) : ∃ A B : Fin 13, A≠B ∧ (i=A ∨ i=B) ∧ (j=A ∨ j=B) := by
  by_cases e : i=j
  · subst j
    by_cases z : i=0
    · exact ⟨i,1,by simp [z],Or.inl rfl,Or.inl rfl⟩
    · exact ⟨i,0,z,Or.inl rfl,Or.inl rfl⟩
  · exact ⟨i,j,e,Or.inl rfl,Or.inr rfl⟩
private theorem sourcePure {S n m c} (k : Fin 29) (hc : Pure S m c)
    (h : if k.val < 28 then Pure S n (input (rawIndex k).val) else m=n) : Pure S n (source c k) := by
  by_cases lt : k.val < 28
  · simp only [ite_eq_left lt] at h
    simpa [source,lt,rawIndex,Fin.ofNat,Nat.mod_eq_of_lt lt] using h
  · have eq : m=n := by simpa [lt] using h
    simpa [source,lt,eq] using hc

end PEqualNP.Research.PlaneCase35FourthWitnessTypes

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35FourthWitnessTypes in
theorem PEqualNP.Research.PlaneCase35FourthWitnessTypes : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    ∃ A B : Fin 13, A ≠ B ∧
      ∀ w ∈ [c,d], ∀ p : Fin 52, p.val/4 ≠ A.val → p.val/4 ≠ B.val → w p.val = true →
        ∃ v ∈ (List.ofFn (fun j : Fin 28 => input j.val)), v p.val = true ∧
          ∀ z : Fin 468, v (52+z.val) = true → w (52+z.val) = true := by
  intro op₃ op₄ l r a b c d
  let ks := indices l r a b
  obtain ⟨i,j,m,n,hx,hy,hz,ht⟩ := plan (tag l) (tag r) (tag (rawIndex a)) (tag (rawIndex b))
    (decide (¬a.val<28)) (decide (¬b.val<28))
  let label (k : Fin 4) := Fin.ofNat 13 (ks k).val
  obtain ⟨A,B,ne,hi,hj⟩ := choose (label i) (label j)
  let S := fun p : Fin 52 => p.val/4 ≠ A.val ∧ p.val/4 ≠ B.val
  have leaf (k : Fin 4) (mode : Bool) (h : allowed (tag (ks k)) k i j mode) :
      Pure S mode (input (ks k).val) := by
    rcases h with e | ⟨line,mem⟩
    · rw [←e]; exact rawPure S _
    · intro p off on
      have e : p.val/4 = (label k).val := (lineShape _ _ line on).2
      rcases mem with rfl | rfl
      · rcases hi with eq | eq <;> rw [eq] at e <;> exact False.elim (by rcases off with ⟨u,v⟩; contradiction)
      · rcases hj with eq | eq <;> rw [eq] at e <;> exact False.elim (by rcases off with ⟨u,v⟩; contradiction)
  have hc : Pure S m c := mixPure op₃ (leaf 0 m hx) (leaf 1 m hy)
  have left : Pure S n (source c a) := by
    apply sourcePure a hc
    by_cases h : a.val < 28
    · rw [ite_eq_left h]
      have leafOk : allowed (tag (rawIndex a)) 2 i j n := by simpa [h] using hz
      exact leaf 2 n leafOk
    · simpa [h] using hz
  have right : Pure S n (source c b) := by
    apply sourcePure b hc
    by_cases h : b.val < 28
    · rw [ite_eq_left h]
      have leafOk : allowed (tag (rawIndex b)) 3 i j n := by simpa [h] using ht
      exact leaf 3 n leafOk
    · simpa [h] using ht
  have hd : Pure S n d := mixPure op₄ left right
  have liftWire {mode w} (pure : Pure S mode w) (p : Fin 52) (ha : p.val/4 ≠ A.val) (hb : p.val/4 ≠ B.val)
      (on : w p.val = true) : ∃ v ∈ (List.ofFn (fun j : Fin 28 => input j.val)), v p.val = true ∧
      ∀ z : Fin 468, v (52+z.val) = true → w (52+z.val) = true := by
    let v : Fin 28 := ⟨_,(valid mode p).1⟩
    exact ⟨_,List.mem_ofFn.mpr ⟨v,rfl⟩,(valid mode p).2,pure p ⟨ha,hb⟩ on⟩
  refine ⟨A,B,ne,?_⟩
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact liftWire hc
  · exact liftWire hd
