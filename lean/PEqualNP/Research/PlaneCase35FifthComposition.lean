import PEqualNP.Research.PlaneCase35FifthAndShape
import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35FifthComposition
open PlaneFirstAndSeparation PlaneFirstAndBudget PlaneCase35FourthOrBudget
def initial : List Column := List.ofFn (fun k : Fin 28 => input k.val)

theorem initial_good (p : Fin 52) (a b : Fin 468)
    (h : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ initial, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hw
  have e := congrArg (fun x : Nat => x.testBit k.val) h
  simp only [Nat.testBit_and,Nat.testBit_or] at e
  intro hp
  have yes : (pos p.val).testBit k.val = true := by simpa [input,p.isLt] using hp
  rw [yes,Bool.true_and,Bool.or_eq_true] at e
  simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using e
def c := mix true (input 15) (input 27)
def d := mix true (input 17) (input 26)
def base (i : Fin 30) : Column :=
  if i.val < 28 then input i.val else if i.val = 28 then c else d
private def Cov (p : Fin 52) (a b : Fin 468) :=
  pos p.val &&& (neg a.val ||| neg b.val) = pos p.val
private def Pair (p : Fin 52) (a b : Fin 468) :=
  p.val ≠ 9 ∧ p.val ≠ 16 ∧ Cov p a b
private def G (w : Column) (p : Fin 52) (a b : Fin 468) :=
  good p.val (52+a.val) (52+b.val) w
private def Cert (e : Column) :=
  ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, Pair p (f i) (f j) ∧ G e p (f i) (f j)
def Single := ∀ u : Fin 52, ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j → ∃ p : Fin 52, Pair p (f i) (f j) ∧ p ≠ u
def Four := ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j → ∃ p : Fin 52, Pair p (f i) (f j) ∧ 4 ≤ p.val
private theorem cdOff : ∀ p : Fin 52, p.val ≠ 9 → p.val ≠ 16 →
    c p.val = false ∧ d p.val = false := by decide +kernel
private theorem raw (k : Fin 30) {p a b} (h : Pair p a b) : G (base k) p a b := by
  obtain ⟨h1,h2,h3⟩ := h
  by_cases lt : k.val < 28
  · have mem : input k.val ∈ initial := List.mem_ofFn.mpr ⟨(⟨k.val,lt⟩ : Fin 28),rfl⟩
    simpa [base,lt,G] using initial_good p a b h3 (input k.val) mem
  · obtain ⟨hc,hd⟩ := cdOff p h1 h2
    by_cases eq : k.val = 28 <;> simp [base,lt,eq,G,good,hc,hd]
private theorem inherit (single : Single) (e : Column) (h : ∀ p a b, Pair p a b → G e p a b) : Cert e := by
  obtain ⟨f,hf⟩ := single 0
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,hp,_⟩ := hf i j lt
  exact ⟨p,hp,h _ _ _ hp⟩
private theorem sparse (four : Four) (e : Column)
    (support : ∀ p : Fin 52, e p.val = true → p.val < 4) : Cert e := by
  obtain ⟨f,hf⟩ := four
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,cov,low⟩ := hf i j lt
  refine ⟨p,cov,?_⟩
  intro on
  have := support p on
  omega
private theorem verified (single : Single) (four : Four) (op : Bool) (a b : Fin 30) : Cert (mix op (base a) (base b)) := by
  cases op
  · apply inherit single
    intro p x y hp on
    rcases Bool.or_eq_true_iff.mp on with h | h
    · rcases raw a hp h with h | h <;> simp [mix,h]
    · rcases raw b hp h with h | h <;> simp [mix,h]
  · rcases PEqualNP.Research.PlaneCase35FifthAndShape a b with ha | hb | ⟨u,hu⟩ | h | h
    · apply inherit single; intro p x y h
      have eq : mix true (base a) (base b) = base a := funext ha
      rw [eq]; exact raw a h
    · apply inherit single; intro p x y h
      have eq : mix true (base a) (base b) = base b := funext hb
      rw [eq]; exact raw b h
    · obtain ⟨f,hf⟩ := single u
      refine ⟨f,?_⟩
      intro i j lt
      obtain ⟨p,hp,ne⟩ := hf i j lt
      exact ⟨p,hp,fun on => False.elim (ne (hu p on))⟩
    · apply sparse four; intro p hp; rcases h p hp with h | h <;> omega
    · apply sparse four; intro p hp; rcases h p hp with h | h <;> omega
end PEqualNP.Research.PlaneCase35FifthComposition
open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget
  PEqualNP.Research.PlaneCase35FifthComposition in
theorem PEqualNP.Research.PlaneCase35FifthComposition : Single → Four → ∀ (op : Bool) (a b : Fin 30) (gs : List Gate) (o : Nat),
    let e := mix op (base a) (base b)
    let pool := (initial ++ [c,d,e]) ++ [fun _ => false, fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro single four op a b gs o e pool hp hn
  apply separated_bound _ gs o _ hp hn
  obtain ⟨f,hf⟩ := verified single four op a b
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,hp,he⟩ := hf i j lt
  obtain ⟨h9,h16,cov⟩ := hp
  obtain ⟨hc,hd⟩ := cdOff p h9 h16
  refine ⟨p,?_⟩
  intro v hv
  rcases List.mem_append.mp hv with prev | con
  · rcases List.mem_append.mp prev with raw | ext
    · exact initial_good p _ _ cov v raw
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ext
      rcases ext with rfl | rfl | rfl
      · simp [good,hc]
      · simp [good,hd]
      · exact he
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at con
    rcases con with rfl | rfl <;> simp [good]
