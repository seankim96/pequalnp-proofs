import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndSeparation

abbrev Column := Nat → Bool
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def good (p a b : Nat) (w : Column) := w p = true → w a = true ∨ w b = true

end PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndSeparation


namespace PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndBudget
open PlaneFirstAndSeparation
abbrev Gate := Bool × Bool × Nat × Nat × Option Nat
variable (guards : Nat → Column)
def step (s : List Column) (g : Gate) : List Column :=
  let x := wire s g.2.2.1
  let y := wire s g.2.2.2.1
  s ++ [fun v => (if g.1 then x v && y v else x v || y v) &&
    (g.2.2.2.2.elim true (fun k => guards k v))]

def charged (g : Gate) := g.1 && g.2.1
-- Values of the unrecorded left operands must agree within each color class.
def synced (s : List Column) (a b : Nat) (gs : List Gate) : Prop :=
  gs.foldr (fun g next state =>
    (g.1 = true → g.2.1 = false → wire state g.2.2.1 a = wire state g.2.2.1 b) ∧
      next (step guards state g)) (fun _ => True) s

private def trace (s : List Column) (r : Nat) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let tail := trace (step guards s g) r gs
    if charged g then 2 * tail + (wire s g.2.2.1 r).toNat else tail

private theorem trace_lt (s : List Column) (r : Nat) (gs : List Gate) :
    trace guards s r gs < 2 ^ (gs.countP charged) := by
  induction gs generalizing s with
  | nil => simp [trace]
  | cons g gs ih =>
    have h := ih (step guards s g)
    cases op : charged g
    · simpa [trace,List.countP_cons,op] using h
    · have count : (g :: gs).countP charged = gs.countP charged + 1 := by simp [op]
      simp only [trace,op,ite_true,count,Nat.pow_succ]
      cases hx : wire s g.2.2.1 r <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

private theorem readGood {s : List Column} {p a b : Nat} (all : ∀ w ∈ s, good p a b w) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases h : s[j]? with
  | none => simp [good]
  | some w => exact all w (List.mem_of_getElem? h)

private theorem preserve (gs : List Gate) (s : List Column) (p a b : Nat)
    (strong : ∀ k, guards k p = true → guards k a = true ∧ guards k b = true)
    (h : ∀ w ∈ s, good p a b w) (sync : synced guards s a b gs) (eq : trace guards s a gs = trace guards s b gs) :
    ∀ w ∈ gs.foldl (step guards) s, good p a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace guards (step guards s g) a gs = trace guards (step guards s g) b gs := by
      cases op : charged g <;> simp [trace,op] at eq <;>
        cases x : wire s g.2.2.1 a <;> cases y : wire s g.2.2.1 b <;> simp_all <;> omega
    apply ih _ _ sync.2 tail
    intro w hw
    have l := readGood h g.2.2.1
    have r := readGood h g.2.2.2.1
    rcases List.mem_append.mp hw with old | last
    · exact h _ old
    obtain rfl := List.mem_singleton.mp last
    intro hit
    obtain ⟨lit,mask⟩ := Bool.and_eq_true_iff.mp hit
    have safe : (g.2.2.2.2.elim true (fun k => guards k a)) = true ∧
                (g.2.2.2.2.elim true (fun k => guards k b)) = true := by
      cases mode : g.2.2.2.2 with
      | none => simp
      | some k => exact strong k (by simpa [mode] using mask)
    simp only [safe.1,safe.2,Bool.and_true]
    cases op : g.1
    · simp [op] at lit ⊢
      rcases lit with left | right
      · rcases l left with v | v <;> tauto
      · rcases r right with v | v <;> tauto
    · have same : wire s g.2.2.1 a = wire s g.2.2.1 b := by
        cases mark : g.2.1
        · exact sync.1 op mark
        · have h : charged g = true := by simp [charged,op,mark]
          simp [trace,h,tail] at eq
          cases x : wire s g.2.2.1 a <;> cases y : wire s g.2.2.1 b <;> simp_all
      simp [op] at lit ⊢
      obtain ⟨lp,rp⟩ := lit
      have la := l lp
      have ra := r rp
      rw [same] at la ⊢
      tauto

end PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndBudget
open PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndBudget PEqualNP.Research.PlaneColoredTraceBudget.PlaneFirstAndSeparation in
theorem PEqualNP.Research.PlaneColoredTraceBudget : ∀ (guards : Nat → Column) (s : List Column) (gs : List Gate) (o q : Nat)
    (K : Finset (Fin 468)) (color : K → Fin q),
    (∀ i j : K, i.val < j.val → ∃ p : Fin 52,
      (∀ k, guards k p.val = true → guards k (52+i.val.val) = true ∧ guards k (52+j.val.val) = true) ∧
      ∀ w ∈ s, good p.val (52+i.val.val) (52+j.val.val) w) →
    (∀ i j : K, color i = color j → synced guards s (52+i.val.val) (52+j.val.val) gs) →
    (∀ p : Fin 52, wire (gs.foldl (step guards) s) o p.val = true) →
    (∀ i : Fin 468, wire (gs.foldl (step guards) s) o (52+i.val) = false) →
    K.card ≤ q * 2 ^ gs.countP charged := by
  intro guards s gs o q K color sep sync hp hn
  let f (i : K) : Fin q × Fin (2 ^ gs.countP charged) :=
    (color i,⟨trace guards s (52+i.val.val) gs,trace_lt guards _ _ _⟩)
  have distinct (i j : K) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,strong,hp0⟩ := sep i j lt
    have c : color i = color j := congrArg Prod.fst eq
    have bits := congrArg (fun z : Fin q × Fin (2 ^ gs.countP charged) => z.2.val) eq
    have remain := preserve guards gs s _ _ _ strong hp0 (sync i j c) bits
    have bad := (readGood remain o) (hp p)
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f inj
