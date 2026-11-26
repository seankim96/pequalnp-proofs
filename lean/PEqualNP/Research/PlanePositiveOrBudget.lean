import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.PlanePositiveOrBudget
open PlaneFirstAndSeparation PlaneFirstAndBudget
private def covered (n a b : Nat) (w : Column) := w a = true → w b = true → w n = true
private def trace (s : List Column) (r : Nat) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let tail := trace (step s g) r gs
    if g.1 then tail else 2 * tail + (wire s g.2.1 r).toNat

private theorem trace_lt (s : List Column) (r : Nat) (gs : List Gate) :
    trace s r gs < 2 ^ (gs.countP (fun g => !g.1)) := by
  induction gs generalizing s with
  | nil => simp [trace]
  | cons g gs ih =>
    have h := ih (step s g)
    cases op : g.1
    · have count : (g :: gs).countP (fun g => !g.1) = gs.countP (fun g => !g.1) + 1 := by simp [op]
      simp only [trace,op,Bool.false_eq_true,ite_false,count,Nat.pow_succ]
      cases hx : wire s g.2.1 r <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    · simpa [trace,List.countP_cons,op] using h

private theorem readGood {s : List Column} {p a b : Nat} (all : ∀ w ∈ s, covered p a b w) (j : Nat) :
    covered p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases h : s[j]? with
  | none => simp [covered]
  | some w => exact all w (List.mem_of_getElem? h)

private theorem preserve (gs : List Gate) (s : List Column) (p a b : Nat)
    (h : ∀ w ∈ s, covered p a b w) (eq : trace s a gs = trace s b gs) :
    ∀ w ∈ gs.foldl step s, covered p a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace (step s g) a gs = trace (step s g) b gs := by
      cases op : g.1 <;> simp [trace,op] at eq <;>
        cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all <;> omega
    apply ih _ _ tail
    intro w hw
    have l := readGood h g.2.1
    have r := readGood h g.2.2
    cases op : g.1
    · simp only [step,op,Bool.false_eq_true,ite_false,addOr,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · have same : wire s g.2.1 a = wire s g.2.1 b := by
          simp [trace,op,tail] at eq
          cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all
        unfold covered at *
        simp only [Bool.or_eq_true] at *
        rw [same] at l ⊢
        tauto
    · simp only [step,op,ite_true,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · unfold covered both at *
        simp only [Bool.and_eq_true] at *
        tauto
end PEqualNP.Research.PlanePositiveOrBudget

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlanePositiveOrBudget in
theorem PEqualNP.Research.PlanePositiveOrBudget : ∀ (s : List Column) (gs : List Gate) (o : Nat) (row : Fin 33 → Fin 52),
    (∀ i j : Fin 33, i.val < j.val → ∃ n : Fin 468, ∀ w ∈ s,
      w (row i).val = true → w (row j).val = true → w (52+n.val) = true) →
    (∀ p : Fin 52, wire (gs.foldl step s) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step s) o (52+n.val) = false) →
    6 ≤ gs.countP (fun g => !g.1) := by
  intro s gs o row h hp hn
  let f (i : Fin 33) : Fin (2 ^ (gs.countP (fun g => !g.1))) :=
    ⟨trace s (row i).val gs,trace_lt _ _ _⟩
  have distinct (i j : Fin 33) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨n,hp0⟩ := h i j lt
    have remain := preserve gs s _ _ _ hp0 (congrArg Fin.val eq)
    have bad := (readGood remain o) (hp (row i)) (hp (row j))
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Fin.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at card
  by_contra h
  have le : gs.countP (fun g => !g.1) ≤ 5 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP (fun g => !g.1) ≤ 32 at bound
  omega
