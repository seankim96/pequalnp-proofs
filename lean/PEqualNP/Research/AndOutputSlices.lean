import PEqualNP.Outside.L_meta_2780

/-! An AND output deciding incidence on sparse line sets has an exact operand
on each such line set. The operand can depend on the lines, but it must work
for every point set simultaneously. No projective-plane axioms are needed. -/

namespace PEqualNP.Research.AndOutputSlices

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2780

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {C : Circuit}

def value (C : Circuit) (w : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) : Bool :=
  wireValue C (incidenceInput X Y) w

def ExactOn (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) (Y : Finset (Fin m)) : Prop :=
  ∀ X, value C w X Y = incidenceFun S X Y

private theorem wire_monotone (hao : IsAO2 (n+m) C) (w : ℕ)
    {X X' : Finset (Fin n)} {Y Y' : Finset (Fin m)} (hx : X ⊆ X') (hy : Y ⊆ Y') :
    value C w X Y = true → value C w X' Y' = true := by
  apply mono2 C.gates (fun g hg => ⟨hao.1 g hg, (hao.2.2 g hg).le⟩)
  · simp [incidenceInput]
  · apply app_mono _ _ _ _ (by simp)
    · exact ofFn_mono _ _ _ (fun p hp => by simpa using hx (by simpa using hp))
    · exact ofFn_mono _ _ _ (fun l hl => by simpa using hy (by simpa using hl))

private theorem output_and (hao : IsAO2 (n+m) C) {j a b : ℕ}
    (hout : C.output = n+m+j) (gate : C.gates[j]? = some ⟨.and,[a,b]⟩)
    (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    C.eval (incidenceInput X Y) = (value C a X Y && value C b X Y) := by
  let data := incidenceInput X Y
  have len : data.length = n+m := by simp [data, incidenceInput]
  have hj : j < C.gates.length := by
    by_contra h
    simp [h] at gate
  have hg : C.gates[j] = ⟨.and,[a,b]⟩ := by simpa [hj] using gate
  have backward (w : ℕ) (hw : w = a ∨ w = b) : w < data.length+j := by
    rw [len]
    apply hao.2.1 j hj
    simpa [MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, gate] using hw
  change (wf C.gates data).getD C.output false =
    ((wf C.gates data).getD a false && (wf C.gates data).getD b false)
  rw [hout, ← len, gate_val C.gates data j hj, hg]
  rw [wire_take C.gates data j a (backward a (Or.inl rfl)) hj.le,
      wire_take C.gates data j b (backward b (Or.inr rfl)) hj.le]
  simp [GateOp.eval]

private theorem false_iff_subset (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    IsFalseInput S X Y ↔ X ⊆ zeroSet S Y := by
  constructor
  · intro h p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl hpl =>
      Finset.disjoint_left.mp (h l hl) hpl hp⟩
  · intro h l hl
    exact Finset.disjoint_left.mpr fun p hpl hp =>
      (Finset.mem_filter.mp (h hp)).2 l hl hpl

/-- Falsity at the single maximal negative point set identifies exactly the
operands that compute the whole incidence slice. -/
theorem exactOn_iff_rejects_maximal (hao : IsAO2 (n+m) C) {w : ℕ}
    (pairs : ∀ l : Fin m, ∀ p ∈ S l, value C w {p} {l} = true)
    (Y : Finset (Fin m)) :
    ExactOn S C w Y ↔ value C w (zeroSet S Y) Y = false := by
  have nohit (X : Finset (Fin n)) :
      incidenceFun S X Y = false ↔ IsFalseInput S X Y := by
    simp only [incidenceFun, decide_eq_false_iff_not, IsFalseInput, Finset.disjoint_left]
    grind
  constructor
  · intro h
    exact (h _).trans ((nohit _).mpr ((false_iff_subset _ _).mpr (fun _ hz => hz)))
  · intro rejects X
    cases h : incidenceFun S X Y with
    | false =>
      have sub := (false_iff_subset X Y).mp ((nohit X).mp h)
      cases hv : value C w X Y with
      | false => rfl
      | true => exact (wire_monotone hao w sub (fun _ hz => hz) hv).symm.trans rejects
    | true =>
      obtain ⟨p,hp,l,hl,hpl⟩ := of_decide_eq_true h
      exact wire_monotone hao w (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_subset_iff.mpr hl) (pairs l p hpl)

/-- For each promised line set, one fixed operand is correct on all point sets. -/
theorem exact_operand (hao : IsAO2 (n+m) C) {j a b q : ℕ}
    (hout : C.output = n+m+j) (gate : C.gates[j]? = some ⟨.and,[a,b]⟩)
    (pairs : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (Y : Finset (Fin m)) (small : Y.card ≤ q) :
    ExactOn S C a Y ∨ ExactOn S C b Y := by
  have both (l : Fin m) (p : Fin n) (onLine : p ∈ S l) :
      value C a {p} {l} = true ∧ value C b {p} {l} = true := by
    apply Bool.and_eq_true_iff.mp
    rw [← output_and hao hout gate]
    exact pairs l p onLine
  rw [exactOn_iff_rejects_maximal hao (fun l p h => (both l p h).1),
      exactOn_iff_rejects_maximal hao (fun l p h => (both l p h).2)]
  have h := sound (zeroSet S Y) Y small ((false_iff_subset _ _).mpr (fun _ hz => hz))
  rw [output_and hao hout gate] at h
  exact Bool.and_eq_false_iff.mp h

/-- One common operand handles at least half of any chosen family of sparse slices. -/
theorem half_family {a b : ℕ} (family : Finset (Finset (Fin m)))
    (cover : ∀ Y ∈ family, ExactOn S C a Y ∨ ExactOn S C b Y) :
    ∃ w ∈ [a,b], ∃ T ⊆ family, family.card ≤ 2*T.card ∧ ∀ Y ∈ T, ExactOn S C w Y := by
  classical
  let A := family.filter (ExactOn S C a)
  let B := family.filter (ExactOn S C b)
  have sub : family ⊆ A ∪ B := by
    intro Y hY
    rcases cover Y hY with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hY,ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hY,hb⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le A B)
  by_cases le : A.card ≤ B.card
  · exact ⟨b, by simp, B, Finset.filter_subset _ _, by omega,
      fun _ h => (Finset.mem_filter.mp h).2⟩
  · exact ⟨a, by simp, A, Finset.filter_subset _ _, by omega,
      fun _ h => (Finset.mem_filter.mp h).2⟩

/-- A complete proof of the normalization premise of the reduction for L-meta-3469.
Take the strict prefix before the output gate, retaining both operands on their
original wire numbers. Any gates following the output disappear as well. -/
theorem normalize : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (j a b : ℕ),
      IsAO2 (n+n) C → C.output = n+n+j → C.gates[j]? = some ⟨.and,[a,b]⟩ →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      ∃ D : Circuit, IsAO2 (n+n) D ∧ D.size+1 ≤ C.size ∧
        RightOnIncidentPairs S ⟨D.gates,a⟩ ∧ RightOnIncidentPairs S ⟨D.gates,b⟩ ∧
        ∀ Y : Finset (Fin n), Y.card ≤ q → ∃ w ∈ [a,b], ∀ X : Finset (Fin n),
          wireValue D (incidenceInput X Y) w = incidenceFun S X Y := by
  intro q n S C j a b hao hout gate pairs sound
  have hj : j < C.gates.length := by
    by_contra h
    simp [h] at gate
  let D : Circuit := ⟨C.gates.take j,0⟩
  have hlen : D.gates.length = j := by simp [D, List.length_take, Nat.min_eq_left hj.le]
  have valid : IsAO2 (n+n) D := by
    refine ⟨fun g hg => hao.1 g (List.mem_of_mem_take hg), ?_,
      fun g hg => hao.2.2 g (List.mem_of_mem_take hg)⟩
    intro k hk w hw
    have lt : k < j := hlen ▸ hk
    apply hao.2.1 k (by omega) w
    simpa only [MetaComplexity.NestedCover.gateAt, D, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt lt] using hw
  have available (w : ℕ) (hw : w = a ∨ w = b) : w < n+n+j := by
    apply hao.2.1 j hj
    simpa [MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, gate] using hw
  have same (w : ℕ) (hw : w=a ∨ w=b) (X Y : Finset (Fin n)) :
      value C w X Y = value D w X Y := by
    apply wire_take C.gates (incidenceInput X Y) j w _ hj.le
    simpa [incidenceInput] using available w hw
  have positive (l p : Fin n) (hp : p ∈ S l) :
      value D a {p} {l} = true ∧ value D b {p} {l} = true := by
    rw [← same a (Or.inl rfl), ← same b (Or.inr rfl), ← Bool.and_eq_true_iff,
        ← output_and hao hout gate]
    exact pairs l p hp
  have saved : D.size+1 ≤ C.size := by
    change D.gates.length+1 ≤ C.gates.length
    omega
  refine ⟨D,valid,saved, fun l p hp => (positive l p hp).1,
    fun l p hp => (positive l p hp).2, ?_⟩
  intro Y hy
  rcases exact_operand hao hout gate pairs sound Y hy with ha|hb
  · exact ⟨a, by simp, fun X => (same a (Or.inl rfl) X Y).symm.trans (ha X)⟩
  · exact ⟨b, by simp, fun X => (same b (Or.inr rfl) X Y).symm.trans (hb X)⟩

end PEqualNP.Research.AndOutputSlices
