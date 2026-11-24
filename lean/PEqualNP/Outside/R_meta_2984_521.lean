import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

-- Singleton point experiments identify one OR which separates two incident
-- points in opposite directions on each of at least 101 distinct lines.
theorem PEqualNP.Outside.R_meta_2984_521
    (locate : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ l, (S l).card = q+1) → IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ (l : Fin n) (X : Finset (Fin n)), X.card = 0 → C.eval (incidenceInput X {l}) = false) →
      100*C.size < n*q → (∃ (pre post : List Gate) (a b : ℕ) (L : Finset (Fin n)),
          C.gates = pre ++ ⟨.or,[a,b]⟩ :: post ∧ 100 < L.card ∧
          ∀ l ∈ L, ∀ w ∈ [(a,b),(b,a)], ∃ p ∈ S l,
            let z := (⟨pre,0⟩ : Circuit).wires (incidenceInput {p} {l})
            z.getD w.1 false = true ∧ z.getD w.2 false = false))
    (collision : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size → RightOnIncidentPairs S C →
      100*C.size < n*q → (∃ (pre post : List Gate) (a b : ℕ) (L : Finset (Fin n)),
          C.gates = pre ++ ⟨.or,[a,b]⟩ :: post ∧ 100 < L.card ∧
          ∀ l ∈ L, ∀ w ∈ [(a,b),(b,a)], ∃ p ∈ S l,
            let z := (⟨pre,0⟩ : Circuit).wires (incidenceInput {p} {l})
            z.getD w.1 false = true ∧ z.getD w.2 false = false) →
      ∃ X Y, Y.card ≤ q ∧ IsFalseInput S X Y ∧ C.eval (incidenceInput X Y) = true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn card plane ao output pairs sound
  by_contra! tooSmall
  have off (l : Fin n) (X : Finset (Fin n)) (empty : X.card = 0) : C.eval (incidenceInput X {l}) = false := by
    have eq := Finset.card_eq_zero.mp empty
    subst X
    exact sound _ _ (by simpa using (show 1 ≤ q by omega)) (by intro j hj; exact Finset.disjoint_empty_right _)
  obtain ⟨X,Y,hy,negative,on⟩ := collision q n S C hq hn card plane ao output pairs tooSmall
    (locate q n S C card ao pairs off tooSmall)
  exact Bool.noConfusion (on.symm.trans (sound X Y hy negative))
