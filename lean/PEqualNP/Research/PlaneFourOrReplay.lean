import PEqualNP.Research.PlaneFourFirstJoin
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Tactic.SplitIfs

-- The circuit-to-union simulation below is from upstream L_meta_8265 at b9979b68.
-- Its proof is included with smaller imports for local replay of the combined theorem.

namespace PEqualNP.Research.PlaneFourOrReplay.simulation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)






end PEqualNP.Research.PlaneFourOrReplay.simulation

theorem PEqualNP.Research.PlaneFourOrReplay.simulation : ∀ (x1 : ℕ),   let x2 : Type := Fin x1;   let x3 : Type := x2 × x2;   have x4 : Set (Set x3) → Set x3 × Set x3 → Set (Set x3) := fun (x4 : Set (Set x3)) (x5 : Set x3 × Set x3) => {x6 : Set x3 | x6 ∈ x4 ∨ x5.1 ∈ x4 ∧ x5.2 ∈ x4 ∧ x6 ⊆ x5.1 ∪ x5.2};   have x5 : Set x2 → Set (Set x3) := fun (x5 : Set x2) => {x6 : Set x3 | x6 = ∅ ∨ ∃ x7 ∈ x5, ∀ x8 ∈ x6, x8.1 = x7 ∨ x8.2 = x7};   ∀ (x6 : Set x3) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : x2 → Bool), x7.eval (List.ofFn x9) = Bool.true ↔ ∃ x10 ∈ x6, x9 x10.1 = Bool.true ∧ x9 x10.2 = Bool.true) → ∃ (x10 : List (Set x3 × Set x3)), x10.length ≤ {x11 : Fin x7.gates.length | (x7.gates.get x11).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x11 : Set x2), (∀ x12 ∈ x6, x12.1 ∈ x11 ∨ x12.2 ∈ x11) → x6 ∈ List.foldl x4 (x5 x11) x10 := by
  intro n X Y step base E C hC hf
  classical
  let pt : Y → Fin n → Bool := fun e i => decide (i = e.1 ∨ i = e.2)
  let W : (Fin n → Bool) → ℕ → Bool := fun x w => (PEqualNP.Research.PlaneFourOrReplay.simulation.run C.gates (List.ofFn x)).getD w false
  let A : ℕ → Set Y := fun w => {e | e ∈ E ∧ W (pt e) w = true}
  have Wg : ∀ x j (hj : j < C.gates.length), W x (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + j then W x i else false) := by
    intro x j hj
    have := PEqualNP.Research.PlaneFourOrReplay.simulation.run_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at this
    exact this
  have Wi : ∀ x (i : Fin n), W x i = x i := by
    intro x i
    simp only [W]
    rw [PEqualNP.Research.PlaneFourOrReplay.simulation.run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  let pr : PEqualNP.CircuitLowerBounds.Gate → ℕ → Set Y × Set Y := fun g j =>
    ((if g.inputs.getD 0 (n + j) < n + j then A (g.inputs.getD 0 (n + j)) else ∅), (if g.inputs.getD 1 (n + j) < n + j then A (g.inputs.getD 1 (n + j)) else ∅))
  let L : ℕ → List (Set Y × Set Y) := fun k => (List.range k).filterMap fun j => if (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or then some (pr (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩) j) else none
  have sub : ∀ (T : Set X) (l : List (Set Y × Set Y)) (S S' : Set Y), S ∈ List.foldl step (base T) l → S' ⊆ S → S' ∈ List.foldl step (base T) l := by
    intro T l
    induction l using List.reverseRecOn with
    | nil =>
      intro S S' hS hS'
      rcases hS with rfl | ⟨t, ht, h⟩
      · exact Or.inl (Set.subset_empty_iff.1 hS')
      · exact Or.inr ⟨t, ht, fun e he => h e (hS' he)⟩
    | append_singleton l p ih =>
      intro S S' hS hS'
      rw [List.foldl_append] at hS ⊢
      rcases hS with h | ⟨h1, h2, h3⟩
      · exact Or.inl (ih S S' h hS')
      · exact Or.inr ⟨h1, h2, hS'.trans h3⟩
  have emp : ∀ (T : Set X) (l : List (Set Y × Set Y)), (∅ : Set Y) ∈ List.foldl step (base T) l := by
    intro T l
    induction l using List.reverseRecOn with
    | nil => exact Or.inl rfl
    | append_singleton l p ih => rw [List.foldl_append]; exact Or.inl ih
  have mon : ∀ (T : Set X) (l l' : List (Set Y × Set Y)) (S : Set Y), S ∈ List.foldl step (base T) l → S ∈ List.foldl step (base T) (l ++ l') := by
    intro T l l'
    induction l' using List.reverseRecOn with
    | nil => intro S h; simpa using h
    | append_singleton l' p ih =>
      intro S h
      rw [← List.append_assoc, List.foldl_append]
      exact Or.inl (ih S h)
  have Ls : ∀ k (hk : k < C.gates.length), L (k + 1) = L k ++ (if C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or then [pr C.gates[k] k] else []) := by
    intro k hk
    have e : C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
    simp only [L]
    rw [List.range_succ, List.filterMap_append]
    congr 1
    simp only [List.filterMap_cons, List.filterMap_nil, e]
    split_ifs with h <;> simp
  have main : ∀ (T : Set X), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) → ∀ k ≤ C.gates.length, ∀ w < n + k, W (fun i => decide (i ∉ T)) w = false → A w ∈ List.foldl step (base T) (L k) := by
    intro T hT k
    induction k with
    | zero =>
      intro _ w hw h
      have hw' : w < n := by omega
      have e := Wi (fun i => decide (i ∉ T)) ⟨w, hw'⟩
      simp only at e
      rw [e] at h
      have hwT : (⟨w, hw'⟩ : Fin n) ∈ T := by simpa using h
      refine Or.inr ⟨⟨w, hw'⟩, hwT, ?_⟩
      rintro a ⟨_, ha⟩
      have e2 := Wi (pt a) ⟨w, hw'⟩
      simp only at e2
      rw [e2] at ha
      simp only [pt, decide_eq_true_eq] at ha
      exact ha.imp Eq.symm Eq.symm
    | succ k ih =>
      intro hk w hw h
      have hk' : k < C.gates.length := by omega
      have ih' := ih (by omega)
      rw [Ls k hk']
      rcases Nat.lt_or_ge w (n + k) with hlt | hge
      · exact mon _ _ _ _ (ih' w hlt h)
      · have : w = n + k := by omega
        subst this
        obtain ⟨ho, hl⟩ := hC _ (List.getElem_mem hk')
        have ho' : C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using ho
        rcases ho' with ho | ho
        · refine mon _ _ _ _ ?_
          rw [Wg _ k hk', ho] at h
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_false, Function.comp, id] at h
          obtain ⟨u, hu, huf⟩ := h
          by_cases hul : u < n + k
          · rw [if_pos hul] at huf
            refine sub _ _ _ _ (ih' u hul (by simpa using huf)) ?_
            rintro e ⟨heE, he⟩
            refine ⟨heE, ?_⟩
            rw [Wg _ k hk', ho] at he
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at he
            have := he u hu
            rwa [if_pos hul] at this
          · have : A (n + k) = ∅ := by
              ext e
              simp only [Set.mem_empty_iff_false, iff_false]
              rintro ⟨_, he⟩
              rw [Wg _ k hk', ho] at he
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at he
              have := he u hu
              rw [if_neg hul] at this; cases this
            rw [this]
            exact emp _ _
        · rw [if_pos ho, List.foldl_append]
          rw [Wg _ k hk', ho] at h
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_false, Function.comp, id] at h
          have hop : ∀ m : ℕ, (if C.gates[k].inputs.getD m (n + k) < n + k then A (C.gates[k].inputs.getD m (n + k)) else ∅) ∈ List.foldl step (base T) (L k) := by
            intro m
            split_ifs with hm
            · rcases Nat.lt_or_ge m C.gates[k].inputs.length with h' | h'
              · have e : C.gates[k].inputs.getD m (n + k) = C.gates[k].inputs[m] := List.getD_eq_getElem _ _ h'
                have hh := h _ (List.getElem_mem h')
                rw [← e, if_pos hm] at hh
                exact ih' _ hm (by simpa using hh)
              · rw [List.getD_eq_default _ _ h'] at hm; omega
            · exact emp _ _
          refine Or.inr ⟨hop 0, hop 1, ?_⟩
          rintro e ⟨heE, he⟩
          rw [Wg _ k hk', ho] at he
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at he
          obtain ⟨u, hu, hut⟩ := he
          by_cases hul : u < n + k
          · rw [if_pos hul] at hut
            simp only [pr]
            generalize C.gates[k].inputs = l at hu hl
            rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
            · cases hu
            · have : u = a := by simpa using hu
              subst this
              left
              simp only [List.getD_cons_zero]
              rw [if_pos hul]
              exact ⟨heE, hut⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · left
                simp only [List.getD_cons_zero]
                rw [if_pos hul]
                exact ⟨heE, hut⟩
              · right
                simp only [List.getD_cons_succ, List.getD_cons_zero]
                rw [if_pos hul]
                exact ⟨heE, hut⟩
            · simp at hl
          · rw [if_neg hul] at hut; cases hut
  refine ⟨L C.gates.length, ?_, ?_⟩
  · have hlen : ∀ k ≤ C.gates.length, (L k).length = ((Finset.range k).filter fun j => (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or).card := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hk' : k < C.gates.length := by omega
        have e : C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk'
        rw [Ls k hk', List.length_append, ih (by omega), Finset.range_add_one, Finset.filter_insert, e]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]; rfl
        · rfl
    rw [hlen _ le_rfl]
    have e : {x11 : Fin C.gates.length | (C.gates.get x11).op = PEqualNP.CircuitLowerBounds.GateOp.or} = ↑(Finset.univ.filter fun x11 : Fin C.gates.length => (C.gates.get x11).op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
      ext j; simp
    rw [e, Set.ncard_coe_finset, ← Finset.card_map Fin.valEmbedding]
    refine Finset.card_le_card fun j hj => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have e2 : C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ = C.gates[j]'hj.1 := List.getD_eq_getElem _ _ hj.1
    rw [Finset.mem_map]
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h3 := hj.2
    rw [e2] at h3
    exact h3
  · intro T hT
    have hfalse : W (fun i => decide (i ∉ T)) C.output = false := by
      cases h : W (fun i => decide (i ∉ T)) C.output
      · rfl
      · obtain ⟨e, he, h1, h2⟩ := (hf _).1 h
        simp only [decide_eq_true_eq] at h1 h2
        rcases hT e he with h' | h'
        · exact absurd h' h1
        · exact absurd h' h2
    have hA : E ⊆ A C.output := by
      intro e he
      exact ⟨he, (hf (pt e)).2 ⟨e, he, by simp [pt], by simp [pt]⟩⟩
    by_cases ho : C.output < n + C.gates.length
    · exact sub _ _ _ _ (main T hT C.gates.length le_rfl _ ho hfalse) hA
    · refine sub _ _ _ _ (emp T _) ?_
      intro e he
      have := (hA he).2
      simp only [W] at this
      rw [List.getD_eq_default _ _ (by rw [PEqualNP.Research.PlaneFourOrReplay.simulation.run_length, List.length_ofFn]; omega)] at this
      cases this

open PEqualNP.Research.PlaneFourCoverCount in
theorem PEqualNP.Research.PlaneFourOrReplay : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => {x3 : Fin x2.gates.length | (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (42 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → x4 C → 34 ≤ x2 C := by
  dsimp only
  intro C mono computes
  let E : Set Pair := {e | incident e}
  have corr : ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔ ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
    intro x
    rw [computes]
    constructor
    · rintro ⟨u,v,h,a,b⟩
      exact ⟨(u,v),h,a,b⟩
    · rintro ⟨⟨u,v⟩,h,a,b⟩
      exact ⟨u,v,h,a,b⟩
  obtain ⟨rs,cost,works⟩ := PEqualNP.Research.PlaneFourOrReplay.simulation 42 E C mono corr
  exact (PEqualNP.Research.PlaneFourFirstJoin rs works).trans cost
