import PEqualNP.Outside.L_meta_2780

/-! On a fixed line, compare the no-point input with the incident singleton
inputs. A wire's mask consists of the rows it changes from false to true on.
An AND can be followed through one operand. An OR needs two only if the
operand masks are incomparable. The counting below allows arbitrary fan-out. -/

namespace PEqualNP.Research.LineSliceOrBudget

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2780

variable {ι : Type} [DecidableEq ι]

private def Budget (ready : Finset ι → Prop) (k : ℕ) : Prop :=
  ∀ T : Finset (Finset ι), (∀ s ∈ T, ready s) → (T.biUnion id).card ≤ T.card + k

private theorem initial (ready : Finset ι → Prop) (small : ∀ s, ready s → s.card ≤ 1) :
    Budget ready 0 := by
  intro T h
  have sum := Finset.sum_le_sum (s := T) (g := fun _ => (1 : ℕ)) (fun s hs => small s (h s hs))
  have u := Finset.card_biUnion_le (s := T) (t := id)
  simp only [id_eq] at u
  exact u.trans (by simpa using sum)

private theorem extend {ready next : Finset ι → Prop} {k d : ℕ} (prev : Budget ready k)
    (newMask : Finset ι) (inputs : Finset (Finset ι)) (built : ∀ s ∈ inputs, ready s)
    (covered : newMask ⊆ inputs.biUnion id) (arity : inputs.card ≤ d+1)
    (step : ∀ s, next s → s = newMask ∨ ready s) : Budget next (k+d) := by
  intro T available
  by_cases used : newMask ∈ T
  · let old := T.erase newMask ∪ inputs
    have readyOld : ∀ s ∈ old, ready s := by
      intro s hs
      rcases Finset.mem_union.mp hs with h|h
      · exact (step s (available s (Finset.mem_erase.mp h).2)).resolve_left (Finset.mem_erase.mp h).1
      · exact built s h
    have incl : T.biUnion id ⊆ old.biUnion id := by
      intro p hp
      obtain ⟨s,hs,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases eq : s = newMask
      · obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp (covered (eq ▸ hp))
        exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_union_right _ hv,hp⟩
      · exact Finset.mem_biUnion.mpr ⟨s,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hs⟩),hp⟩
    have h1 := (Finset.card_le_card incl).trans (prev old readyOld)
    have h2 : old.card ≤ (T.erase newMask).card + inputs.card := Finset.card_union_le _ _
    have h3 := Finset.card_erase_add_one used
    omega
  · have h := prev T (fun s hs => (step s (available s hs)).resolve_left (fun eq => used (eq ▸ hs)))
    omega

def mask (F : Finset ι) (base : List Bool) (row : ι → List Bool) (i : ℕ) : Finset ι :=
  F.filter (fun p => base.getD i false = false ∧ (row p).getD i false = true)

private def bit (g : Gate) (U : List Bool) : Bool := g.op.eval (g.inputs.map fun i => U.getD i false)
private def push (g : Gate) (U : List Bool) : List Bool := U ++ [bit g U]

/-- A binary OR really branches on this slice when both operands are false at
the base and each accepts a singleton rejected by the other operand. -/
def splits (F : Finset ι) (base : List Bool) (row : ι → List Bool) (g : Gate) : Prop :=
  g.op = .or ∧ ∃ a b, g.inputs = [a,b] ∧ base.getD a false = false ∧ base.getD b false = false ∧
    ¬ mask F base row a ⊆ mask F base row b ∧ ¬ mask F base row b ⊆ mask F base row a

noncomputable local instance (F : Finset ι) (U : List Bool) (V : ι → List Bool) (g : Gate) :
    Decidable (splits F U V g) := Classical.propDecidable _

noncomputable def charges (F : Finset ι) (base : List Bool) (row : ι → List Bool) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if splits F base row g then 1 else 0) + charges F (push g base) (fun p => push g (row p)) gs

private def ready (F : Finset ι) (U : List Bool) (V : ι → List Bool) (s : Finset ι) : Prop :=
  ∃ i, mask F U V i = s

private theorem oneStep (F : Finset ι) (U : List Bool) (V : ι → List Bool)
    (len : ∀ p, (V p).length = U.length) (g : Gate) (binary : g.inputs.length = 2)
    (ao : g.op = .and ∨ g.op = .or) {k : ℕ} (prior : Budget (ready F U V) k) :
    Budget (ready F (push g U) (fun p => push g (V p))) (k + (if splits F U V g then 1 else 0)) := by
  classical
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp binary
  let A := mask F U V a
  let B := mask F U V b
  let N := F.filter (fun p => bit g U = false ∧ bit g (V p) = true)
  have atNew (s : Finset ι) (hs : ready F (push g U) (fun p => push g (V p)) s) : s = N ∨ ready F U V s := by
    obtain ⟨i,rfl⟩ := hs
    rcases Nat.lt_trichotomy i U.length with h|h|h
    · right; refine ⟨i, ?_⟩
      ext p
      simp only [mask,Finset.mem_filter,push,getD_snoc_lt _ _ _ h,getD_snoc_lt _ _ _ (show i < (V p).length by rw [len];exact h)]
    · left; subst i; ext p; simp [mask,N,push, ← len p]
    · right; refine ⟨i, ?_⟩
      ext p
      constructor
      · intro old
        have on := (Finset.mem_filter.mp old).2.2
        rw [List.getD_eq_default _ _ (show (V p).length ≤ i by rw [len];omega)] at on
        contradiction
      · intro fresh
        have on := (Finset.mem_filter.mp fresh).2.2
        change (V p ++ [bit g (V p)]).getD i false = true at on
        rw [getD_snoc_gt _ _ _ (show (V p).length < i by rw [len];exact h)] at on
        contradiction
  have branchOne (w : ℕ) (sub : N ⊆ mask F U V w) :
      Budget (ready F (push g U) (fun p => push g (V p))) (k+0) := by
    apply extend prior N {mask F U V w} _ _ (by simp) atNew
    · intro s hs; exact ⟨w,(Finset.mem_singleton.mp hs).symm⟩
    · simpa using sub
  have orBit (op : g.op = .or) (W : List Bool) :
      bit g W = (W.getD a false || W.getD b false) := by simp [bit,op,ab,GateOp.eval]
  have andBit (op : g.op = .and) (W : List Bool) :
      bit g W = (W.getD a false && W.getD b false) := by simp [bit,op,ab,GateOp.eval]
  have orCover (op : g.op = .or) (ua : U.getD a false = false) (ub : U.getD b false = false) : N ⊆ A ∪ B := by
    intro p h
    obtain ⟨hp,_,hon⟩ := Finset.mem_filter.mp h
    rw [orBit op] at hon
    exact (Bool.or_eq_true_iff.mp hon).elim
      (fun h => Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,ua,h⟩))
      (fun h => Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,ub,h⟩))
  by_cases separated : splits F U V g
  · simp only [ite_eq_left separated]
    obtain ⟨op,aa,bb,hab,ua,ub,_,_⟩ := separated
    have eqs : aa = a ∧ bb = b := by simpa using hab.symm.trans ab
    obtain ⟨rfl,rfl⟩ := eqs
    apply extend prior N {A,B} _ _ _ atNew
    · intro s hs; rcases Finset.mem_insert.mp hs with rfl|h
      · exact ⟨_,rfl⟩
      · exact ⟨_,(Finset.mem_singleton.mp h).symm⟩
    · simpa using orCover op ua ub
    · exact Finset.card_insert_le _ _ |>.trans (by simp)
  · simp only [ite_eq_right separated]
    have oneAnd (op : g.op = .and) : N ⊆ A ∨ N ⊆ B := by
      by_cases ua : U.getD a false = false
      · left; intro p h
        obtain ⟨hp,_,on⟩ := Finset.mem_filter.mp h
        rw [andBit op] at on
        exact Finset.mem_filter.mpr ⟨hp,ua,(Bool.and_eq_true_iff.mp on).1⟩
      · right; intro p h
        obtain ⟨hp,off,on⟩ := Finset.mem_filter.mp h
        rw [andBit op] at on off
        exact Finset.mem_filter.mpr ⟨hp,(Bool.and_eq_false_iff.mp off).resolve_left ua,(Bool.and_eq_true_iff.mp on).2⟩
    have oneOr (op : g.op = .or) : N ⊆ A ∨ N ⊆ B := by
      by_cases ub : U.getD a false = false ∧ U.getD b false = false
      · have cmp : A ⊆ B ∨ B ⊆ A := by
          by_contra! bad
          exact separated ⟨op,a,b,ab,ub.1,ub.2,bad.1,bad.2⟩
        have sub := orCover op ub.1 ub.2
        exact cmp.elim (fun h => Or.inr (sub.trans (Finset.union_subset h (by rfl)))) (fun h => Or.inl (sub.trans (Finset.union_subset (by rfl) h)))
      · left; intro p h
        have off := (Finset.mem_filter.mp h).2.1
        rw [orBit op] at off
        exact (ub (Bool.or_eq_false_iff.mp off)).elim
    rcases ao.elim oneAnd oneOr with h|h
    · exact branchOne a h
    · exact branchOne b h

private theorem propagate (F : Finset ι) (gs : List Gate)
    (leg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (U : List Bool) (V : ι → List Bool) (len : ∀ p, (V p).length = U.length)
    {k : ℕ} (budget : Budget (ready F U V) k) :
    Budget (ready F (wf gs U) (fun p => wf gs (V p))) (k + charges F U V gs) := by
  classical
  induction gs generalizing U V k with
  | nil => simpa [wf, charges] using budget
  | cons g gs ih =>
    have first := leg g (by simp)
    have step := oneStep F U V len g first.2 first.1 budget
    have h := ih (fun j hj => leg j (by simp [hj])) (push g U) (fun p => push g (V p))
      (fun p => by simp [push,len]) step
    simpa only [wf_cons,charges,Nat.add_assoc,push,bit] using h

/-- The number of singleton changes observed at an output is bounded by one plus
the number of OR gates with incomparable operand masks on that very slice. -/
theorem singleton_budget (F : Finset ι) (gs : List Gate)
    (leg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (U : List Bool) (V : ι → List Bool) (len : ∀ p, (V p).length = U.length)
    (small : ∀ i, (mask F U V i).card ≤ 1) (out : ℕ) :
    (mask F (wf gs U) (fun p => wf gs (V p)) out).card ≤ charges F U V gs + 1 := by
  let final := mask F (wf gs U) (fun p => wf gs (V p)) out
  have base := initial (ready F U V) (by rintro _ ⟨i,rfl⟩; exact small i)
  have budget := propagate F gs leg U V len base
  have bound := budget {final} (by intro s hs; exact ⟨out,(Finset.mem_singleton.mp hs).symm⟩)
  simpa [final,Nat.add_comm] using bound

variable {n m : ℕ}

private theorem single_input (F : Finset (Fin n)) (Y : Finset (Fin m)) (i : ℕ) :
    (mask F (incidenceInput (∅ : Finset (Fin n)) Y) (fun p => incidenceInput {p} Y) i).card ≤ 1 := by
  by_cases hi : i < n
  · apply Finset.card_le_one_iff.mpr
    intro p r hp hr
    have point (v : Fin n) (h : v ∈ mask F (incidenceInput (∅ : Finset (Fin n)) Y) (fun t => incidenceInput {t} Y) i) :
        (⟨i,hi⟩ : Fin n) = v := by
      have z := (Finset.mem_filter.mp h).2.2
      unfold incidenceInput at z
      rw [List.getD_append _ _ _ _ (by simpa using hi)] at z
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn,hi] using z
    exact (point p hp).symm.trans (point r hr)
  · have zero : mask F (incidenceInput (∅ : Finset (Fin n)) Y) (fun p => incidenceInput {p} Y) i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨off,on⟩ := (Finset.mem_filter.mp hp).2
      unfold incidenceInput at off on
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)] at off on
      simp only [List.length_ofFn] at off on
      exact Bool.noConfusion (off.symm.trans on)
    simp [zero]

/-- Every line with d incident points needs at least d−1 distinct branching OR
gates. Only incident pairs and the empty-point negative on this line are used. -/
theorem line_budget (S : Fin m → Finset (Fin n)) (C : Circuit) (l : Fin m)
    (ao : IsAO2 (n+m) C) (pairs : RightOnIncidentPairs S C)
    (off : C.eval (incidenceInput (∅ : Finset (Fin n)) {l}) = false) :
    (S l).card ≤ charges (S l) (incidenceInput (∅ : Finset (Fin n)) {l}) (fun p => incidenceInput {p} {l}) C.gates + 1 := by
  have bound := singleton_budget (S l) C.gates (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩)
    (incidenceInput (∅ : Finset (Fin n)) {l}) (fun p => incidenceInput {p} {l})
    (fun _ => by simp [incidenceInput]) (single_input _ _) C.output
  have full : mask (S l) (wf C.gates (incidenceInput (∅ : Finset (Fin n)) {l}))
      (fun p => wf C.gates (incidenceInput {p} {l})) C.output = S l := by
    apply Finset.filter_true_of_mem
    intro p hp
    exact ⟨off,pairs l p hp⟩
  rwa [full] at bound


omit [DecidableEq ι] in
/-- If the total over all experiments exceeds b times the number of gates,
some one gate genuinely splits on more than b experiments. -/
private theorem congestion {L : Type} [Fintype L] [DecidableEq L] (bound : ℕ)
    (F : L → Finset ι) (gs : List Gate) (U : L → List Bool) (V : L → ι → List Bool)
    (excess : bound * gs.length < ∑ l, charges (F l) (U l) (V l) gs) :
    ∃ pre g post, gs = pre ++ g :: post ∧
      bound < (Finset.univ.filter (fun l => splits (F l) (wf pre (U l)) (fun p => wf pre (V l p)) g)).card := by
  classical
  induction gs generalizing U V with
  | nil => simp [charges] at excess
  | cons g gs ih =>
    let active := Finset.univ.filter fun l => splits (F l) (U l) (V l) g
    by_cases crowded : bound < active.card
    · exact ⟨[],g,gs,rfl,crowded⟩
    · have flags : (∑ l, if splits (F l) (U l) (V l) g then 1 else 0) = active.card := by
        simp [active,Finset.sum_boole]
      simp only [charges,Finset.sum_add_distrib,flags,List.length_cons,Nat.mul_succ] at excess
      obtain ⟨pre,j,post,eq,hj⟩ := ih (fun l => push g (U l)) (fun l p => push g (V l p)) (by omega)
      exact ⟨g::pre,j,post,congrArg (g :: ·) eq,hj⟩

/-- A circuit below the proposed bound must split the incident point rows of
at least 101 distinct lines at one and the same OR gate. -/
theorem crowded_gate {n q : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (lineCard : ∀ l, (S l).card = q+1) (ao : IsAO2 (n+n) C)
    (pairs : RightOnIncidentPairs S C)
    (off : ∀ l : Fin n, C.eval (incidenceInput (∅ : Finset (Fin n)) {l}) = false)
    (tooSmall : 100*C.size < n*q) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧
      100 < (Finset.univ.filter (fun l => splits (S l)
        (wf pre (incidenceInput (∅ : Finset (Fin n)) {l}))
        (fun p => wf pre (incidenceInput {p} {l})) g)).card := by
  let cost := fun l : Fin n => charges (S l) (incidenceInput (∅ : Finset (Fin n)) {l}) (fun p => incidenceInput {p} {l}) C.gates
  have lower (l : Fin n) : q ≤ cost l := by
    have h := line_budget S C l ao pairs (off l)
    rw [lineCard] at h
    exact Nat.le_of_succ_le_succ h
  have total : n*q ≤ ∑ l, cost l := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun l _ => lower l)
  exact congestion 100 S C.gates _ _ (tooSmall.trans_le total)

/-- The first premise of the proposed reduction, in its project-facing form. -/
theorem locate : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ l, (S l).card = q+1) → IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ (l : Fin n) (X : Finset (Fin n)), X.card = 0 → C.eval (incidenceInput X {l}) = false) →
      100*C.size < n*q → (∃ (pre post : List Gate) (a b : ℕ) (L : Finset (Fin n)),
          C.gates = pre ++ ⟨.or,[a,b]⟩ :: post ∧ 100 < L.card ∧
          ∀ l ∈ L, ∀ w ∈ [(a,b),(b,a)], ∃ p ∈ S l,
            let z := (⟨pre,0⟩ : Circuit).wires (incidenceInput {p} {l})
            z.getD w.1 false = true ∧ z.getD w.2 false = false) := by
  classical
  intro q n S C card ao pairs off small
  obtain ⟨pre,g,post,decomp,many⟩ := crowded_gate S C card ao pairs (fun l => off l ∅ (by simp)) small
  let U (l : Fin n) := wf pre (incidenceInput (∅ : Finset (Fin n)) {l})
  let V (l p : Fin n) := wf pre (incidenceInput {p} {l})
  let L := Finset.univ.filter fun l => splits (S l) (U l) (V l) g
  change 100 < L.card at many
  obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < L.card by omega)
  obtain ⟨op,a,b,ins,_,_,_,_⟩ := (Finset.mem_filter.mp hl).2
  have shape : g = ⟨.or,[a,b]⟩ := by cases g; simp_all
  refine ⟨pre,post,a,b,L,shape ▸ decomp,many,?_⟩
  intro l hl w hw
  obtain ⟨_,a',b',ins',ua,ub,ab,ba⟩ := (Finset.mem_filter.mp hl).2
  have eq : a' = a ∧ b' = b := by simpa using ins'.symm.trans ins
  obtain ⟨rfl,rfl⟩ := eq
  have witness (i j : ℕ) (offj : (U l).getD j false = false)
      (diff : ¬ mask (S l) (U l) (V l) i ⊆ mask (S l) (U l) (V l) j) :
      ∃ p ∈ S l, (V l p).getD i false = true ∧ (V l p).getD j false = false := by
    obtain ⟨p,yes,no⟩ := Finset.not_subset.mp diff
    obtain ⟨hp,_,on⟩ := Finset.mem_filter.mp yes
    refine ⟨p,hp,on,?_⟩
    cases hj : (V l p).getD j false with
    | false => rfl
    | true => exact (no (Finset.mem_filter.mpr ⟨hp,offj,hj⟩)).elim
  rcases List.mem_cons.mp hw with rfl|h
  · exact witness _ _ ub ab
  · have eqw := List.mem_singleton.mp h
    subst w
    exact witness _ _ ua ba


/-- With several selected lines, every point in their union gives a positive
singleton row. Thus even with nested ANDs the circuit must branch on all but
one of those points, as counted by distinct OR positions on this input slice. -/
theorem sparse_budget (S : Fin m → Finset (Fin n)) (C : Circuit) (q : ℕ)
    (Y : Finset (Fin m)) (sparse : Y.card ≤ q) (ao : IsAO2 (n+m) C)
    (pairs : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    (Y.biUnion S).card ≤ charges (Y.biUnion S) (incidenceInput (∅ : Finset (Fin n)) Y)
      (fun p => incidenceInput {p} Y) C.gates + 1 := by
  have bound := singleton_budget (Y.biUnion S) C.gates (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩)
    (incidenceInput (∅ : Finset (Fin n)) Y) (fun p => incidenceInput {p} Y)
    (fun _ => by simp [incidenceInput]) (single_input _ _) C.output
  have off := sound (∅ : Finset (Fin n)) Y sparse (fun _ _ => Finset.disjoint_empty_right _)
  have full : mask (Y.biUnion S) (wf C.gates (incidenceInput (∅ : Finset (Fin n)) Y))
      (fun p => wf C.gates (incidenceInput {p} Y)) C.output = Y.biUnion S := by
    apply Finset.filter_true_of_mem
    intro p hp
    obtain ⟨l,hl,pl⟩ := Finset.mem_biUnion.mp hp
    refine ⟨off,?_⟩
    apply mono2 C.gates (fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩)
      (incidenceInput {p} {l}) (incidenceInput {p} Y) (by simp [incidenceInput]) _ C.output (pairs l p pl)
    apply app_mono _ _ _ _ (by simp)
    · exact fun _ h => h
    · apply ofFn_mono
      intro i hi
      have eq : i = l := by simpa using hi
      simpa [eq] using hl
  rwa [full] at bound

/-- Distinct lines through a fixed point have disjoint sets of other points.
A pencil of t selected lines therefore offers exactly t*q+1 positive rows. -/
theorem pencil_union (S : Fin m → Finset (Fin n)) (q : ℕ) (card : ∀ l, (S l).card = q+1)
    (unique : ∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (p : Fin n) (Y : Finset (Fin m)) (nonempty : Y.Nonempty) (common : ∀ l ∈ Y, p ∈ S l) :
    (Y.biUnion S).card = Y.card*q + 1 := by
  let rest := fun l => (S l).erase p
  have disj : (Y : Set (Fin m)).PairwiseDisjoint rest := by
    intro l hl k hk ne
    apply Finset.disjoint_left.mpr
    intro r hr hs
    have left := Finset.mem_erase.mp hr
    have right := Finset.mem_erase.mp hs
    obtain ⟨j,_,only⟩ := unique r p left.1
    exact ne ((only l ⟨left.2,common l hl⟩).trans (only k ⟨right.2,common k hk⟩).symm)
  have erased : (Y.biUnion S).erase p = Y.biUnion rest := by
    ext r
    simp [rest,Finset.mem_biUnion]
    grind
  have count (l : Fin m) (hl : l ∈ Y) : (rest l).card = q := by
    have h := Finset.card_erase_add_one (common l hl)
    rw [card] at h
    exact Nat.add_right_cancel h
  obtain ⟨l,hl⟩ := nonempty
  have h := Finset.card_erase_add_one (Finset.mem_biUnion.mpr ⟨l,hl,common l hl⟩)
  rw [erased, Finset.card_biUnion disj, Finset.sum_congr rfl count] at h
  simpa using h.symm


private def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false

omit [DecidableEq ι] in
private theorem charge_le_or (F : Finset ι) (gs : List Gate) (U : List Bool) (V : ι → List Bool) :
    charges F U V gs ≤ (gs.filter isOr).length := by
  classical
  induction gs generalizing U V with
  | nil => simp [charges]
  | cons g gs ih =>
    have h := ih (push g U) (fun p => push g (V p))
    by_cases s : splits F U V g
    · simp [charges,s,isOr,s.1] at *
      omega
    · cases op : isOr g <;> simp [charges,s,op] <;> omega

/-- A q-line pencil forces q² distinct OR gates in the unrestricted circuit.
No hypothesis is imposed on the position of the output or the nesting of ANDs. -/
theorem quadratic_or {q n : ℕ} (positive : 0 < q) (size : 0 < n)
    (S : Fin n → Finset (Fin n)) (card : ∀ l, (S l).card = q+1)
    (unique : ∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (C : Circuit) (ao : IsAO2 (n+n) C) (pairs : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    q*q ≤ (C.gates.filter (fun g => match g.op with | .or => true | _ => false)).length := by
  classical
  let through (p : Fin n) := Finset.univ.filter fun l => p ∈ S l
  have count : (∑ p, (through p).card) = n*(q+1) := by
    calc
      _ = ∑ p : Fin n, ∑ l : Fin n, if p ∈ S l then 1 else 0 := by simp [through,Finset.sum_boole]
      _ = ∑ l : Fin n, ∑ p : Fin n, if p ∈ S l then 1 else 0 := Finset.sum_comm
      _ = n*(q+1) := by simp [card]
  obtain ⟨p,hp⟩ : ∃ p : Fin n, q ≤ (through p).card := by
    by_contra! all
    have h := Finset.sum_le_sum (s := Finset.univ) (g := fun _ => q) (fun p _ => (all p).le)
    rw [count] at h
    have lt := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self q) size
    exact (not_lt_of_ge (by simpa using h : n*(q+1) ≤ n*q)) lt
  obtain ⟨Y,sub,hy⟩ := Finset.exists_subset_card_eq hp
  have nonempty : Y.Nonempty := Finset.card_pos.mp (hy ▸ positive)
  have union := pencil_union S q card unique p Y nonempty (fun l hl => (Finset.mem_filter.mp (sub hl)).2)
  have need := sparse_budget S C q Y hy.le ao pairs sound
  rw [union,hy] at need
  exact (Nat.le_of_succ_le_succ need).trans (charge_le_or _ _ _ _)


/-- With all points selected, independently switching on any nonempty line
changes the output. At least m−1 distinct OR positions must split on this
single experiment; the same conclusion holds with arbitrary AND depth. -/
theorem all_points_or (S : Fin m → Finset (Fin n)) (C : Circuit)
    (line : ∀ l, (S l).Nonempty) (ao : IsAO2 (n+m) C)
    (pairs : RightOnIncidentPairs S C)
    (off : C.eval (incidenceInput (Finset.univ : Finset (Fin n)) (∅ : Finset (Fin m))) = false) :
    m ≤ (C.gates.filter (fun g => match g.op with | .or => true | _ => false)).length + 1 := by
  let X : Finset (Fin n) := Finset.univ
  let U := incidenceInput X (∅ : Finset (Fin m))
  let V (l : Fin m) := incidenceInput X {l}
  have small (i : ℕ) : (mask Finset.univ U V i).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro l k hl hk
    have eq (j : Fin m) (hj : j ∈ mask Finset.univ U V i) : i = n+j.val := by
      obtain ⟨offi,oni⟩ := (Finset.mem_filter.mp hj).2
      change (incidenceInput X (∅ : Finset (Fin m))).getD i false = false at offi
      change (incidenceInput X {j}).getD i false = true at oni
      unfold incidenceInput at offi oni
      by_cases pt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa using pt)] at offi oni
        exact Bool.noConfusion (offi.symm.trans oni)
      · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt pt)] at oni
        simp only [List.length_ofFn] at oni
        by_cases valid : i-n < m
        · have same : (⟨i-n,valid⟩ : Fin m) = j := by simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,valid] using oni
          have val := congrArg Fin.val same
          change i-n = j.val at val
          omega
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid)] at oni
          contradiction
    exact Fin.ext (by have e := eq l hl; have f := eq k hk; omega)
  have budget := singleton_budget (Finset.univ : Finset (Fin m)) C.gates
    (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩) U V (fun _ => by simp [U,V,incidenceInput]) small C.output
  have full : mask Finset.univ (wf C.gates U) (fun l => wf C.gates (V l)) C.output = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro l _
    obtain ⟨p,hp⟩ := line l
    refine ⟨off,?_⟩
    apply mono2 C.gates (fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩)
      (incidenceInput {p} {l}) (incidenceInput X {l}) (by simp [incidenceInput]) _ C.output (pairs l p hp)
    apply app_mono _ _ _ _ (by simp)
    · apply ofFn_mono; intro i _; simp [X]
    · exact fun _ h => h
  rw [full] at budget
  have h := budget.trans (Nat.add_le_add_right (charge_le_or _ _ _ _) 1)
  change m ≤ (C.gates.filter isOr).length + 1
  simpa only [Finset.card_univ,Fintype.card_fin] using h

end PEqualNP.Research.LineSliceOrBudget
