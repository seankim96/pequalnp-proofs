import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlaneFirstAndSeparation

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) : List Column :=
  s ++ [fun r => wire s g.1 r || wire s g.2 r]
def good (p a b : Nat) (w : Column) := w p = true → w a = true ∨ w b = true

private def From (base : List Column) (w : Column) :=
  ∃ ws : List Column, (∀ v ∈ ws, v ∈ base) ∧ w = disj ws

private theorem readFrom {base s : List Column} (h : ∀ v ∈ s, From base v) (i : Nat) :
    From base (wire s i) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases he : s[i]? with
  | none => exact ⟨[],by simp,rfl⟩
  | some w => exact h w (List.mem_of_getElem? he)

private theorem allFrom (base : List Column) (gs : List (Nat × Nat)) :
    ∀ v ∈ gs.foldl addOr base, From base v := by
  have step (s : List Column) (g : Nat × Nat) (hs : ∀ v ∈ s, From base v) :
      ∀ v ∈ addOr s g, From base v := by
    intro v hv
    rcases List.mem_append.mp hv with old | newWire
    · exact hs v old
    · obtain rfl := List.mem_singleton.mp newWire
      obtain ⟨l,hl,el⟩ := readFrom hs g.1
      obtain ⟨r,hr,er⟩ := readFrom hs g.2
      refine ⟨l ++ r,?_,?_⟩
      · intro w hw
        exact (List.mem_append.mp hw).elim (hl w) (hr w)
      · funext i
        simp [el,er,disj]
  have run (gates : List (Nat × Nat)) (s : List Column) (hs : ∀ v ∈ s, From base v) :
      ∀ v ∈ gates.foldl addOr s, From base v := by
    induction gates generalizing s with
    | nil => exact hs
    | cons g tail ih => exact ih _ (step s g hs)
  apply run
  intro v hv
  refine ⟨[v],by simpa using hv,?_⟩
  funext r
  simp [disj]

private theorem fromGood {base : List Column} {w : Column} {p a b : Nat}
    (h : From base w) (hb : ∀ v ∈ base, good p a b v) : good p a b w := by
  obtain ⟨ws,sub,rfl⟩ := h
  intro hpos
  obtain ⟨v,hv,hp⟩ := List.any_eq_true.mp hpos
  rcases hb v (sub v hv) hp with ha | hc
  · exact Or.inl (List.any_eq_true.mpr ⟨v,hv,ha⟩)
  · exact Or.inr (List.any_eq_true.mpr ⟨v,hv,hc⟩)

def separated (s : List Column) :=
  ∃ n : Fin 257 → Fin 468, ∀ i j : Fin 257, i.val < j.val →
    ∃ p : Fin 52, ∀ w ∈ s, good p.val (52 + (n i).val) (52 + (n j).val) w

end PEqualNP.Research.PlaneFirstAndSeparation

open PEqualNP.Research.PlaneFirstAndSeparation in
theorem PEqualNP.Research.PlaneFirstAndSeparation : ∀ (base : List Column)
    (gs : List (Nat × Nat)) (left right : Nat),
    (∀ l r : List Column, (∀ w ∈ l, w ∈ base) → (∀ w ∈ r, w ∈ base) →
      separated (base ++ [both (disj l) (disj r)])) →
    let s := gs.foldl addOr base
    separated (s ++ [both (wire s left) (wire s right)]) := by
  intro base gs left right h
  let s := gs.foldl addOr base
  have hs : ∀ v ∈ s, From base v := allFrom base gs
  obtain ⟨l,hl,el⟩ := readFrom hs left
  obtain ⟨r,hr,er⟩ := readFrom hs right
  obtain ⟨n,hn⟩ := h l r hl hr
  refine ⟨n,?_⟩
  intro i j lt
  obtain ⟨p,hp⟩ := hn i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact fromGood (hs w old) (fun v hv => hp v (List.mem_append_left _ hv))
  · obtain rfl := List.mem_singleton.mp last
    change good _ _ _ (both (wire s left) (wire s right))
    rw [el,er]
    exact hp _ (by simp)
