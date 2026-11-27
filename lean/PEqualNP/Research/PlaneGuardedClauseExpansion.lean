import Mathlib.Data.List.Basic

namespace PEqualNP.Research.PlaneGuardedClauseExpansion.Core
abbrev Side := List (Nat × Bool)
abbrev Row := Nat → Bool
def hit (s : Side) (g : Bool) (r : Row) := s.any (fun l => r l.1 && (!l.2 || g))
def push (r : Row) (v : Bool) : Row := fun i => if i = 0 then v else r (i-1)
def step (g : Bool) (r : Row) (gate : Side × Side) :=
  push r (hit gate.1 g r && hit gate.2 g r)

private def plug (new : Side) (s : Side) : Side :=
  s.flatMap (fun l => if l.1 = 0 then new.map (fun t => (t.1, t.2 || l.2))
    else [(l.1-1, l.2)])

private theorem plug_hit (new s : Side) (g : Bool) (r : Row) :
    hit (plug new s) g r = hit s g (push r (hit new g r)) := by
  induction s with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨k,b⟩
    cases k with
    | zero =>
      simp only [plug, List.flatMap_cons, if_pos rfl, hit, List.any_append, List.any_map,
        List.any_cons, push, Function.comp_def] at *
      cases b <;> cases g <;> simp_all [Bool.and_assoc, Function.comp_def] <;> rfl
    | succ k =>
      simp only [plug, List.flatMap_cons, Nat.succ_ne_zero, if_false, List.singleton_append,
        hit, List.any_cons, push] at *
      simp_all

private theorem hit_mono (s : Side) (g : Bool) (r : Row) :
    hit s g (push r false) = true → hit s g (push r true) = true := by
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  rintro ⟨l, hl, a, b⟩
  refine ⟨l, hl, ?_, b⟩
  by_cases h : l.1 = 0 <;> simp_all [push]

private theorem meet_hit (s : Side) (g : Bool) (r : Row) (a b : Bool) :
    hit s g (push r (a && b)) = (hit s g (push r a) && hit s g (push r b)) := by
  have h := hit_mono s g r
  cases a <;> cases b <;> simp_all <;>
    cases ha : hit s g (push r false) <;> cases hb : hit s g (push r true) <;> simp_all

private theorem allBoth {α : Type} (cs : List α) (f h : α → Bool) :
    cs.all (fun s => f s && h s) = (cs.all f && cs.all h) := by
  induction cs with
  | nil => rfl
  | cons a cs ih => simp [ih, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
end PEqualNP.Research.PlaneGuardedClauseExpansion.Core
open PEqualNP.Research.PlaneGuardedClauseExpansion.Core in
theorem PEqualNP.Research.PlaneGuardedClauseExpansion : ∀ (gates : List (Side × Side)) (out : Side),
  ∃ clauses : List Side, clauses.length = 2 ^ gates.length ∧
    ∀ (g : Bool) (r : Row), hit out g (gates.foldl (step g) r) = clauses.all (fun s => hit s g r) := by
  intro gates
  induction gates with
  | nil =>
    intro out
    exact ⟨[out], by simp, by simp⟩
  | cons gate gates ih =>
    intro out
    obtain ⟨cs, size, spec⟩ := ih out
    refine ⟨cs.map (plug gate.1) ++ cs.map (plug gate.2), ?_, ?_⟩
    · simp only [List.length_append, List.length_map, size, List.length_cons]
      rw [Nat.pow_succ, Nat.mul_two]
    · intro g r
      rw [List.foldl_cons, spec]
      simp only [List.all_append, List.all_map, Function.comp_def, plug_hit]
      simp only [step, meet_hit, allBoth]
