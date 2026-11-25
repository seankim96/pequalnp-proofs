import PEqualNP.Research.OrderThreePlaneRows

namespace PEqualNP.Research.OrderThreePlanePrefixes

open OrderThreePlanePrefixData

def code (isAnd : Bool) (a b : Nat) : Nat :=
  (if isAnd then 729 else 0) + 27 * min a b + max a b

def isAnd (g : Nat) := decide (729 ≤ g)
def left (g : Nat) := (g % 729)/27
def right (g : Nat) := g%27

def move (p : Perm) (g : Nat) := code (isAnd g) (p[left g]?.getD (left g)) (p[right g]?.getD (right g))

def binary (op : Bool) (a b : Signature) : Signature :=
  if op then (a.1 &&& b.1,a.2 &&& b.2) else (a.1 ||| b.1,a.2 ||| b.2)

def dominates (a b : Signature) : Bool :=
  (b.1 &&& a.1 == b.1) && (a.2 &&& b.2 == a.2)

def value (w : Array Signature) (g : Nat) :=
  binary (isAnd g) (w[left g]?.getD (0,0)) (w[right g]?.getD (0,0))

def admissible (w : Array Signature) (g : Nat) : Bool :=
  let b := value w g
  !(dominates (0,0) b || w.any (fun a => dominates a b))

def candidates (w : Array Signature) : List Nat :=
  (List.range w.size).flatMap fun a => (List.range w.size).flatMap fun b =>
    if a<b then ([code false a b,code true a b].filter (admissible w)) else []

-- Which first gate has already been built in each of the five tables.
def initial : Fin 5 → Option Nat := fun s => [none,some (code true 0 13),
  some (code false 0 1),some (code false 0 13),some (code false 0 14)][s.val]!

def bank (s : Fin 5) : Array Signature :=
  match initial s with
  | none => rawColumns
  | some g => rawColumns.push (value rawColumns g)

def witnessOk (s : Stage) (i : Nat) : Bool :=
  if i < s.representatives.size then s.nodes[i]? == s.representatives[i]?
  else
    let c := s.commands[i-s.representatives.size]?.getD 0
    let parent := c/8
    let gen := c%8
    parent < i && gen < s.permutations.size &&
      s.nodes[i]? == some (move (s.permutations[gen]?.getD #[]) (s.nodes[parent]?.getD 0))

inductive Reachable (s : Stage) : Nat → Prop
  | root {g} (h : g ∈ s.representatives) : Reachable s g
  | step {g p} (h : Reachable s g) (hp : p ∈ s.permutations) : Reachable s (move p g)

theorem nodes_sound (s : Stage)
    (checks : (List.range s.nodes.size).all (witnessOk s) = true) (i : Nat) (hi : i < s.nodes.size) :
    Reachable s s.nodes[i] := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have ok := List.all_eq_true.mp checks i (List.mem_range.mpr hi)
    unfold witnessOk at ok
    split at ok
    next hroot =>
      have eq : s.nodes[i] = s.representatives[i] := by
        simpa [hi,hroot] using beq_iff_eq.mp ok
      exact eq ▸ Reachable.root (Array.getElem_mem hroot)
    next hother =>
      let c := s.commands[i - s.representatives.size]?.getD 0
      have parts := Bool.and_eq_true_iff.mp ok
      have limits := Bool.and_eq_true_iff.mp parts.1
      have lt : c/8 < i := of_decide_eq_true limits.1
      have gen : c%8 < s.permutations.size := of_decide_eq_true limits.2
      have parent := Nat.lt_trans lt hi
      have eq : s.nodes[i] = move s.permutations[c%8] s.nodes[c/8] := by
        have direct : s.nodes[i]? = some (move (s.permutations[c%8]?.getD #[]) (s.nodes[c/8]?.getD 0)) :=
          beq_iff_eq.mp parts.2
        simpa [hi,gen,parent] using direct
      rw [eq]
      exact .step (ih _ lt parent) (Array.getElem_mem gen)

def table (i : Fin 5) : Stage := stages[i.val]?.getD stage0

end PEqualNP.Research.OrderThreePlanePrefixes
