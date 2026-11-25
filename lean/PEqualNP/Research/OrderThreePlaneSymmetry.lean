import PEqualNP.Research.OrderThreePlanePrefixes

/-! Each base symmetry permutes the positive and negative rows. A certificate
lists the destination of every row. Arbitrary words preserve both sets. -/

namespace PEqualNP.Research.OrderThreePlanePrefixes

open OrderThreePlanePrefixData

def coord (p : Perm) (i : Nat) := p[i]?.getD i

def Agrees (p : Perm) (x y : Nat) : Prop :=
  ∀ i < 26, y.testBit i = x.testBit (coord p i)

def Preserves (p : Perm) (rs : Array Nat) : Prop :=
  (∀ x ∈ rs, ∃ y ∈ rs, Agrees p x y) ∧
  (∀ y ∈ rs, ∃ x ∈ rs, Agrees p x y)

structure PlaneSymmetry (p : Perm) : Prop where
  size : p.size = 26
  bound : ∀ i < 26, coord p i < 26
  positiveRows : Preserves p positive
  negativeRows : Preserves p negative

private theorem pull_agrees (p : Perm) (x : Nat) : Agrees p x (pull p x) := by
  intro i hi
  exact bit_rowOf _ i hi

private def block (f : Nat → Bool) : Nat → Nat → Bool
  | 0, i => f i
  | d+1, i => block f d i && block f d (i+2^d)

private theorem block_join {f d i} (lo : block f d i = true)
    (hi : block f d (i+2^d) = true) : block f (d+1) i = true :=
  Bool.and_eq_true_iff.mpr ⟨lo,hi⟩

private theorem block_sound {f : Nat → Bool} (d i j : Nat) (lo : i ≤ j) (hi : j < i+2^d)
    (h : block f d i = true) : f j = true := by
  induction d generalizing i with
  | zero =>
    have eq : i = j := by omega
    simpa [block,eq] using h
  | succ d ih =>
    rw [Nat.pow_succ] at hi
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    by_cases early : j < i+2^d
    · exact ih i lo early left
    · exact ih (i+2^d) (by omega) (by omega) right


private def edge (p : Perm) (rs keys : Array Nat) (i : Nat) : Bool :=
  if i < rs.size then pull p (atRow rs i) == atRow rs (atRow keys i) else true

private theorem from_edges (p : Perm) (rs keys : Array Nat)
    (length : keys.size = rs.size) (limit : rs.size ≤ 512)
    (covered : pack keys.toList = pack (List.range rs.size))
    (checked : block (edge p rs keys) 9 0 = true) : Preserves p rs := by
  have inRange (k : Nat) : k ∈ keys ↔ k < rs.size := by
    rw [← Array.mem_toList_iff,← bit_pack,covered,bit_pack,List.mem_range]
  have row {i : Nat} (hi : i < rs.size) : atRow rs i ∈ rs := by simp [atRow,hi]
  have index {i : Nat} (hi : i < rs.size) : atRow keys i < rs.size := by
    apply (inRange _).mp
    have hk : i < keys.size := length.symm ▸ hi
    simp [atRow,hk]
  have image {i : Nat} (hi : i < rs.size) : Agrees p (atRow rs i) (atRow rs (atRow keys i)) := by
    have h := block_sound 9 0 i (Nat.zero_le _) (by omega) checked
    have eq : pull p (atRow rs i) = atRow rs (atRow keys i) := by simpa [edge,hi] using h
    rw [← eq]
    exact pull_agrees _ _
  constructor
  · intro x hx
    obtain ⟨i,hi,hx⟩ := Array.mem_iff_getElem.mp hx
    have eq : atRow rs i = x := by simpa [atRow,hi] using hx
    exact ⟨_,row (index hi),eq ▸ image hi⟩
  · intro y hy
    obtain ⟨j,hj,hy⟩ := Array.mem_iff_getElem.mp hy
    obtain ⟨i,hi,hk⟩ := Array.mem_iff_getElem.mp ((inRange j).mpr hj)
    have hri : i < rs.size := length ▸ hi
    have hit : atRow rs (atRow keys i) = y := by simpa [atRow,hi,hk,hj] using hy
    exact ⟨_,row hri,hit ▸ image hri⟩

def basis (k : Fin 3) : Perm := stage0.permutations[k.val]!

private def positive0Keys : Array Nat := #[
  51,48,49,50,0,1,2,3,4,5,6,7,8,9,10,11,15,12,13,14,
  16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,
  39,36,37,38,40,41,42,43,47,44,45,46]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem positive0Preserved : Preserves (basis 0) positive := by
  apply from_edges _ _ positive0Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 4 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private def negative0Keys : Array Nat := #[
  342,343,0,344,345,1,346,347,2,348,3,349,4,5,6,350,7,8,351,352,
  353,354,9,355,10,356,11,357,12,358,13,359,14,360,15,16,361,17,362,18,
  363,19,20,364,21,365,22,23,24,366,25,26,27,28,29,30,367,31,32,368,
  33,369,34,35,36,37,370,38,39,371,372,40,373,374,41,375,42,376,377,43,
  44,378,45,46,379,47,48,380,49,50,51,52,53,54,55,56,57,58,381,59,
  382,60,61,62,63,383,64,65,66,67,68,384,385,69,386,387,70,388,71,72,
  389,73,390,74,391,392,75,76,393,77,78,79,80,81,82,83,84,85,86,87,
  394,88,89,90,395,91,92,396,93,94,95,96,97,98,99,100,101,102,103,104,
  105,106,107,108,109,110,397,398,111,399,400,112,401,113,114,115,116,117,118,119,
  402,120,121,403,122,123,124,404,125,405,126,406,127,128,129,407,130,131,132,133,
  134,135,408,136,137,138,409,139,410,140,411,141,412,142,143,413,144,145,146,147,
  148,149,414,150,151,152,415,153,416,154,417,155,156,157,158,418,159,160,161,162,
  163,164,165,419,166,420,167,168,169,421,170,171,422,172,173,423,174,175,176,177,
  178,179,424,180,181,425,182,426,183,184,185,186,427,187,188,189,190,191,192,193,
  194,428,195,196,429,197,430,198,199,200,201,202,203,204,205,431,206,207,432,208,
  209,433,210,211,434,212,213,214,215,216,217,218,435,219,220,221,222,223,224,225,
  436,226,227,437,228,229,230,231,232,233,234,438,235,236,439,237,238,239,440,240,
  241,242,441,442,443,243,444,244,245,246,247,248,445,249,250,446,251,447,252,253,
  254,255,256,448,257,449,258,259,260,450,261,451,262,452,263,264,265,266,267,268,
  269,270,453,271,454,272,455,273,456,274,457,275,276,277,278,279,280,458,281,459,
  282,460,283,284,285,461,286,287,288,289,290,462,291,292,293,294,295,296,297,298,
  299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,
  319,463,320,321,464,322,323,324,325,326,327,328,465,329,330,466,331,332,333,467,
  334,335,336,337,338,339,340,341]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem negative0Preserved : Preserves (basis 0) negative := by
  apply from_edges _ _ negative0Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 5 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private theorem basis0_sound : PlaneSymmetry (basis 0) := by
  refine ⟨by decide +kernel,?_,positive0Preserved,negative0Preserved⟩
  have bound : ∀ i : Fin 26, coord (basis 0) i.val < 26 := by decide +kernel
  exact fun i hi => bound ⟨i,hi⟩

private def positive1Keys : Array Nat := #[
  0,3,1,2,27,24,26,25,5,4,6,7,44,45,46,47,16,19,17,18,
  34,32,35,33,8,11,10,9,20,21,23,22,29,30,28,31,13,12,14,15,
  40,43,41,42,37,36,38,39,48,49,50,51]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem positive1Preserved : Preserves (basis 1) positive := by
  apply from_edges _ _ positive1Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 4 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private def negative1Keys : Array Nat := #[
  19,262,263,25,3,26,27,249,250,69,88,281,290,282,291,75,92,285,286,20,
  0,243,264,265,244,4,28,29,5,6,251,252,253,70,89,71,72,76,77,93,
  33,34,270,15,37,38,16,39,260,78,94,79,95,287,293,86,87,97,289,9,
  35,36,10,257,271,80,81,96,82,59,40,60,61,272,273,43,44,45,98,107,
  99,100,108,294,295,296,104,105,62,41,274,275,46,47,101,109,102,106,49,65,
  66,50,67,278,55,56,57,51,68,52,279,21,1,22,23,245,266,267,246,268,
  7,30,31,254,255,73,90,283,284,292,24,2,247,269,248,8,32,256,74,91,
  11,12,258,17,18,261,83,84,288,13,14,259,85,63,42,64,276,277,48,103,
  110,297,53,54,280,58,187,166,188,189,320,330,331,321,332,192,175,193,325,326,
  208,218,209,210,219,213,220,167,190,191,168,169,176,194,177,180,181,328,185,186,
  329,214,215,216,217,182,183,184,195,205,206,333,334,198,221,222,225,224,196,207,
  199,201,202,336,204,203,170,171,172,322,323,324,178,327,211,212,173,174,179,197,
  335,200,223,111,130,298,307,299,308,120,135,121,122,136,303,304,305,153,315,316,
  158,317,112,131,113,114,300,301,309,302,154,155,125,138,126,139,306,310,159,160,
  318,140,149,311,312,143,144,162,319,165,141,150,313,163,146,147,152,314,115,132,
  116,117,133,123,124,137,156,118,134,119,157,127,128,129,161,142,151,145,164,148,
  226,236,337,338,341,232,238,339,239,241,227,228,237,234,235,340,242,229,230,233,
  240,231,363,342,441,451,452,442,366,348,445,446,384,394,385,386,458,459,462,460,
  392,396,461,343,443,444,349,447,387,388,393,352,368,369,353,448,453,360,370,361,
  450,354,355,449,371,381,382,372,373,454,455,456,377,378,374,457,379,344,364,365,
  345,346,350,367,389,390,395,347,351,391,356,357,358,362,359,375,383,376,380,427,
  419,463,466,464,432,435,433,420,424,425,465,426,428,431,467,429,421,422,434,423,
  430,397,407,398,399,402,408,403,415,416,418,400,401,417,404,405,409,406,410,411,
  414,413,412,436,439,440,437,438]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem negative1Preserved : Preserves (basis 1) negative := by
  apply from_edges _ _ negative1Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 5 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private theorem basis1_sound : PlaneSymmetry (basis 1) := by
  refine ⟨by decide +kernel,?_,positive1Preserved,negative1Preserved⟩
  have bound : ∀ i : Fin 26, coord (basis 1) i.val < 26 := by decide +kernel
  exact fun i hi => bound ⟨i,hi⟩

private def positive2Keys : Array Nat := #[
  0,48,40,16,51,47,39,15,46,43,35,11,42,38,31,7,3,37,34,27,
  50,33,30,23,45,29,26,19,41,25,22,14,36,21,18,10,32,17,13,6,
  2,28,12,9,49,24,8,5,1,44,20,4]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem positive2Preserved : Preserves (basis 2) positive := by
  apply from_edges _ _ positive2Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 4 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private def negative2Keys : Array Nat := #[
  67,96,38,52,54,57,50,259,362,133,27,269,29,31,25,248,177,256,247,82,
  129,85,81,80,357,14,184,10,358,12,359,13,356,119,169,117,116,174,2,168,
  102,45,77,275,47,41,378,44,447,302,6,122,3,252,4,253,244,5,251,155,
  72,71,399,388,70,114,113,0,111,108,64,61,60,292,365,277,376,42,268,189,
  23,22,19,267,266,21,324,246,210,346,390,344,422,345,172,166,1,171,296,100,
  99,373,40,459,456,273,372,386,69,342,384,68,152,66,65,271,36,35,369,33,
  279,203,51,449,257,309,191,265,264,20,183,405,355,9,352,426,182,354,228,167,
  313,411,444,457,274,443,301,300,243,401,397,343,112,206,382,59,452,363,467,331,
  187,262,455,371,441,454,95,139,39,34,293,97,94,370,37,186,361,16,450,360,
  308,193,136,130,26,326,175,160,216,79,406,126,425,181,353,316,403,461,446,348,
  445,305,299,121,250,416,153,398,291,219,88,462,290,464,332,263,188,321,433,209,
  419,460,282,458,442,385,310,409,138,453,270,368,465,448,341,307,438,404,424,466,
  451,463,330,148,56,288,87,18,15,280,204,58,53,55,261,258,17,124,255,7,
  327,254,161,215,128,127,84,83,78,11,230,115,319,105,144,43,286,75,304,120,
  249,297,222,284,283,335,276,323,245,322,212,208,73,170,295,294,98,281,314,202,
  147,146,49,336,278,201,338,235,180,125,226,312,311,140,298,334,195,333,320,272,
  318,217,289,287,86,329,185,260,339,325,242,159,214,317,315,285,303,340,306,328,
  337,234,109,151,91,93,89,367,199,380,351,350,134,194,137,132,32,24,28,30,
  179,176,8,157,391,74,423,347,231,118,173,163,106,101,413,393,76,379,46,377,
  349,417,154,387,110,225,107,383,63,395,90,364,430,375,434,389,421,150,207,62,
  414,149,429,196,237,131,190,437,420,227,412,141,410,374,400,431,205,381,428,220,
  408,396,92,366,238,192,135,440,418,402,392,415,435,218,394,432,439,407,236,436,
  427,164,224,145,142,200,198,48,233,123,178,240,156,229,165,162,104,143,223,103,
  221,197,211,241,213,232,239,158]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem negative2Preserved : Preserves (basis 2) negative := by
  apply from_edges _ _ negative2Keys
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · iterate 5 (all_goals apply block_join)
    all_goals as_aux_lemma => decide +kernel

private theorem basis2_sound : PlaneSymmetry (basis 2) := by
  refine ⟨by decide +kernel,?_,positive2Preserved,negative2Preserved⟩
  have bound : ∀ i : Fin 26, coord (basis 2) i.val < 26 := by decide +kernel
  exact fun i hi => bound ⟨i,hi⟩


private theorem basis_sound (i : Fin 3) : PlaneSymmetry (basis i) := by
  have cases' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases' with rfl|rfl|rfl
  · exact basis0_sound
  · exact basis1_sound
  · exact basis2_sound

private def permId : Perm := Array.range 26

private theorem id_coord {i : Nat} (hi : i < 26) : coord permId i = i := by
  simp [coord,permId,hi]

private theorem id_preserves (rs : Array Nat) : Preserves permId rs := by
  have id (x : Nat) : Agrees permId x x := fun i hi => by rw [id_coord hi]
  exact ⟨fun x h => ⟨x,h,id x⟩,fun x h => ⟨x,h,id x⟩⟩

private theorem id_sound : PlaneSymmetry permId := by
  exact ⟨by decide +kernel,fun i hi => by rwa [id_coord hi],id_preserves _,id_preserves _⟩

private def comp (p q : Perm) := q.map (coord p)

private theorem comp_coord (p q : Perm) {i : Nat} (hi : i < q.size) :
    coord (comp p q) i = coord p (coord q i) := by
  simp [coord,comp,hi]

private theorem comp_agrees {p q : Perm} (qs : PlaneSymmetry q)
    {x y z : Nat} (xy : Agrees p x y) (yz : Agrees q y z) : Agrees (comp p q) x z := by
  intro i hi
  have small : i < q.size := qs.size.symm ▸ hi
  rw [comp_coord p q small,yz i hi,xy _ (qs.bound i hi)]

private theorem comp_preserves {p q : Perm} {rs : Array Nat} (qs : PlaneSymmetry q)
    (pRows : Preserves p rs) (qRows : Preserves q rs) : Preserves (comp p q) rs := by
  constructor
  · intro x hx
    obtain ⟨y,hy,xy⟩ := pRows.1 x hx
    obtain ⟨z,hz,yz⟩ := qRows.1 y hy
    exact ⟨z,hz,comp_agrees qs xy yz⟩
  · intro z hz
    obtain ⟨y,hy,yz⟩ := qRows.2 z hz
    obtain ⟨x,hx,xy⟩ := pRows.2 y hy
    exact ⟨x,hx,comp_agrees qs xy yz⟩

private theorem comp_sound {p q : Perm} (ps : PlaneSymmetry p) (qs : PlaneSymmetry q) :
    PlaneSymmetry (comp p q) := by
  refine ⟨by simpa [comp] using qs.size,?_,comp_preserves qs ps.positiveRows qs.positiveRows,
    comp_preserves qs ps.negativeRows qs.negativeRows⟩
  intro i hi
  rw [comp_coord p q (qs.size.symm ▸ hi)]
  exact ps.bound _ (qs.bound i hi)

private def imageCoord : List (Fin 3) → Nat → Nat
  | [], i => i
  | k :: ks, i => coord (basis k) (imageCoord ks i)

def wordPerm (ks : List (Fin 3)) : Perm := permId.map (imageCoord ks)

theorem word_sound (ks : List (Fin 3)) : PlaneSymmetry (wordPerm ks) := by
  induction ks with
  | nil =>
    have eq : wordPerm [] = permId := by simp [wordPerm,imageCoord]
    exact eq.symm ▸ id_sound
  | cons k ks ih =>
    have eq : wordPerm (k :: ks) = comp (basis k) (wordPerm ks) := by
      simp [wordPerm,comp,Array.map_map,Function.comp_def,imageCoord]
    exact eq.symm ▸ comp_sound (basis_sound k) ih

private def generatorWords : Array (Array (List (Fin 3))) := #[
  #[[0],[1],[2]],
  #[[0,1,1,0,1,0,1,2,1,2,1,0],[0,0,0,1,0,1,0,1,0],[0,0,1,0,1,2,1,2,1,0],[1,2,1,1,2,1,1],[1,0,0,0,1,0,1,0,1,0],[0,2,1,0,0,1,1,0,0,0,0]],
  #[[0,1,1,0,1,0,1,2,1,2,1,0],[0,0,0,1,0,1,0,1,0],[0,0,1,0,1,2,1,2,1,0],[1,2,1,1,2,1,1],[0,0,0,1,1,0,1,0,1,0,1]],
  #[[0,1,1,0,1,0,1,2,1,2,1,0],[0,0,0,1,0,1,0,1,0],[0,0,1,0,1,2,1,2,1,0],[1,2,1,1,2,1,1],[1,0,0,0,1,0,1,0,1,0],[0,2,1,0,0,1,1,0,0,0,0]],
  #[[0,1,1,0,1,0,1,2,1,2,1,0],[0,0,0,1,0,1,0,1,0],[0,0,1,0,1,2,1,2,1,0],[0,0,1,1,0,1,0,1,0,1,1],[2,0,1,2,1,2,1,0,0,1]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
private theorem generator_words (i : Fin 5) : (table i).permutations = (generatorWords[i.val]!).map wordPerm := by
  have cases' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases' with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem sound_generators (i : Fin 5) (p : Perm) (hp : p ∈ (table i).permutations) :
    PlaneSymmetry p ∧ (initial i).all (fun g => move p g == g) = true := by
  have fixed := (Bool.and_eq_true_iff.mp (checked_stages i)).2
  have mem : p ∈ (generatorWords[i.val]!).map wordPerm := by
    rw [← generator_words i]
    exact hp
  obtain ⟨w,_,rfl⟩ := Array.mem_map.mp mem
  exact ⟨word_sound w,Array.all_eq_true_iff_forall_mem.mp fixed _ hp⟩

end PEqualNP.Research.OrderThreePlanePrefixes
