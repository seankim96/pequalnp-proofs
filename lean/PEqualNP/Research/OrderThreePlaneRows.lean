import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Basic
import PEqualNP.Research.OrderThreePlanePrefixData

/-! The exact test families for L-meta-2625. Inputs 0 through 12 are points
and the other thirteen are lines. Each Boolean input is also represented
by a 26-bit mask, with its lowest bit corresponding to point zero. -/

namespace PEqualNP.Research.OrderThreePlanePrefixes

open OrderThreePlanePrefixData

def pack : List Nat → Nat
  | [] => 0
  | i :: is => (2^i) ||| pack is

theorem bit_pack (xs : List Nat) (i : Nat) : (pack xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [pack]
  | cons a xs ih =>
    simp only [pack,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr (eq_comm) Iff.rfl

def rowOf (f : Nat → Bool) : Nat := pack ((List.range 26).filter f)

theorem bit_rowOf (f : Nat → Bool) (i : Nat) (hi : i < 26) : (rowOf f).testBit i = f i := by
  apply Bool.eq_iff_iff.mpr
  simp [rowOf,bit_pack,hi]

def pull (p : Perm) (r : Nat) : Nat := rowOf fun i => r.testBit (p[i]?.getD i)

def differences : Finset (Fin 13) := {0,1,3,9}

def reps : List (Nat × Nat) := [(7,904),(13,2848),(19,708),(21,2720),
  (25,2656),(37,2440),(41,2370),(133,808)]

def deskRow (z : Nat × Nat) (m t : Fin 13) (dual : Bool) : Fin (13+13) → Bool :=
  let bit := fun (a b : Nat) (i : Fin 13) =>
    if dual = true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
  Fin.append (bit z.1 z.2) (bit z.2 z.1)

def asMask (f : Fin 26 → Bool) := rowOf fun i => if h : i < 26 then f ⟨i,h⟩ else false

theorem mask_input (f : Fin 26 → Bool) (i : Fin 26) : (asMask f).testBit i.val = f i := by
  simp [asMask,bit_rowOf, i.isLt]

def deskPositive : List Nat := (List.finRange 13).flatMap fun p =>
  ((List.finRange 13).filter fun w => decide (∃ d ∈ differences, p = w + d)).map fun w =>
    asMask (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w))

def rowBatch (z : Nat × Nat) : List Nat :=
  ([1,3,9] : List (Fin 13)).flatMap fun m => (List.finRange 13).flatMap fun t =>
    [asMask (deskRow z m t false),asMask (deskRow z m t true)]

def deskNegative : List Nat := reps.flatMap rowBatch

def atRow (rs : Array Nat) (i : Nat) := rs[i]?.getD 0

theorem key_cover (rs : Array Nat) (keys : List Nat)
    (eq : pack keys = pack (List.range rs.size)) (v : Nat) :
    v ∈ keys.map (atRow rs) ↔ v ∈ rs := by
  have hm (i : Nat) : i ∈ keys ↔ i < rs.size := by
    rw [← bit_pack,eq,bit_pack,List.mem_range]
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have bound := (hm i).mp hi
    simp [atRow,bound]
  · intro h
    obtain ⟨i,hi,he⟩ := Array.mem_iff_getElem.mp h
    exact List.mem_map.mpr ⟨i,(hm i).mpr hi,by simpa [atRow,hi] using he⟩

private def posKeys : List Nat := [0, 16, 40, 48, 1, 4, 20, 44, 5, 8, 24, 49, 2, 9, 12, 28, 6, 13, 17, 32, 10, 18, 21, 36, 14, 22, 25, 41, 19, 26, 29, 45, 23, 30, 33, 50, 3, 27, 34, 37, 7, 31, 38, 42, 11, 35, 43, 46, 15, 39, 47, 51]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem posBatch : deskPositive = posKeys.map (atRow positive) := by decide +kernel

private def negKeys0 : List Nat := [164, 441, 109, 463, 67, 337, 38, 239, 362, 162, 256, 107, 174, 65, 114, 37, 386, 17, 455, 8, 466, 2, 340, 0, 241, 342, 277, 75, 279, 392, 309, 389, 191, 375, 193, 276, 216, 274, 406, 264, 128, 190, 144, 188, 286, 181, 393, 126, 395, 125, 430, 120, 316, 195, 293, 198, 85, 44, 355, 250, 437, 282, 414, 287, 137, 80, 23, 354, 323, 400, 222, 407, 204, 132, 47, 21, 446, 170]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk0 : rowBatch (7,904) = negKeys0.map (atRow negative) := by decide +kernel

private def negKeys1 : List Nat := [318, 320, 224, 436, 151, 315, 96, 221, 57, 149, 31, 94, 359, 55, 253, 30, 172, 13, 401, 5, 460, 1, 334, 343, 439, 442, 110, 384, 467, 350, 248, 103, 68, 454, 341, 247, 169, 62, 39, 330, 242, 168, 399, 34, 18, 234, 165, 111, 459, 15, 351, 158, 275, 43, 461, 175, 160, 273, 271, 285, 391, 79, 405, 257, 237, 387, 383, 404, 124, 131, 189, 364, 335, 115, 105, 187, 186, 197]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk1 : rowBatch (13,2848) = negKeys1.map (atRow negative) := by decide +kernel

private def negKeys2 : List Nat := [150, 397, 95, 458, 56, 333, 367, 236, 259, 159, 177, 104, 117, 63, 388, 35, 456, 16, 331, 7, 438, 347, 317, 244, 223, 166, 259, 7, 150, 104, 331, 458, 177, 347, 95, 63, 438, 333, 117, 244, 56, 35, 317, 236, 388, 166, 367, 16, 223, 159, 456, 397, 95, 166, 259, 333, 388, 104, 438, 16, 150, 244, 367, 458, 117, 159, 331, 35, 223, 347, 56, 397, 177, 236, 456, 63, 317, 7]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk2 : rowBatch (19,708) = negKeys2.map (atRow negative) := by decide +kernel

private def negKeys3 : List Nat := [314, 298, 220, 432, 148, 311, 93, 218, 54, 146, 29, 92, 358, 53, 252, 28, 422, 12, 301, 4, 433, 345, 312, 243, 435, 419, 292, 73, 429, 377, 268, 283, 203, 374, 308, 266, 183, 196, 136, 263, 215, 182, 403, 130, 84, 180, 413, 121, 284, 78, 379, 402, 102, 40, 450, 325, 155, 99, 453, 260, 157, 71, 369, 448, 231, 154, 382, 368, 233, 118, 61, 363, 327, 229, 100, 59, 329, 178]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk3 : rowBatch (21,2720) = negKeys3.map (atRow negative) := by decide +kernel

private def negKeys4 : List Nat := [310, 226, 217, 415, 145, 294, 91, 205, 52, 138, 27, 86, 357, 48, 447, 24, 324, 10, 228, 3, 416, 344, 295, 443, 431, 321, 91, 344, 431, 48, 324, 294, 52, 443, 310, 24, 228, 205, 27, 321, 217, 10, 416, 138, 357, 226, 145, 3, 295, 86, 447, 415, 52, 3, 447, 321, 416, 294, 310, 86, 91, 10, 357, 443, 228, 415, 431, 138, 145, 24, 27, 344, 324, 226, 295, 205, 217, 48]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk4 : rowBatch (25,2656) = negKeys4.map (atRow negative) := by decide +kernel

private def negKeys5 : List Nat := [297, 281, 207, 428, 139, 307, 87, 214, 380, 143, 269, 90, 184, 51, 122, 26, 390, 11, 457, 349, 332, 246, 235, 167, 418, 398, 296, 98, 449, 445, 134, 74, 206, 381, 326, 322, 82, 41, 409, 270, 230, 227, 45, 19, 289, 185, 417, 153, 365, 352, 200, 123, 319, 272, 97, 213, 14, 50, 444, 251, 440, 385, 152, 306, 32, 89, 346, 356, 338, 112, 225, 427, 58, 142, 6, 25, 464, 171]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk5 : rowBatch (37,2440) = negKeys5.map (atRow negative) := by decide +kernel

private def negKeys6 : List Nat := [291, 208, 202, 410, 408, 290, 288, 201, 199, 135, 133, 83, 81, 46, 378, 22, 267, 9, 426, 348, 305, 245, 212, 420, 412, 299, 163, 371, 452, 254, 179, 101, 108, 451, 465, 173, 119, 60, 66, 328, 339, 113, 72, 33, 370, 232, 240, 69, 373, 360, 261, 156, 280, 249, 77, 209, 425, 278, 313, 76, 396, 353, 129, 300, 265, 394, 434, 127, 147, 20, 194, 421, 376, 140, 304, 192, 219, 42]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk6 : rowBatch (41,2370) = negKeys6.map (atRow negative) := by decide +kernel

private def negKeys7 : List Nat := [161, 262, 106, 424, 64, 303, 36, 211, 361, 141, 255, 88, 423, 49, 302, 366, 210, 258, 411, 176, 462, 116, 336, 70, 238, 372, 64, 70, 336, 366, 302, 211, 36, 372, 238, 258, 210, 141, 361, 262, 161, 176, 411, 88, 255, 424, 106, 116, 462, 49, 423, 303, 302, 49, 462, 176, 161, 372, 36, 303, 423, 88, 411, 258, 238, 70, 64, 424, 255, 141, 210, 366, 336, 116, 106, 262, 361, 211]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem chunk7 : rowBatch (133,808) = negKeys7.map (atRow negative) := by decide +kernel

private def negKeys := negKeys0 ++ negKeys1 ++ negKeys2 ++ negKeys3 ++ negKeys4 ++ negKeys5 ++ negKeys6 ++ negKeys7

private theorem negBatch : deskNegative = negKeys.map (atRow negative) := by
  simp only [deskNegative,reps,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    negKeys,List.map_append,chunk0,chunk1,chunk2,chunk3,chunk4,chunk5,chunk6,chunk7,List.append_assoc]

set_option maxRecDepth 8000 in
private theorem posCover : pack posKeys = pack (List.range positive.size) := by decide +kernel
set_option maxRecDepth 8000 in
private theorem negCover : pack negKeys = pack (List.range negative.size) := by decide +kernel

theorem exact_rows (r : Nat) :
    (r ∈ deskPositive ↔ r ∈ positive) ∧ (r ∈ deskNegative ↔ r ∈ negative) := by
  rw [posBatch,negBatch]
  exact ⟨key_cover _ _ posCover r, key_cover _ _ negCover r⟩

theorem row_counts : positive.size = 52 ∧ negative.size = 468 := by decide +kernel

set_option maxRecDepth 5000 in
theorem rows_distinct : positive.toList.Nodup ∧ negative.toList.Nodup := by
  have pos : positive.toList.IsChain (· < ·) := by decide +kernel
  have neg : negative.toList.IsChain (· < ·) := by decide +kernel
  exact ⟨(List.isChain_iff_pairwise.mp pos).nodup,(List.isChain_iff_pairwise.mp neg).nodup⟩


def columnsOk (rs : Array Nat) {n : Nat} (s : BitVec n) (i : Nat) :=
  (List.range rs.size).all fun k => s.getLsbD k == (rs[k]?.getD 0).testBit i

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem raw_correct : rawColumns.size = 26 ∧ (List.range 26).all (fun i =>
    let s := rawColumns[i]?.getD (0,0)
    columnsOk positive s.1 i && columnsOk negative s.2 i) = true := by decide +kernel

end PEqualNP.Research.OrderThreePlanePrefixes
