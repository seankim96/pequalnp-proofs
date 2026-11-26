import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.PlaneCase35FifthOrCut

def positive : Array Nat := #[
    8193, 8194, 8200, 8704, 16386, 16388, 16400, 17408, 32772, 32776, 32800, 34816, 65544, 65552,
    65600, 69632, 131073, 131088, 131104, 131200, 262146, 262176, 262208, 262400, 524292, 524352, 524416, 524800,
    1048584, 1048704, 1048832, 1049600, 2097168, 2097408, 2097664, 2099200, 4194336, 4194816, 4195328, 4198400, 8388609, 8388672,
    8389632, 8390656, 16777218, 16777344, 16779264, 16781312, 33554433, 33554436, 33554688, 33558528]

def negative : Array Nat := #[
    61888, 92576, 115585, 162112, 177472, 185152, 192832, 208132, 231170, 308368, 316033, 339076, 346753, 362113,
    377473, 408580, 416264, 462340, 470020, 555296, 570640, 601376, 608545, 616736, 623875, 670976, 678152, 686336,
    693506, 701696, 724226, 732416, 754946, 801808, 808969, 824337, 832528, 924680, 932864, 940040, 1079392, 1102401,
    1133089, 1194052, 1202752, 1210432, 1217090, 1233472, 1247750, 1325076, 1333761, 1348113, 1364481, 1378821, 1395201, 1448452,
    1456132, 1464832, 1509892, 1587248, 1595425, 1603616, 1609747, 1640483, 1656865, 1841169, 1849360, 1857537, 1871889, 2126048,
    2143424, 2150593, 2158784, 2172068, 2196611, 2241604, 2266178, 2274368, 2372740, 2379913, 2397313, 2405504, 2412673, 2425989,
    2434180, 2458753, 2495500, 2503684, 2641961, 2659331, 2688035, 2720771, 2757642, 2790402, 2888713, 2904073, 2921473, 3019784,
    3158116, 3166305, 3174496, 3182659, 3199041, 3211303, 3280966, 3289156, 3313730, 3674147, 3690529, 3706883, 3735587, 4221376,
    4235728, 4243905, 4252096, 4270468, 4278657, 4286848, 4292995, 4309377, 4335940, 4344136, 4352320, 4393222, 4401412, 4466836,
    4475017, 4524165, 4532356, 4540545, 4737289, 4751635, 4786435, 4802817, 4817155, 4851978, 4868360, 4917506, 4982809, 4999177,
    5253204, 5275731, 5310471, 5376070, 5384260, 5441542, 5507093, 5515284, 5572613, 5769235, 5799955, 5834755, 6031377, 6308041,
    6324419, 6340801, 6357127, 6389891, 6422606, 6553741, 6570121, 6619269, 7340103, 7372867, 7405575, 7471174, 8417696, 8434064,
    8442752, 8450432, 8462756, 8471456, 8479136, 8487810, 8504192, 8540936, 8557314, 8573696, 8585990, 8618754, 8663188, 8671880,
    8688272, 8695952, 8704640, 8786444, 8802824, 8925488, 8933672, 8941856, 8950034, 8958224, 9048330, 9064712, 9081090, 9449524,
    9474578, 9503270, 9572870, 9605634, 9634310, 9703956, 9711636, 9736720, 9835012, 9965618, 9973808, 9998354, 10498212, 10506408,
    10514592, 10551462, 10559652, 10620942, 10752140, 10760324, 10768520, 10883084, 11014186, 11030568, 11145226, 11538470, 11546660, 11599910,
    11669510, 12062754, 12591508, 12616082, 12624272, 12648838, 12657028, 12681602, 12714254, 12779782, 12845212, 12853396, 13107482, 13140242,
    13238538, 14680206, 14745734, 14811150, 14942348, 16819536, 16827201, 16852260, 16859937, 16877313, 16892673, 16917828, 16925512, 16942912,
    16950592, 16958272, 16975620, 16983300, 17008384, 17073681, 17106437, 17139201, 17171980, 17237508, 17311024, 17318185, 17335569, 17343760,
    17368353, 17376544, 17383713, 17401089, 17564697, 17597457, 17834100, 17842785, 17859153, 17875521, 17891877, 17908257, 18088469, 18121233,
    18153989, 18883684, 18890857, 18940965, 18949156, 19006540, 19014724, 19137549, 19203077, 19268620, 19399721, 19415081, 19465249, 19661833,
    19923045, 19931236, 19939425, 19988517, 20980052, 20988233, 21004625, 21012816, 21020993, 21102924, 21111108, 21119304, 21233693, 21496089,
    21512457, 21528849, 21757977, 22020181, 22028372, 22052945, 22282261, 23068749, 23085129, 23199820, 23330829, 24117317, 25174324, 25183016,
    25232164, 25239844, 25248544, 25297676, 25314056, 25363204, 25428508, 25559564, 25690424, 25698608, 25706792, 26214964, 26222644, 26280484,
    26477076, 29360412, 29368596, 29491468, 29622300, 29884696, 33581280, 33596624, 33631392, 33639072, 33646752, 33654402, 33704520, 33719874,
    33754626, 33785346, 33827984, 33835656, 33851024, 33858704, 33885824, 33893504, 33901184, 33916544, 33951240, 33966600, 34016768, 34090032,
    34147362, 34155552, 34212874, 34278402, 34343960, 34352144, 34475016, 34613360, 34622048, 34629728, 34636370, 34671138, 34687520, 34736706,
    34753088, 34767426, 34802178, 35129394, 35137584, 35194914, 35661024, 35668200, 35676384, 35685570, 35693760, 35718306, 35726496, 35751042,
    35783754, 35816514, 36176938, 36242466, 36307978, 37759184, 37767368, 37775552, 37781714, 37789904, 37881930, 37898312, 38013080, 38021264,
    38029448, 38275098, 38406154, 38537240, 38799442, 38807632, 38830162, 38930498, 39323666, 39846090, 39862472, 39878850, 39977034, 41960104,
    41976466, 42009250, 42025632, 42041986, 42205848, 42222216, 42238608, 42467386, 42992178, 43024914, 43057698, 43515954, 44040362, 44056744,
    44105890, 44564522, 46137498, 46170258, 46399640, 46661658, 48234634, 50340976, 50348648, 50366032, 50373712, 50464328, 50479688, 50497088,
    50595352, 50628112, 50726408, 50857016, 50865200, 51119128, 51380848, 51388528, 51397216, 51413584, 52429928, 52438112, 52445288, 52560968,
    52954152, 58720824, 58737192, 58982936, 59244600, 59769392]

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) := s ++ [fun r => wire s g.1 r || wire s g.2 r]
abbrev Gate := Bool × Nat × Nat
def step (s : List Column) (g : Gate) : List Column :=
  if g.1 then s ++ [both (wire s g.2.1) (wire s g.2.2)] else addOr s g.2

def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 ||| b 1) <<< 26) ||| ((b 3 ||| b 9) <<< 27)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def mix (op : Bool) (a b : Column) : Column := fun r =>
  if op then a r && b r else a r || b r
def base (i : Fin 30) : Column :=
  if i.val < 28 then input i.val
  else if i.val = 28 then mix true (input 15) (input 27)
  else mix true (input 17) (input 26)

private def negatives : Array (Fin 468) := #[421, 270, 41, 158, 135]
private def positives : Array (Array (Fin 52)) := #[
  #[1, 4, 10, 12, 13, 14, 15, 18, 21, 26, 29, 34, 36, 42, 43, 44, 48, 49, 50],
  #[2, 7, 9, 12, 17, 21, 23, 24, 25, 27, 28, 32, 38, 42, 44, 45, 46, 47, 48],
  #[0, 4, 6, 8, 10, 11, 15, 16, 22, 25, 28, 29, 30, 31, 34, 39, 41, 47, 51],
  #[1, 4, 8, 14, 16, 18, 19, 20, 25, 28, 32, 33, 34, 35, 38, 39, 41, 44, 49],
  #[1, 4, 11, 12, 16, 17, 20, 24, 25, 26, 27, 28, 35, 36, 38, 39, 43, 46, 50]]
private def choices : Array (Fin 5) := #[1, 0, 3, 1, 1, 0, 2, 0, 4, 0, 1, 4, 2, 0, 2, 2, 0, 3, 1, 1, 2, 3, 3, 0, 1, 0, 0, 0, 0, 0]
private def negRow (t : Fin 5) := 52 + (negatives[t.val]!).val
private def flag (t : Fin 5) (i : Fin 19) : Fin 52 := positives[t.val]![i.val]!
variable (t : Fin 5)
private def supp (x : Column) : Finset (Fin 19) :=
  if x (negRow t) then ∅ else Finset.univ.filter (fun i => x (flag t i).val)
private def Count (s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp t (s.getD j (fun _ => false)))).card ≤ q + W.card

private theorem cutOr (x y : Column) : supp t (mix false x y) ⊆ supp t x ∪ supp t y := by
  cases hx : x (negRow t) <;> cases hy : y (negRow t) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp t (mix true x y) ⊆ supp t (if x (negRow t) then y else x) := by
  cases hx : x (negRow t) <;> cases hy : y (negRow t) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Column} {q c : Nat} (h : Count t s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp t v ⊆ parents.biUnion (fun j => supp t (s.getD j (fun _ => false)))) : Count t (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp t ((s ++ [v]).getD j (fun _ => false))) ⊆
        U.biUnion (fun j => supp t (s.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp t v := by simpa using hij
        obtain ⟨a,ha,hai⟩ := Finset.mem_biUnion.mp (sub hv)
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_right _ ha,hai⟩
      · have hd : (s ++ [v]).getD j (fun _ => false) = s.getD j (fun _ => false) := by
          by_cases hj : j < s.length
          · exact List.getD_append _ _ _ _ hj
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩),hd ▸ hij⟩
    have hc := Finset.card_union_le (W.erase s.length) parents
    rw [Finset.card_erase_of_mem incl] at hc
    have hw := Finset.card_pos.mpr ⟨_,incl⟩
    have hU := h U
    have := Finset.card_le_card hs
    change U.card ≤ _ at hc
    omega
  · have eq : W.biUnion (fun j => supp t ((s ++ [v]).getD j (fun _ => false))) =
        W.biUnion (fun j => supp t (s.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega


private theorem appendGate {s : List Column} {q : Nat} (h : Count t s q) (op : Bool) (i j : Nat) :
    Count t (s ++ [mix op (wire s i) (wire s j)]) (q+(!op).toNat) := by
  cases op
  · apply grow t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
    simpa [wire] using cutOr t (wire s i) (wire s j)
  · let k := if wire s i (negRow t) then j else i
    apply grow t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd t (wire s i) (wire s j)
    change _ ⊆ supp t (wire s k)
    cases e : wire s i (negRow t) <;> simpa only [k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) {s : List Column} {q : Nat} (h : Count t s q) :
    Count t (gs.foldl step s) (q+gs.countP (fun g => !g.1)) := by
  induction gs generalizing s q with
  | nil => simpa using h
  | cons g gs ih =>
    obtain ⟨op,i,j⟩ := g
    have next := appendGate t h op i j
    have eq : step s (op,i,j) = s ++ [mix op (wire s i) (wire s j)] := by cases op <;> rfl
    simp only [List.foldl_cons,eq]
    cases op <;> simpa [List.countP_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih next

private theorem addConst {s : List Column} {q : Nat} (h : Count t s q) (b : Bool) :
    Count t (s ++ [fun _ => b]) q := by
  have empty : supp t (fun _ => b) = ∅ := by cases b <;> simp [supp]
  exact grow t (c := 0) h _ ∅ (by simp) (by simp [empty])
private theorem baseSmall : ∀ k : Fin 5, ∀ i : Fin 30, (supp k (base i)).card ≤ 1 := by
  decide +kernel
private theorem chosen : ∀ i : Fin 30, i.val ≠ 13 →
    let k := choices[i.val]!
    base i (negRow k) = true ∨ ∀ f : Fin 19, base i (flag k f).val = false := by
  decide +kernel

private theorem orSmall (x y : Column)
    (hx : x (negRow t) = true ∨ ∀ f : Fin 19, x (flag t f).val = false)
    (hy : (supp t y).card ≤ 1) : (supp t (mix false x y)).card ≤ 1 := by
  rcases hx with h | h
  · simp [supp,mix,h]
  · apply le_trans (Finset.card_le_card (show supp t (mix false x y) ⊆ supp t y from ?_)) hy
    cases he : x (negRow t) <;> cases hf : y (negRow t) <;>
      simp [supp,mix,he,hf,Finset.subset_iff,h]

private theorem slice (op : Bool) (a b : Fin 30) :
    ∃ k : Fin 5, (supp k (mix op (base a) (base b))).card ≤ 1 := by
  cases op
  · by_cases ha : a.val = 13
    · by_cases hb : b.val = 13
      · have he : a = b := Fin.ext (ha.trans hb.symm)
        subst b
        have same : mix false (base a) (base a) = base a := by
          funext r; exact Bool.or_self ..
        exact ⟨0, by rw [same]; exact baseSmall 0 a⟩
      · refine ⟨choices[b.val]!,?_⟩
        rw [show mix false (base a) (base b) = mix false (base b) (base a) by
          funext r; exact Bool.or_comm ..]
        exact orSmall _ _ _ (chosen b hb) (baseSmall _ a)
    · exact ⟨_,orSmall _ _ _ (chosen a (by omega)) (baseSmall _ b)⟩
  · refine ⟨0,le_trans (Finset.card_le_card (cutAnd 0 _ _)) ?_⟩
    split <;> apply baseSmall

private theorem start : Count t (List.ofFn base) 0 := by
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < 30
  · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
    apply baseSmall
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
    simp [supp]

private theorem addSmall {s : List Column} (h : Count t s 0) (v : Column)
    (hv : (supp t v).card ≤ 1) : Count t (s ++ [v]) 0 := by
  have small (i : Nat) : (supp t (wire s i)).card ≤ 1 := by
    simpa [wire] using h {i}
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i < s.length
  · rw [List.getD_append _ _ _ _ hi]; exact small i
  · by_cases he : i = s.length
    · subst i; simpa using hv
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [supp]

end PEqualNP.Research.PlaneCase35FifthOrCut
open PEqualNP.Research.PlaneCase35FifthOrCut in
theorem PEqualNP.Research.PlaneCase35FifthOrCut : ∀ (op : Bool) (a b : Fin 30) (gs : List Gate) (o : Nat),
    let e := mix op (base a) (base b)
    let pool := List.ofFn base ++ [e,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    18 ≤ gs.countP (fun g => !g.1) := by
  intro op a b gs o e pool hp hn
  obtain ⟨k,hk⟩ := slice op a b
  have init : Count k pool 0 := by
    simpa [pool,e,List.append_assoc] using
      addConst k (addConst k (addSmall k (start k) _ hk) false) true
  have cost := run k gs init {o}
  have full : supp k (wire (gs.foldl step pool) o) = Finset.univ := by
    have nh : wire (gs.foldl step pool) o (negRow k) = false := hn (negatives[k.val]!)
    simp only [supp,nh,Bool.false_eq_true,ite_false]
    exact Finset.filter_true_of_mem (fun i _ => hp (flag k i))
  simp only [Finset.singleton_biUnion,Finset.card_singleton] at cost
  change (supp k (wire _ o)).card ≤ _ at cost
  rw [full] at cost
  simp only [Finset.card_univ,Fintype.card_fin] at cost
  omega
