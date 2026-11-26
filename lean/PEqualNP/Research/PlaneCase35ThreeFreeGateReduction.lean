import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction
abbrev Term := Finset (Fin 6)
abbrev Form := List Term

def atom (i : Fin 6) : Form := [{i}]
def combine (op : Bool) (x y : Form) : Form :=
  if op then x.flatMap (fun m => y.map (fun n => m ∪ n)) else x ++ y
def choose (k : Fin 3) (fresh x y : Form) : Form :=
  if k = 0 then fresh else if k = 1 then x else y
def pick (k : Fin 3) (fresh x y : Bool) : Bool :=
  if k = 0 then fresh else if k = 1 then x else y
def gate (op x y : Bool) : Bool := if op then x && y else x || y
def eval (v : Term) (xs : Form) : Bool := xs.any fun t => decide (t ⊆ v)

private theorem count : ∀ (a b c l r : Bool) (i j : Fin 3),
    let x := combine a (atom 0) (atom 1)
    let y := combine b (if l then x else atom 2) (if r then x else atom 3)
    let z := combine c (choose i (atom 4) x y) (choose j (atom 5) x y)
    ((x ++ y ++ z).eraseDups.filter (fun t => 1 < t.card)).length ≤ 4 := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 0 in
  decide +kernel

private theorem evalAtom (v : Term) (i : Fin 6) : eval v (atom i) = decide (i ∈ v) := by
  simp [eval, atom]

private theorem evalCombine (v : Term) (op : Bool) (x y : Form) :
    eval v (combine op x y) = gate op (eval v x) (eval v y) := by
  cases op
  · simp [eval,combine,gate]
  · apply Bool.eq_iff_iff.mpr
    simp [eval,combine,gate,List.any_eq_true,Finset.union_subset_iff]
    aesop

private theorem evalChoose (v : Term) (k : Fin 3) (f x y : Form) :
    eval v (choose k f x y) = pick k (eval v f) (eval v x) (eval v y) := by
  unfold choose pick
  by_cases h : k = 0 <;> by_cases g : k = 1 <;> simp [h,g]

end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction
open PEqualNP.Research.PlaneCase35ThreeFreeGateReduction in
theorem PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.normalForm : ∀ (op₁ op₂ op₃ useLeft useRight : Bool) (left right : Fin 3),
    let x := combine op₁ (atom 0) (atom 1)
    let y := combine op₂ (if useLeft then x else atom 2) (if useRight then x else atom 3)
    let z := combine op₃ (choose left (atom 4) x y) (choose right (atom 5) x y)
    ((x ++ y ++ z).eraseDups.filter (fun t => 1 < t.card)).length ≤ 4 ∧
    ∀ v : Finset (Fin 6),
      let b (i : Fin 6) := decide (i ∈ v)
      let u := gate op₁ (b 0) (b 1)
      let w := gate op₂ (if useLeft then u else b 2) (if useRight then u else b 3)
      eval v x = u ∧ eval v y = w ∧
        eval v z = gate op₃ (pick left (b 4) u w) (pick right (b 5) u w) := by
  intro a b c l r i j x y z
  refine ⟨count a b c l r i j, ?_⟩
  intro v bit u w
  have hx : eval v x = u := by simp [x,u,bit,evalCombine,evalAtom]
  have hy : eval v y = w := by cases l <;> cases r <;> simp [y,w,bit,evalCombine,evalAtom,hx]
  exact ⟨hx,hy,by simp [z,evalCombine,evalChoose,evalAtom,hx,hy,bit]⟩

namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction

private abbrev Basis (rows : Nat → Term) (high : Fin 52 → Prop) :=
  ∀ a b : Fin 6, (∀ r, a ∈ rows r → b ∈ rows r) ∨
    (∀ r, b ∈ rows r → a ∈ rows r) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, high p → a ∈ rows p.val → b ∈ rows p.val → p = q

private theorem termShape {rows : Nat → Term} {high : Fin 52 → Prop}
    (basis : Basis rows high) (t : Term) :
    (∀ r, t ⊆ rows r) ∨ (∃ a : Fin 6, ∀ r, t ⊆ rows r ↔ a ∈ rows r) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, high p → t ⊆ rows p.val → p = q := by
  induction t using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert a t _ ih =>
    rcases ih with all | ⟨b,hb⟩ | ⟨q,hq⟩
    · exact Or.inr (Or.inl ⟨a,fun r => by simp [Finset.insert_subset_iff,all r]⟩)
    · rcases basis a b with ab | ba | ⟨q,hq⟩
      · refine Or.inr (Or.inl ⟨a,?_⟩)
        intro r; rw [Finset.insert_subset_iff,hb]
        exact ⟨And.left,fun h => ⟨h,ab r h⟩⟩
      · refine Or.inr (Or.inl ⟨b,?_⟩)
        intro r; rw [Finset.insert_subset_iff,hb]
        exact ⟨And.right,fun h => ⟨ba r h,h⟩⟩
      · refine Or.inr (Or.inr ⟨q,?_⟩)
        intro p hp h
        obtain ⟨ha,ht⟩ := Finset.insert_subset_iff.mp h
        exact hq p hp ha ((hb _).mp ht)
    · exact Or.inr (Or.inr ⟨q,fun p hp h => hq p hp (Finset.insert_subset_iff.mp h).2⟩)

private abbrev Pass (rows : Nat → Term) (p i j : Nat) (t : Term) :=
  t ⊆ rows p → t ⊆ rows i ∨ t ⊆ rows j
private abbrev Raw (rows : Nat → Term) (p i j : Nat) :=
  ∀ a ∈ rows p, a ∈ rows i ∨ a ∈ rows j
private theorem safeTerm {rows : Nat → Term} {high : Fin 52 → Prop}
    (basis : Basis rows high) (t : Term) :
    ∃ q : Fin 52, ∀ (p : Fin 52) (i j : Nat), high p → p ≠ q →
      Raw rows p.val i j → Pass rows p.val i j t := by
  rcases termShape basis t with all | ⟨a,one⟩ | ⟨q,single⟩
  · exact ⟨0,fun _ i _ _ _ _ _ => Or.inl (all i)⟩
  · exact ⟨0,fun p i j _ _ raw h => (raw a ((one _).mp h)).imp (one i).mpr (one j).mpr⟩
  · exact ⟨q,fun p _ _ hp ne _ h => False.elim (ne (single p hp h))⟩

end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction
open PEqualNP.Research.PlaneCase35ThreeFreeGateReduction in
theorem PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.trace : ∀ (rows : Nat → Finset (Fin 6)) (high : Fin 52 → Prop),
    (∀ a b : Fin 6, (∀ r, a ∈ rows r → b ∈ rows r) ∨
      (∀ r, b ∈ rows r → a ∈ rows r) ∨
      ∃ q : Fin 52, ∀ p : Fin 52, high p → a ∈ rows p.val → b ∈ rows p.val → p = q) →
    ∀ (a b c l r : Bool) (j k : Fin 3),
    let bit (i : Fin 6) (v : Nat) := decide (i ∈ rows v)
    let x (v : Nat) := gate a (bit 0 v) (bit 1 v)
    let y (v : Nat) := gate b (if l then x v else bit 2 v) (if r then x v else bit 3 v)
    let z (v : Nat) := gate c (pick j (bit 4 v) (x v) (y v)) (pick k (bit 5 v) (x v) (y v))
    ∃ S : Finset (Fin 52), S.card ≤ 4 ∧ ∀ (p : Fin 52) (i j : Nat), high p → p ∉ S →
      (∀ t ∈ rows p.val, t ∈ rows i ∨ t ∈ rows j) →
      ∀ w ∈ [x,y,z], w p.val = true → w i = true ∨ w j = true := by
  classical
  intro rows high basis a b c l r j k bit x y z
  let X := combine a (atom 0) (atom 1)
  let Y := combine b (if l then X else atom 2) (if r then X else atom 3)
  let Z := combine c (choose j (atom 4) X Y) (choose k (atom 5) X Y)
  obtain ⟨bound,sem⟩ := normalForm a b c l r j k
  let allTerms := X ++ Y ++ Z
  let hard := allTerms.eraseDups.filter (fun t => 1 < t.card)
  choose exception works using safeTerm (rows := rows) (high := high) basis
  let S := hard.toFinset.image exception
  refine ⟨S, Finset.card_image_le.trans ((List.toFinset_card_le (l := hard)).trans bound), ?_⟩
  intro p i j hp clear raw
  have onePass (t : Term) (ht : t ∈ allTerms) : Pass rows p.val i j t := by
    by_cases many : 1 < t.card
    · have mem : t ∈ hard.toFinset := by simpa [hard, many] using ht
      exact works t p i j hp (fun eq => clear (eq ▸ Finset.mem_image_of_mem exception mem)) raw
    · by_cases none : t.card = 0
      · have := Finset.card_eq_zero.mp none
        simp [Pass, this]
      · obtain ⟨u,rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
        simpa [Pass] using raw u
  have sweep (f : Form) (inside : ∀ t ∈ f, t ∈ allTerms) :
      eval (rows p.val) f = true → eval (rows i) f = true ∨ eval (rows j) f = true := by
    simp only [eval,List.any_eq_true,decide_eq_true_eq]
    rintro ⟨t,ht,hit⟩
    exact (onePass t (inside t ht) hit).imp (fun h => ⟨t,ht,h⟩) (fun h => ⟨t,ht,h⟩)
  have ex (v : Nat) : eval (rows v) X = x v := (sem (rows v)).1
  have ey (v : Nat) : eval (rows v) Y = y v := (sem (rows v)).2.1
  have ez (v : Nat) : eval (rows v) Z = z v := (sem (rows v)).2.2
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  · simpa only [ex] using sweep X (by intro t ht; simp [allTerms,ht])
  · simpa only [ey] using sweep Y (by intro t ht; simp [allTerms,ht])
  · simpa only [ez] using sweep Z (by intro t ht; simp [allTerms,ht])

namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base

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

private def words : Array Nat := #[282574488403969, 17592187093010, 562949970198816, 268440068, 4295106624, 68721837056, 2199061020672, 35184976592896, 1125909578907648, 154753040392, 4675071901824, 79199196940288, 2393087057887232, 15, 240, 3840, 61440, 983040, 15728640, 251658240, 4026531840, 64424509440, 1030792151040, 16492674416640, 263882790666240, 4222124650659840, 300166675496979, 155021480460, 512, 65536]
private def w (a : Fin 30) := words[a.val]!
private theorem posBits : ∀ (a : Fin 30) (p : Fin 52), base a p.val = (w a).testBit p.val := by decide +kernel
private def sub (a b : Fin 30) := a = b ∨
  (b = 26 ∧ (a = 0 ∨ a = 1)) ∨ (b = 27 ∧ (a = 3 ∨ a = 9)) ∨
  (a = 28 ∧ (b = 15 ∨ b = 27)) ∨ (a = 29 ∧ (b = 17 ∨ b = 26))
private theorem wordOr (x : Nat) :
    (extend x).testBit 26 = (x.testBit 26 || (extend x).testBit 0 || (extend x).testBit 1) ∧
    (extend x).testBit 27 = (x.testBit 27 || (extend x).testBit 3 || (extend x).testBit 9) := by
  have hi (v : Nat) : (v%2).testBit 1 = false := by
    have cases : v%2=0 ∨ v%2=1 := by omega
    rcases cases with h|h <;> rw [h] <;> decide
  simp [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_assoc,hi]
private theorem lower (a b : Fin 30) (h : sub a b) (r : Nat) : base a r = true → base b r = true := by
  rcases h with e | ⟨eb,ea|ea⟩ | ⟨eb,ea|ea⟩ | ⟨ea,eb|eb⟩ | ⟨ea,eb|eb⟩
  · simp [e]
  all_goals subst a; subst b
  · change input 0 r = true → input 26 r = true
    by_cases hr : r < 52 <;> simp only [input,hr,ite_true,ite_false,pos,neg]
    all_goals rw [(wordOr _).1]; grind
  · change input 1 r = true → input 26 r = true
    by_cases hr : r < 52 <;> simp only [input,hr,ite_true,ite_false,pos,neg]
    all_goals rw [(wordOr _).1]; grind
  · change input 3 r = true → input 27 r = true
    by_cases hr : r < 52 <;> simp only [input,hr,ite_true,ite_false,pos,neg]
    all_goals rw [(wordOr _).2]; grind
  · change input 9 r = true → input 27 r = true
    by_cases hr : r < 52 <;> simp only [input,hr,ite_true,ite_false,pos,neg]
    all_goals rw [(wordOr _).2]; grind
  · change (input 15 r && input 27 r) = true → input 15 r = true
    simp_all
  · change (input 15 r && input 27 r) = true → input 27 r = true
    simp_all
  · change (input 17 r && input 26 r) = true → input 17 r = true
    simp_all
  · change (input 17 r && input 26 r) = true → input 26 r = true
    simp_all

private def idx (a b : Fin 30) : Fin 52 := Fin.ofNat 52 (Nat.log2 (w a &&& w b))
private theorem codes : ∀ a b : Fin 30, ¬ sub a b → ¬ sub b a →
    let z := w a &&& w b
    z = 0 ∨ z = 2^(idx a b).val ∨ z = 3 ∨ z = 12 := by
  unfold sub
  decide +kernel
end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base
open PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base in
theorem PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base : ∀ a b : Fin 30,
    let x := mix true (base a) (base b)
    (∀ r : Nat, x r = base a r) ∨ (∀ r : Nat, x r = base b r) ∨
    (∃ f : Fin 52, ∀ p : Fin 52, x p.val = true → p = f) ∨
    (∀ p : Fin 52, x p.val = true → p.val = 0 ∨ p.val = 1) ∨
    (∀ p : Fin 52, x p.val = true → p.val = 2 ∨ p.val = 3) := by
  intro a b x
  by_cases ha : sub a b
  · left; intro r
    cases e : base a r <;> simp [x,mix,e,lower a b ha r]
  by_cases hb : sub b a
  · right; left; intro r
    cases e : base b r <;> simp [x,mix,e,lower b a hb r]
  have on (p : Fin 52) : x p.val = (w a &&& w b).testBit p.val := by
    simp [x,mix,posBits,Nat.testBit_and]
  rcases codes a b ha hb with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl ⟨0,by intro p; simp [on,h]⟩))
  · right; right; left; refine ⟨idx a b,?_⟩; intro p hp
    apply Fin.ext; symm; simpa [on,h,Nat.testBit_two_pow] using hp
  · right; right; right; left
    have bits : ∀ p : Fin 52, (3:Nat).testBit p.val = true → p.val = 0 ∨ p.val = 1 := by decide
    simpa only [on,h] using bits
  · right; right; right; right
    have bits : ∀ p : Fin 52, (12:Nat).testBit p.val = true → p.val = 2 ∨ p.val = 3 := by decide
    simpa only [on,h] using bits


namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction
open Base
def fixed (swap : Bool) (k : Fin 32) : Column :=
  if h : k.val < 30 then base ⟨k.val,h⟩
  else if (k.val = 30) = (swap = false) then mix true (input 13) (input 26)
  else mix true (input 13) (input 27)

private theorem inactive : ∀ (sw : Bool) (k : Fin 32) (p : Fin 52),
    30 ≤ k.val → 4 ≤ p.val → fixed sw k p.val = false := by decide +kernel

private theorem pairBasis (sw : Bool) (a b : Fin 32) :
    (∀ r, fixed sw a r = true → fixed sw b r = true) ∨
    (∀ r, fixed sw b r = true → fixed sw a r = true) ∨
    ∃ q : Fin 52, ∀ p : Fin 52, 4 ≤ p.val →
      fixed sw a p.val = true → fixed sw b p.val = true → p = q := by
  by_cases ha : a.val < 30
  · by_cases hb : b.val < 30
    · let u : Fin 30 := ⟨a.val,ha⟩
      let v : Fin 30 := ⟨b.val,hb⟩
      have ea : fixed sw a = base u := by simp [fixed,ha,u]
      have eb : fixed sw b = base v := by simp [fixed,hb,v]
      rw [ea,eb]
      rcases Base u v with h | h | ⟨q,h⟩ | h | h
      · left; intro r hit; simpa [mix,hit] using h r
      · right; left; intro r hit; simpa [mix,hit] using h r
      · exact Or.inr (Or.inr ⟨q,fun p _ h₁ h₂ => h p (by simp [mix,h₁,h₂])⟩)
      all_goals
        refine Or.inr (Or.inr ⟨0,?_⟩)
        intro p hp h₁ h₂
        have h₃ := h p (by simp [mix,h₁,h₂])
        omega
    · exact Or.inr (Or.inr ⟨0,fun p hp _ hit => by simp [inactive sw b p (by omega) hp] at hit⟩)
  · exact Or.inr (Or.inr ⟨0,fun p hp hit _ => by simp [inactive sw a p (by omega) hp] at hit⟩)

end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction
open PEqualNP.Research.PlaneCase35ThreeFreeGateReduction PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base in
theorem PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.exceptions : ∀ (sw : Bool) (src : Fin 6 → Fin 32) (a b c l r : Bool) (j k : Fin 3),
    let f (i : Fin 6) := fixed sw (src i)
    let x (v : Nat) := gate a (f 0 v) (f 1 v)
    let y (v : Nat) := gate b (if l then x v else f 2 v) (if r then x v else f 3 v)
    let z (v : Nat) := gate c (pick j (f 4 v) (x v) (y v)) (pick k (f 5 v) (x v) (y v))
    ∃ S : Finset (Fin 52), S.card ≤ 4 ∧ ∀ (p : Fin 52) (i j : Fin 468),
      4 ≤ p.val → p ∉ S →
      (∀ t : Fin 30, base t p.val = true → base t (52+i.val) = true ∨ base t (52+j.val) = true) →
      ∀ w ∈ [x,y,z], w p.val = true → w (52+i.val) = true ∨ w (52+j.val) = true := by
  intro sw src a b c l r j k f x y z
  let rows (v : Nat) : Finset (Fin 6) := Finset.univ.filter (fun t => f t v = true)
  have mem (v : Nat) (t : Fin 6) : t ∈ rows v ↔ f t v = true := by simp [rows]
  have basis : Basis rows (fun p => 4 ≤ p.val) := by
    intro u v
    simpa only [mem,f] using pairBasis sw (src u) (src v)
  obtain ⟨S,size,valid⟩ := trace rows (fun p => 4 ≤ p.val) basis a b c l r j k
  refine ⟨S,size,?_⟩
  intro p i j hp miss raw
  have transfer : Raw rows p.val (52+i.val) (52+j.val) := by
    intro u hit
    have on := (mem _ u).mp hit
    change fixed sw (src u) p.val = true at on
    by_cases hu : (src u).val < 30
    · have e : fixed sw (src u) = base ⟨(src u).val,hu⟩ := by simp [fixed,hu]
      rw [e] at on
      simpa only [mem,f,e] using raw _ on
    · simp [inactive sw (src u) p (by omega) hp] at on
  simpa only [mem,decide_eq_true_eq, Bool.decide_eq_true, x,y,z] using valid p (52+i.val) (52+j.val) hp miss transfer

namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndSeparation

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) : List Column :=
  s ++ [fun r => wire s g.1 r || wire s g.2 r]
def good (p a b : Nat) (w : Column) := w p = true → w a = true ∨ w b = true

def separated (s : List Column) :=
  ∃ n : Fin 257 → Fin 468, ∀ i j : Fin 257, i.val < j.val →
    ∃ p : Fin 52, ∀ w ∈ s, good p.val (52 + (n i).val) (52 + (n j).val) w

end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndSeparation


namespace PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndBudget
open PlaneFirstAndSeparation
abbrev Gate := Bool × Nat × Nat
def step (s : List Column) (g : Gate) : List Column :=
  if g.1 then s ++ [both (wire s g.2.1) (wire s g.2.2)] else addOr s g.2

private def trace (s : List Column) (r : Nat) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let tail := trace (step s g) r gs
    if g.1 then 2 * tail + (wire s g.2.1 r).toNat else tail

private theorem trace_lt (s : List Column) (r : Nat) (gs : List Gate) :
    trace s r gs < 2 ^ (gs.countP Prod.fst) := by
  induction gs generalizing s with
  | nil => simp [trace]
  | cons g gs ih =>
    have h := ih (step s g)
    cases op : g.1
    · simpa [trace,List.countP_cons,op] using h
    · have count : (g :: gs).countP Prod.fst = gs.countP Prod.fst + 1 := by simp [op]
      simp only [trace,op,ite_true,count,Nat.pow_succ]
      cases hx : wire s g.2.1 r <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

private theorem readGood {s : List Column} {p a b : Nat} (all : ∀ w ∈ s, good p a b w) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases h : s[j]? with
  | none => simp [good]
  | some w => exact all w (List.mem_of_getElem? h)

private theorem preserve (gs : List Gate) (s : List Column) (p a b : Nat)
    (h : ∀ w ∈ s, good p a b w) (eq : trace s a gs = trace s b gs) :
    ∀ w ∈ gs.foldl step s, good p a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace (step s g) a gs = trace (step s g) b gs := by
      cases op : g.1 <;> simp [trace,op] at eq <;>
        cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all <;> omega
    apply ih _ _ tail
    intro w hw
    have l := readGood h g.2.1
    have r := readGood h g.2.2
    cases op : g.1
    · simp only [step,op,Bool.false_eq_true,ite_false,addOr,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · unfold good at *
        simp only [Bool.or_eq_true] at *
        tauto
    · simp only [step,op,ite_true,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · have same : wire s g.2.1 a = wire s g.2.1 b := by
          simp [trace,op,tail] at eq
          cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all
        unfold good both at *
        simp only [Bool.and_eq_true] at *
        rw [same] at l ⊢
        tauto

theorem separated_bound (s : List Column) (gs : List Gate) (o : Nat)
    (K : Finset (Fin 468)) (hk : 257 ≤ K.card)
    (sep : ∀ i j : K, i.val < j.val → ∃ p : Fin 52,
      ∀ w ∈ s, good p.val (52+i.val.val) (52+j.val.val) w)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52 + n.val) = false) :
    9 ≤ gs.countP Prod.fst := by
  let f (i : K) : Fin (2 ^ (gs.countP Prod.fst)) :=
    ⟨trace s (52 + i.val.val) gs,trace_lt _ _ _⟩
  have distinct (i j : K) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,hp0⟩ := sep i j lt
    have remain := preserve gs s _ _ _ hp0 (congrArg Fin.val eq)
    have bad := (readGood remain o) (hp p)
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin,Fintype.card_coe] at card
  by_contra h
  have le : gs.countP Prod.fst ≤ 8 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP Prod.fst ≤ 256 at bound
  omega
end PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndBudget



open PEqualNP.Research.PlaneCase35ThreeFreeGateReduction PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.Base PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35ThreeFreeGateReduction.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneCase35ThreeFreeGateReduction : (∀ S : Finset (Fin 52), S.card ≤ 4 → ∃ K : Finset (Fin 468), 257 ≤ K.card ∧
    ∀ i j : K, i.val < j.val → ∃ p : Fin 52, 4 ≤ p.val ∧ p ∉ S ∧
      ∀ t : Fin 30, base t p.val = true →
        base t (52+i.val.val) = true ∨ base t (52+j.val.val) = true) →
    ∀ (sw : Bool) (src : Fin 6 → Fin 32) (a b c l r : Bool) (j k : Fin 3)
      (gs : List Gate) (o : Nat),
    let f (i : Fin 6) := fixed sw (src i)
    let x (v : Nat) := gate a (f 0 v) (f 1 v)
    let y (v : Nat) := gate b (if l then x v else f 2 v) (if r then x v else f 3 v)
    let z (v : Nat) := gate c (pick j (f 4 v) (x v) (y v)) (pick k (f 5 v) (x v) (y v))
    let pool := (List.ofFn (fixed sw) ++ [x,y,z]) ++ [fun _ => false, fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ m : Fin 468, wire (gs.foldl step pool) o (52+m.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro cert sw src a b c l r j k gs o f x y z pool hp hn
  obtain ⟨S,size,transfer⟩ := exceptions sw src a b c l r j k
  obtain ⟨K,big,pairs⟩ := cert S size
  apply separated_bound pool gs o K big _ hp hn
  intro i j lt
  obtain ⟨p,high,clear,raw⟩ := pairs i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with before | con
  · rcases List.mem_append.mp before with input | free
    · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp input
      by_cases h : t.val < 30
      · simpa [good,fixed,h] using raw ⟨t.val,h⟩
      · simp [good,inactive sw t p (by omega) high]
    · exact transfer p i.val j.val high clear raw w free
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at con
    rcases con with rfl | rfl <;> simp [good]
