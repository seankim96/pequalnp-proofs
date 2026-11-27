import Mathlib.Data.List.GetD
import Mathlib.Data.List.Forall2
set_option maxRecDepth 15000
set_option maxHeartbeats 0
namespace PEqualNP.Research.PlaneCase35DominatingGuard
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
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def fixed (k : Fin 32) : Column :=
  if h : k.val < 30 then base ⟨k.val,h⟩
  else if k.val = 30 then mix true (input 13) (input 26) else mix true (input 13) (input 27)
def cheap (g : Bool × Nat × Nat) := g.1 && (g.2.1 == 32 || g.2.2 == 32)
def step (s : List Column) (g : Bool × Nat × Nat) :=
  if g.1 then s ++ [fun r => wire s g.2.1 r && wire s g.2.2 r]
  else s ++ [fun r => wire s g.2.1 r || wire s g.2.2 r]

abbrev G := Bool × Nat × Nat
def val (s : List Column) (g : G) (r : Nat) := if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def dominates (s : List Column) (g k : G) :=
  (∀ p : Fin 52, val s g p.val = true → val s k p.val = true) ∧
  (∀ j : Fin 468, val s k (52+j.val) = true → val s g (52+j.val) = true)

private abbrev rel (r : Nat) (a b : Column) := a r = true → b r = true
private theorem readRel {s t : List Column} {r : Nat} (h : List.Forall₂ (rel r) s t) (i : Nat) :
    rel r (wire s i) (wire t i) := by
  induction h generalizing i with
  | nil => exact id
  | cons ab _ ih => cases i with
    | zero => exact ab
    | succ i => exact ih i
private theorem pushRel {s t : List Column} {r : Nat} (g : G) (h : List.Forall₂ (rel r) s t) :
    List.Forall₂ (rel r) (step s g) (step t g) := by
  have a := readRel h g.2.1
  have b := readRel h g.2.2
  unfold step
  split <;> apply List.rel_append h <;> apply List.Forall₂.cons _ List.Forall₂.nil
  · intro hit
    obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp hit
    exact Bool.and_eq_true_iff.mpr ⟨a x,b y⟩
  · intro hit
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hit).imp a b)
private theorem transfer {s : List Column} {r : Nat} (g k : G) (gs : List G) (o : Nat)
    (h : val s g r = true → val s k r = true) :
    rel r (wire (gs.foldl step (step s g)) o) (wire (gs.foldl step (step s k)) o) := by
  have eqStep (z : G) : step s z = s ++ [val s z] := by cases z with
    | mk op ab => cases op <;> rfl
  have same (u : List Column) : List.Forall₂ (rel r) u u := by
    induction u with
    | nil => exact .nil
    | cons x _ ih => exact .cons id ih
  have init : List.Forall₂ (rel r) (step s g) (step s k) := by
    rw [eqStep,eqStep]; exact List.rel_append (same s) (.cons h .nil)
  suffices ∀ (u v : List Column), List.Forall₂ (rel r) u v →
      List.Forall₂ (rel r) (gs.foldl step u) (gs.foldl step v) from readRel (this _ _ init) o
  induction gs with
  | nil => exact fun _ _ h => h
  | cons x xs ih => exact fun _ _ h => ih _ _ (pushRel x h)
end PEqualNP.Research.PlaneCase35DominatingGuard
open PEqualNP.Research.PlaneCase35DominatingGuard in
theorem PEqualNP.Research.PlaneCase35DominatingGuard (sizeBound : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + gs.countP cheap ≤ 8 + gs.length) : ∀ (pre : List G) (g : G) (tail : List G) (o : Nat),
  let start := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  let s := pre.foldl step start
  let gs := pre ++ g :: tail
  cheap g = false →
  (∃ k : G, cheap k = true ∧ dominates s g k) →
  (∀ p : Fin 52, wire (gs.foldl step start) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step start) o (52+j.val) = false) →
  36 + gs.countP cheap ≤ 8 + gs.length := by
  intro pre g tail o start s gs old dom hp hn
  obtain ⟨k,hk,hpD,hnD⟩ := dom
  have lower := sizeBound (pre ++ k :: tail) o
    (fun p => by
      simp only [List.foldl_append,List.foldl_cons]
      exact transfer g k tail o (hpD p) (by simpa only [gs,List.foldl_append,List.foldl_cons] using hp p))
    (fun j => by
      simp only [List.foldl_append,List.foldl_cons]
      cases hit : wire (tail.foldl step (step s k)) o (52+j.val) with
      | false => simp only [hit]
      | true =>
        have bad := transfer k g tail o (hnD j) hit
        have no := hn j
        simp only [gs,List.foldl_append,List.foldl_cons] at no
        exact False.elim (Bool.noConfusion (bad.symm.trans no)))
  simp [gs,List.countP_append,hk,old] at lower ⊢
  omega
namespace PEqualNP.Research.PlaneCase35DominatingGuard
private abbrev eight := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
private abbrev pre : List G := [(true,15,32),(true,25,32)]
private abbrev ten := pre.foldl step eight
private def safeNeg (j : Nat) : Prop :=
  (fixed 19 (52+j) && (fixed 2 (52+j) || fixed 6 (52+j))) = true →
    (fixed 0 (52+j) && fixed 1 (52+j)) = true
private theorem safePos : ∀ p : Fin 52, (fixed 0 p.val && fixed 1 p.val) = false := by decide +kernel
private theorem neg0 : ∀ t : Fin 12, safeNeg (12*0+t.val) := by unfold safeNeg; decide +kernel
private theorem neg1 : ∀ t : Fin 12, safeNeg (12*1+t.val) := by unfold safeNeg; decide +kernel
private theorem neg2 : ∀ t : Fin 12, safeNeg (12*2+t.val) := by unfold safeNeg; decide +kernel
private theorem neg3 : ∀ t : Fin 12, safeNeg (12*3+t.val) := by unfold safeNeg; decide +kernel
private theorem neg4 : ∀ t : Fin 12, safeNeg (12*4+t.val) := by unfold safeNeg; decide +kernel
private theorem neg5 : ∀ t : Fin 12, safeNeg (12*5+t.val) := by unfold safeNeg; decide +kernel
private theorem neg6 : ∀ t : Fin 12, safeNeg (12*6+t.val) := by unfold safeNeg; decide +kernel
private theorem neg7 : ∀ t : Fin 12, safeNeg (12*7+t.val) := by unfold safeNeg; decide +kernel
private theorem neg8 : ∀ t : Fin 12, safeNeg (12*8+t.val) := by unfold safeNeg; decide +kernel
private theorem neg9 : ∀ t : Fin 12, safeNeg (12*9+t.val) := by unfold safeNeg; decide +kernel
private theorem neg10 : ∀ t : Fin 12, safeNeg (12*10+t.val) := by unfold safeNeg; decide +kernel
private theorem neg11 : ∀ t : Fin 12, safeNeg (12*11+t.val) := by unfold safeNeg; decide +kernel
private theorem neg12 : ∀ t : Fin 12, safeNeg (12*12+t.val) := by unfold safeNeg; decide +kernel
private theorem neg13 : ∀ t : Fin 12, safeNeg (12*13+t.val) := by unfold safeNeg; decide +kernel
private theorem neg14 : ∀ t : Fin 12, safeNeg (12*14+t.val) := by unfold safeNeg; decide +kernel
private theorem neg15 : ∀ t : Fin 12, safeNeg (12*15+t.val) := by unfold safeNeg; decide +kernel
private theorem neg16 : ∀ t : Fin 12, safeNeg (12*16+t.val) := by unfold safeNeg; decide +kernel
private theorem neg17 : ∀ t : Fin 12, safeNeg (12*17+t.val) := by unfold safeNeg; decide +kernel
private theorem neg18 : ∀ t : Fin 12, safeNeg (12*18+t.val) := by unfold safeNeg; decide +kernel
private theorem neg19 : ∀ t : Fin 12, safeNeg (12*19+t.val) := by unfold safeNeg; decide +kernel
private theorem neg20 : ∀ t : Fin 12, safeNeg (12*20+t.val) := by unfold safeNeg; decide +kernel
private theorem neg21 : ∀ t : Fin 12, safeNeg (12*21+t.val) := by unfold safeNeg; decide +kernel
private theorem neg22 : ∀ t : Fin 12, safeNeg (12*22+t.val) := by unfold safeNeg; decide +kernel
private theorem neg23 : ∀ t : Fin 12, safeNeg (12*23+t.val) := by unfold safeNeg; decide +kernel
private theorem neg24 : ∀ t : Fin 12, safeNeg (12*24+t.val) := by unfold safeNeg; decide +kernel
private theorem neg25 : ∀ t : Fin 12, safeNeg (12*25+t.val) := by unfold safeNeg; decide +kernel
private theorem neg26 : ∀ t : Fin 12, safeNeg (12*26+t.val) := by unfold safeNeg; decide +kernel
private theorem neg27 : ∀ t : Fin 12, safeNeg (12*27+t.val) := by unfold safeNeg; decide +kernel
private theorem neg28 : ∀ t : Fin 12, safeNeg (12*28+t.val) := by unfold safeNeg; decide +kernel
private theorem neg29 : ∀ t : Fin 12, safeNeg (12*29+t.val) := by unfold safeNeg; decide +kernel
private theorem neg30 : ∀ t : Fin 12, safeNeg (12*30+t.val) := by unfold safeNeg; decide +kernel
private theorem neg31 : ∀ t : Fin 12, safeNeg (12*31+t.val) := by unfold safeNeg; decide +kernel
private theorem neg32 : ∀ t : Fin 12, safeNeg (12*32+t.val) := by unfold safeNeg; decide +kernel
private theorem neg33 : ∀ t : Fin 12, safeNeg (12*33+t.val) := by unfold safeNeg; decide +kernel
private theorem neg34 : ∀ t : Fin 12, safeNeg (12*34+t.val) := by unfold safeNeg; decide +kernel
private theorem neg35 : ∀ t : Fin 12, safeNeg (12*35+t.val) := by unfold safeNeg; decide +kernel
private theorem neg36 : ∀ t : Fin 12, safeNeg (12*36+t.val) := by unfold safeNeg; decide +kernel
private theorem neg37 : ∀ t : Fin 12, safeNeg (12*37+t.val) := by unfold safeNeg; decide +kernel
private theorem neg38 : ∀ t : Fin 12, safeNeg (12*38+t.val) := by unfold safeNeg; decide +kernel
theorem and01Witness : dominates ten (true,0,1) (true,19,32) := by
  constructor
  · intro p h
    change (fixed 0 p.val && fixed 1 p.val) = true at h
    rw [safePos p] at h
    contradiction
  · intro j
    change safeNeg j.val
    have batches (i : Fin 39) (t : Fin 12) : safeNeg (12*i.val+t.val) := by
      match i with
      | ⟨0,_⟩ => exact neg0 t
      | ⟨1,_⟩ => exact neg1 t
      | ⟨2,_⟩ => exact neg2 t
      | ⟨3,_⟩ => exact neg3 t
      | ⟨4,_⟩ => exact neg4 t
      | ⟨5,_⟩ => exact neg5 t
      | ⟨6,_⟩ => exact neg6 t
      | ⟨7,_⟩ => exact neg7 t
      | ⟨8,_⟩ => exact neg8 t
      | ⟨9,_⟩ => exact neg9 t
      | ⟨10,_⟩ => exact neg10 t
      | ⟨11,_⟩ => exact neg11 t
      | ⟨12,_⟩ => exact neg12 t
      | ⟨13,_⟩ => exact neg13 t
      | ⟨14,_⟩ => exact neg14 t
      | ⟨15,_⟩ => exact neg15 t
      | ⟨16,_⟩ => exact neg16 t
      | ⟨17,_⟩ => exact neg17 t
      | ⟨18,_⟩ => exact neg18 t
      | ⟨19,_⟩ => exact neg19 t
      | ⟨20,_⟩ => exact neg20 t
      | ⟨21,_⟩ => exact neg21 t
      | ⟨22,_⟩ => exact neg22 t
      | ⟨23,_⟩ => exact neg23 t
      | ⟨24,_⟩ => exact neg24 t
      | ⟨25,_⟩ => exact neg25 t
      | ⟨26,_⟩ => exact neg26 t
      | ⟨27,_⟩ => exact neg27 t
      | ⟨28,_⟩ => exact neg28 t
      | ⟨29,_⟩ => exact neg29 t
      | ⟨30,_⟩ => exact neg30 t
      | ⟨31,_⟩ => exact neg31 t
      | ⟨32,_⟩ => exact neg32 t
      | ⟨33,_⟩ => exact neg33 t
      | ⟨34,_⟩ => exact neg34 t
      | ⟨35,_⟩ => exact neg35 t
      | ⟨36,_⟩ => exact neg36 t
      | ⟨37,_⟩ => exact neg37 t
      | ⟨38,_⟩ => exact neg38 t
      | ⟨v+39,h⟩ => omega
    have h := batches ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
    simpa only [Nat.div_add_mod] using h
theorem and01Bound (sizeBound : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + gs.countP cheap ≤ 8 + gs.length) (tail : List G) (o : Nat)
    (hp : ∀ p : Fin 52, wire (tail.foldl step (step ten (true,0,1))) o p.val = true)
    (hn : ∀ j : Fin 468, wire (tail.foldl step (step ten (true,0,1))) o (52+j.val) = false)
    (h28 : 26 ≤ tail.countP cheap) : 64 ≤ 11 + tail.length := by
  have b := PEqualNP.Research.PlaneCase35DominatingGuard sizeBound pre (true,0,1) tail o
    (by decide) ⟨(true,19,32),by decide,and01Witness⟩ hp hn
  change 36 + (([(true,15,32),(true,25,32),(true,0,1)] : List G) ++ tail).countP cheap ≤ 8 + ([(true,15,32),(true,25,32),(true,0,1)] ++ tail).length at b
  simp [List.countP_append,List.countP_cons,cheap] at b h28
  omega
end PEqualNP.Research.PlaneCase35DominatingGuard
