import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace PEqualNP.Research.PlaneCase35AdaptiveCharge
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
def value (s : List Column) (g : G) (r : Nat) :=
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def possible (pred : G → Bool) (s : List Column) (g : G) := ∃ alt : G, pred alt = true ∧ ∀ r : Fin 520, value s alt r.val = value s g r.val
def free (g : G) := !g.1 || cheap g
noncomputable def credit (s : List Column) (g : G) : Nat := by
  classical
  exact if possible Prod.fst s g ∧ possible free s g then 1 else 0
noncomputable def auditStep (state : List Column × Nat) (g : G) := (step state.1 g,state.2 + credit state.1 g)
def better (a b : Column) :=
  (∀ p : Fin 52, a p.val = true → b p.val = true) ∧
  (∀ j : Fin 468, b (52+j.val) = true → a (52+j.val) = true)
def intrinsic (g : G) := cheap g || (g.2.1 == g.2.2)
def admissible (s : List Column) (g : G) :=
  ∃ k : G, intrinsic k = true ∧ better (value s g) (value s k)
noncomputable def weight (s : List Column) (g : G) : Nat := by
  classical
  exact if admissible s g then 1 else 0
noncomputable def tally (state : List Column × Nat) (g : G) :=
  (step state.1 g,state.2 + weight state.1 g)
private theorem transB {a b c : Column} (h : better a b) (k : better b c) : better a c :=
  ⟨fun p v => k.1 p (h.1 p v),fun j v => h.2 j (k.2 j v)⟩
private theorem combine {a b c d : Bool} (op : Bool) (h : a = true → c = true) (k : b = true → d = true) :
    (if op then a && b else a || b) = true → (if op then c && d else c || d) = true := by
  cases op <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.and_eq_true,Bool.or_eq_true]
  · exact Or.imp h k
  · exact fun z => ⟨h z.1,k z.2⟩
private theorem snoc (s : List Column) (x : Column) (j : Nat) :
    wire (s ++ [x]) j = if j = s.length then x else wire s j := by
  by_cases h : j < s.length
  · rw [ite_eq_right (show j ≠ s.length by omega)]; exact List.getD_append _ _ _ _ h
  · rw [wire,List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : j = s.length
    · simp [e]
    · rw [ite_eq_right e,wire,List.getD_eq_default _ _ (show [x].length ≤ j-s.length by simp; omega),
          List.getD_eq_default _ _ (show s.length ≤ j by omega)]
private theorem stepEq (s : List Column) (g : G) : step s g = s ++ [value s g] := by
  cases g with | mk op ab => cases op <;> rfl

private theorem paid (s : List Column) (g : G) (h : intrinsic g = true) : credit s g = 1 := by
  classical
  rcases Bool.or_eq_true_iff.mp h with ch | eq
  · have a : possible Prod.fst s g := ⟨g,(Bool.and_eq_true_iff.mp ch).1,fun _ => rfl⟩
    have b : possible free s g := ⟨g,by simp [free,ch],fun _ => rfl⟩
    simp [credit,a,b]
  · have e : g.2.1 = g.2.2 := by simpa using eq
    have a : possible Prod.fst s g := ⟨(true,g.2.2,g.2.2),rfl,by intro r; simp [value,e]⟩
    have b : possible free s g := ⟨(false,g.2.2,g.2.2),rfl,by intro r; simp [value,e]⟩
    simp [credit,a,b]

private theorem simulate (gs : List G) (s t : List Column) (a b : Nat) (ab : a ≤ b)
    (len : s.length = t.length) (h : ∀ j, better (wire s j) (wire t j)) :
    ∃ ys : List G, ys.length = gs.length ∧
      (∀ j, better (wire (gs.foldl step s) j) (wire (ys.foldl step t) j)) ∧
      (gs.foldl tally (s,a)).2 ≤ (ys.foldl auditStep (t,b)).2 := by
  classical
  induction gs generalizing s t a b with
  | nil => exact ⟨[],rfl,h,ab⟩
  | cons g gs ih =>
    have pick : ∃ k, better (value s g) (value s k) ∧ weight s g ≤ credit t k := by
      by_cases e : admissible s g
      · obtain ⟨k,hk,hv⟩ := (show admissible s g from e)
        exact ⟨k,hv,by simp [weight,e,paid t k hk]⟩
      · exact ⟨g,⟨fun _ => id,fun _ => id⟩,by simp [weight,e]⟩
    obtain ⟨k,dom,cost⟩ := pick
    have mono : better (value s k) (value t k) :=
      ⟨fun p => combine k.1 ((h k.2.1).1 p) ((h k.2.2).1 p),
       fun j => combine k.1 ((h k.2.1).2 j) ((h k.2.2).2 j)⟩
    have next : ∀ j, better (wire (step s g) j) (wire (step t k) j) := by
      intro j
      simp only [stepEq,snoc,len]
      split
      · exact transB dom mono
      · exact h j
    obtain ⟨ys,hlen,hr,hc⟩ := ih (step s g) (step t k) (a+weight s g) (b+credit t k)
      (by omega) (by simp [stepEq,len]) next
    exact ⟨k::ys,by simp [hlen],hr,hc⟩
end PEqualNP.Research.PlaneCase35AdaptiveCharge
open PEqualNP.Research.PlaneCase35AdaptiveCharge in
theorem PEqualNP.Research.PlaneCase35AdaptiveCharge (sizeBound : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + (gs.foldl auditStep (pool,0)).2 ≤ 8 + gs.length) : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + (gs.foldl tally (pool,0)).2 ≤ 8 + gs.length := by
  intro gs o pool hp hn
  obtain ⟨ys,hl,hr,hc⟩ := simulate gs pool pool 0 0 (by decide) rfl (fun _ => ⟨fun _ => id,fun _ => id⟩)
  have bound := sizeBound ys o (fun p => (hr o).1 p (hp p)) (fun j => by
    cases e : wire (ys.foldl step pool) o (52+j.val) with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion ((((hr o).2 j e)).symm.trans (hn j))))
  change 35 + (ys.foldl auditStep (pool,0)).2 ≤ 8 + ys.length at bound
  omega

namespace PEqualNP.Research.PlaneCase35AdaptiveCharge
private abbrev eight := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
private abbrev pre : List G := [(true,15,32),(true,25,32),(true,0,17),(true,0,23)]
private abbrev g13 : G := (true,23,26)
private abbrev g14 : G := (true,0,38)
private abbrev twelve := pre.foldl step eight
private abbrev thirteen := step twelve g13
private abbrev prefix14 := pre ++ [g13,g14]
private def row37 (r : Nat) := input 0 r && input 23 r
private def row38 (r : Nat) := input 23 r && input 26 r
private theorem rowlink : ∀ p : Fin 52, row38 p.val = true → row37 p.val = true := by decide +kernel
private theorem silent0 : ∀ j : Fin 12, row37 (52+(12*0+j.val)) = false := by decide +kernel
private theorem silent1 : ∀ j : Fin 12, row37 (52+(12*1+j.val)) = false := by decide +kernel
private theorem silent2 : ∀ j : Fin 12, row37 (52+(12*2+j.val)) = false := by decide +kernel
private theorem silent3 : ∀ j : Fin 12, row37 (52+(12*3+j.val)) = false := by decide +kernel
private theorem silent4 : ∀ j : Fin 12, row37 (52+(12*4+j.val)) = false := by decide +kernel
private theorem silent5 : ∀ j : Fin 12, row37 (52+(12*5+j.val)) = false := by decide +kernel
private theorem silent6 : ∀ j : Fin 12, row37 (52+(12*6+j.val)) = false := by decide +kernel
private theorem silent7 : ∀ j : Fin 12, row37 (52+(12*7+j.val)) = false := by decide +kernel
private theorem silent8 : ∀ j : Fin 12, row37 (52+(12*8+j.val)) = false := by decide +kernel
private theorem silent9 : ∀ j : Fin 12, row37 (52+(12*9+j.val)) = false := by decide +kernel
private theorem silent10 : ∀ j : Fin 12, row37 (52+(12*10+j.val)) = false := by decide +kernel
private theorem silent11 : ∀ j : Fin 12, row37 (52+(12*11+j.val)) = false := by decide +kernel
private theorem silent12 : ∀ j : Fin 12, row37 (52+(12*12+j.val)) = false := by decide +kernel
private theorem silent13 : ∀ j : Fin 12, row37 (52+(12*13+j.val)) = false := by decide +kernel
private theorem silent14 : ∀ j : Fin 12, row37 (52+(12*14+j.val)) = false := by decide +kernel
private theorem silent15 : ∀ j : Fin 12, row37 (52+(12*15+j.val)) = false := by decide +kernel
private theorem silent16 : ∀ j : Fin 12, row37 (52+(12*16+j.val)) = false := by decide +kernel
private theorem silent17 : ∀ j : Fin 12, row37 (52+(12*17+j.val)) = false := by decide +kernel
private theorem silent18 : ∀ j : Fin 12, row37 (52+(12*18+j.val)) = false := by decide +kernel
private theorem silent19 : ∀ j : Fin 12, row37 (52+(12*19+j.val)) = false := by decide +kernel
private theorem silent20 : ∀ j : Fin 12, row37 (52+(12*20+j.val)) = false := by decide +kernel
private theorem silent21 : ∀ j : Fin 12, row37 (52+(12*21+j.val)) = false := by decide +kernel
private theorem silent22 : ∀ j : Fin 12, row37 (52+(12*22+j.val)) = false := by decide +kernel
private theorem silent23 : ∀ j : Fin 12, row37 (52+(12*23+j.val)) = false := by decide +kernel
private theorem silent24 : ∀ j : Fin 12, row37 (52+(12*24+j.val)) = false := by decide +kernel
private theorem silent25 : ∀ j : Fin 12, row37 (52+(12*25+j.val)) = false := by decide +kernel
private theorem silent26 : ∀ j : Fin 12, row37 (52+(12*26+j.val)) = false := by decide +kernel
private theorem silent27 : ∀ j : Fin 12, row37 (52+(12*27+j.val)) = false := by decide +kernel
private theorem silent28 : ∀ j : Fin 12, row37 (52+(12*28+j.val)) = false := by decide +kernel
private theorem silent29 : ∀ j : Fin 12, row37 (52+(12*29+j.val)) = false := by decide +kernel
private theorem silent30 : ∀ j : Fin 12, row37 (52+(12*30+j.val)) = false := by decide +kernel
private theorem silent31 : ∀ j : Fin 12, row37 (52+(12*31+j.val)) = false := by decide +kernel
private theorem silent32 : ∀ j : Fin 12, row37 (52+(12*32+j.val)) = false := by decide +kernel
private theorem silent33 : ∀ j : Fin 12, row37 (52+(12*33+j.val)) = false := by decide +kernel
private theorem silent34 : ∀ j : Fin 12, row37 (52+(12*34+j.val)) = false := by decide +kernel
private theorem silent35 : ∀ j : Fin 12, row37 (52+(12*35+j.val)) = false := by decide +kernel
private theorem silent36 : ∀ j : Fin 12, row37 (52+(12*36+j.val)) = false := by decide +kernel
private theorem silent37 : ∀ j : Fin 12, row37 (52+(12*37+j.val)) = false := by decide +kernel
private theorem silent38 : ∀ j : Fin 12, row37 (52+(12*38+j.val)) = false := by decide +kernel
private theorem silent : ∀ j : Fin 468, row37 (52+j.val) = false := by
  intro j
  have bat (i : Fin 39) (t : Fin 12) : row37 (52+(12*i.val+t.val)) = false := by
    match i with
    | ⟨0,_⟩ => exact silent0 t
    | ⟨1,_⟩ => exact silent1 t
    | ⟨2,_⟩ => exact silent2 t
    | ⟨3,_⟩ => exact silent3 t
    | ⟨4,_⟩ => exact silent4 t
    | ⟨5,_⟩ => exact silent5 t
    | ⟨6,_⟩ => exact silent6 t
    | ⟨7,_⟩ => exact silent7 t
    | ⟨8,_⟩ => exact silent8 t
    | ⟨9,_⟩ => exact silent9 t
    | ⟨10,_⟩ => exact silent10 t
    | ⟨11,_⟩ => exact silent11 t
    | ⟨12,_⟩ => exact silent12 t
    | ⟨13,_⟩ => exact silent13 t
    | ⟨14,_⟩ => exact silent14 t
    | ⟨15,_⟩ => exact silent15 t
    | ⟨16,_⟩ => exact silent16 t
    | ⟨17,_⟩ => exact silent17 t
    | ⟨18,_⟩ => exact silent18 t
    | ⟨19,_⟩ => exact silent19 t
    | ⟨20,_⟩ => exact silent20 t
    | ⟨21,_⟩ => exact silent21 t
    | ⟨22,_⟩ => exact silent22 t
    | ⟨23,_⟩ => exact silent23 t
    | ⟨24,_⟩ => exact silent24 t
    | ⟨25,_⟩ => exact silent25 t
    | ⟨26,_⟩ => exact silent26 t
    | ⟨27,_⟩ => exact silent27 t
    | ⟨28,_⟩ => exact silent28 t
    | ⟨29,_⟩ => exact silent29 t
    | ⟨30,_⟩ => exact silent30 t
    | ⟨31,_⟩ => exact silent31 t
    | ⟨32,_⟩ => exact silent32 t
    | ⟨33,_⟩ => exact silent33 t
    | ⟨34,_⟩ => exact silent34 t
    | ⟨35,_⟩ => exact silent35 t
    | ⟨36,_⟩ => exact silent36 t
    | ⟨37,_⟩ => exact silent37 t
    | ⟨38,_⟩ => exact silent38 t
    | ⟨i+39,h⟩ => omega
  simpa only [Nat.div_add_mod] using bat ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
private theorem w13 : admissible twelve g13 := by
  refine ⟨(false,37,37),rfl,?_,?_⟩
  · intro p hp
    change row38 p.val = true at hp
    change (row37 p.val || row37 p.val) = true
    simpa using rowlink p hp
  · intro j hj
    change (row37 (52+j.val) || row37 (52+j.val)) = true at hj
    simp [silent j] at hj
private theorem w14 : admissible thirteen g14 := by
  refine ⟨(false,37,37),rfl,?_,?_⟩
  · intro p hp
    change (input 0 p.val && row38 p.val) = true at hp
    change (row37 p.val || row37 p.val) = true
    simpa using rowlink p (Bool.and_eq_true_iff.mp hp).2
  · intro j hj
    change (row37 (52+j.val) || row37 (52+j.val)) = true at hj
    simp [silent j] at hj
private theorem unitGuard (s : List Column) (g : G) (h : cheap g = true) : weight s g = 1 := by
  classical
  have ok : admissible s g := ⟨g,by simp [intrinsic,h],⟨fun _ => id,fun _ => id⟩⟩
  simp [weight,ok]
private theorem reserve (s : List Column) (n : Nat) (gs : List G) :
    n + gs.countP cheap ≤ (gs.foldl tally (s,n)).2 := by
  induction gs generalizing n s with
  | nil => simp
  | cons g gs ih =>
    have h := ih (step s g) (n+weight s g)
    simp only [List.foldl_cons,tally,List.countP_cons]
    cases e : cheap g <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
      first | omega | rw [unitGuard s g e] at h ⊢; omega
theorem fourteenBound (general : ∀ (gs : List G) (o : Nat),
    (∀ p : Fin 52, wire (gs.foldl step eight) o p.val = true) →
    (∀ j : Fin 468, wire (gs.foldl step eight) o (52+j.val) = false) →
    35 + (gs.foldl tally (eight,0)).2 ≤ 8 + gs.length)
    (tail : List G) (o : Nat)
    (hp : ∀ p : Fin 52, wire ((prefix14 ++ tail).foldl step eight) o p.val = true)
    (hn : ∀ j : Fin 468, wire ((prefix14 ++ tail).foldl step eight) o (52+j.val) = false)
    (reads : 25 ≤ tail.countP cheap) : 64 ≤ 14 + tail.length := by
  classical
  have law := general (prefix14 ++ tail) o hp hn
  have hc := reserve (prefix14.foldl tally (eight,0)).1 (prefix14.foldl tally (eight,0)).2 tail
  have h1 := unitGuard eight (true,15,32) rfl
  have h2 := unitGuard (step eight (true,15,32)) (true,25,32) rfl
  have h3 : weight twelve g13 = 1 := by unfold weight; exact if_pos w13
  have h4 : weight thirteen g14 = 1 := by unfold weight; exact if_pos w14
  have fixedCost : 4 ≤ (prefix14.foldl tally (eight,0)).2 := by
    change 4 ≤ 0 + weight eight (true,15,32) + weight (step eight (true,15,32)) (true,25,32) +
      weight _ (true,0,17) + weight _ (true,0,23) + weight twelve g13 + weight thirteen g14
    rw [h1,h2,h3,h4]; omega
  change (prefix14.foldl tally (eight,0)).2 + tail.countP cheap ≤ (tail.foldl tally (prefix14.foldl tally (eight,0))).2 at hc
  rw [List.foldl_append] at law
  simp only [List.length_append,show prefix14.length = 6 from rfl] at law
  omega
end PEqualNP.Research.PlaneCase35AdaptiveCharge
