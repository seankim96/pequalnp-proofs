import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation

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

end PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation

open PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation in
theorem PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation : ∀ (base : List Column)
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


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndBudget
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
    (sep : separated s)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52 + n.val) = false) :
    9 ≤ gs.countP Prod.fst := by
  obtain ⟨n,h⟩ := sep
  let f (i : Fin 257) : Fin (2 ^ (gs.countP Prod.fst)) :=
    ⟨trace s (52 + (n i).val) gs,trace_lt _ _ _⟩
  have distinct (i j : Fin 257) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,hp0⟩ := h i j lt
    have remain := preserve gs s _ _ _ hp0 (congrArg Fin.val eq)
    have bad := (readGood remain o) (hp p)
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Fin.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at card
  by_contra h
  have le : gs.countP Prod.fst ≤ 8 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP Prod.fst ≤ 256 at bound
  omega
end PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndBudget

open PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndBudget : ∀ (base : List Column)
    (ors : List (Nat × Nat)) (left right : Nat) (tail : List Gate) (out : Nat),
    (∀ l r : List Column, (∀ w ∈ l, w ∈ base) → (∀ w ∈ r, w ∈ base) →
      separated (base ++ [both (disj l) (disj r)])) →
    let s := ors.foldl addOr base
    let final := tail.foldl step (s ++ [both (wire s left) (wire s right)])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52 + n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro base ors left right tail out cert
  dsimp only
  intro hp hn
  exact separated_bound _ tail out (PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation base ors left right cert) hp hn


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape

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
end PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape in
theorem PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape : ∀ a b : Fin 30,
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


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthGuard
open PlaneFirstAndSeparation PlaneFirstAndBudget
open PlaneCase35FifthAndShape (input mix pos neg extend)
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def omittedFlags : Nat := 4406657483279
private def indices (i : Nat) : Nat :=
  (0x193c96431d8dc662f1588c3e170781c05fefb7cbddeaf378bbddae973b95c2df6eb65aed568b3d9ac961b057ebd5dae56eb358abd5aa953a8d429f4da65228d45a250a833f9f4e66f3499cca5f2c95caa53289348a411f8d46631168ac52271288c421d0d8642a110783412070280bf9f6f97c3ddecf479bc9deec753a5d0e772b8dc4e06fb75b4d96c355a0cf6632d92c863b198ac461b0982bc5dae972b55a2c960af572b556a853a9948a351285409f4f27134984b255288f47235188b4521d0c8541a09027f3f1f4f6793c1dcec74399c4e06f369b0d66833998ca633117cbc5a2c960aa5327938964a249188a44219007e3e1e0ec6c35198c4602e160ac54291408c44210d06430160a85026110803c1c0d0602c14090401c0a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0xa424848e42084a64080d2a4048c824028d0e2a040a6290422e28042ae22044a621848262104a262084c2a2040e822024e061908226180832e130a02e128242a124a40e120a42a114a20e110a22e108252a104a602102870a0e0c08a0c0c1860b0c02e0a0c0a6090c222082c30a070e00a060e08a058680a054a80a050e80a044a882042c90e038602e030e02e028642a024a48e018682a014aa02012ca0200a4d020068e09c4001c9c2010c9c0011c9940214991022499002349884128984021c9824308982030c9814320981032498043285700045d64000d55080515500055d484109d480119d44001d942014c5408151d4041491402154531002553040615300065d2804295250405d24040dd2040691202464d150205d140215d114221d110225d10c241d108251d1042611102074d0c04195098501509412150905215088511d0841291082530906060cd058601d050605d048611903070490287401022544d01c301d018701d014321d00c341100a5508e4008cce0008ecc8011a8c4009c4c30106cc2010e4c181824c101864c081920c021944b210064b100264b01026ca8102a8a6100c8a45088ca2100e0a030a44989012896120489492108941214c930206c929202c921206c910226c909212090303448a910288a5108888512808831308865208886120c88452880843094c830306c8293028825308881c380c81838288143a0880d380080b19008071a04710007470804347000474650085c644089c64008dc62004e461008746080c345c08114588013458081345508054520846451080745080530502854c4c4809c4c0819c4a090a449810344949014488113c48490944548814450885c4448890442894443090684249480422944441c181441818344149810412984440c1c1040a1d004069c043890034385021438102343210464310027430d041430904343050610303064c2c5009c2c140942904234289403c28502942584814250485c24508902434840223444421848302124a4020b4c002070e041c901141c580141948214190823418901341858210183830c154a01c150a05c1492110143814c130a06c1292428125a400123844c114a21c10d241010786040c9411c0c580900c3c1080a590800a3d00409850340949210092d20008b51000879208070e048065a080063c04c05c281c058681c054a810052c84c04d281004b490c0387020032d04802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x80002008000008400000240000012000000100000008000000400000020000001000000080000004000000200000010000000800000040000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x1fe03f7e077e00003f807ef00000ff077f000000000000000003bb001baa4d58800688841c794f42c010a003d01e001b8801c00e24800032400000140400033f9eb0e01d0000000000000000df7947d0190e3b71a0882e86040c0c00800200000000000000003fb7f7f7e71e000000000007efdb7f0e9deff23f706c607409fffffffffffc0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffc0000000000000000000000000000000000000000000000000fff800000000001fffffffffff000000000000000000000000003e00000000007003ff800000000ffc000000007ffffffffe000000000000000000ff800000000001803fc000000601fe0000003fe0000000fffffe000000000000003ff800000380b01c1fe0000000e0ffc0001c0ff000007fc000ffffc0000000381803f00000200601000fe0004008401e00000707f000381f007f001ff8000000000187f00488108066040f0090031c00f000e2430780000c7830780e03fe018901e0b3078103002000000470061149c66700081040380100020003c0c1c0f802628c1573381060011160e1a702c40090027122141993c04098c319101c9e63102821002152000104000c48ab6050052500b640a10a019a1828544245090ced64020a400a1481542121151201600010006a36840022d2aa8a89059417525545e000000000000000000000000000017fedffb1c000000000f7ece79cddfc6c339d803bdffbd5a0000000000000000000000000000bdebfcc80000077b75ede62503fa003febd60000001d00dbfd200000000000000000000000edf000015b557400003fc07efc0efc00007f00fde00001fe0efe0000000000000000077600375480000000000018be1bc0001f87f97e0000787fc00007c3ff00000000000fe00ff387c00007c3e0000000000000034f050000c7e3b0001e3f8001ef00000001f83fc4e39c0006300058f630f000c600000000000628580061c5e0098007600000e40cbc3618006871c0079999b004001c40530048000000000d32814d805034000450020544080ad406d40116288098601618880801c68840200000114c05040100d58800688841c794f42c010a003d01e001b8801c00e248000324000001404000000000000000fd5699add101541baf5ada0b00b70e805a206205a0059000511019fcf58700e80000000000000006fbca3e80c871db8d044174302060600400100000000000000001fdbfbfbf38f000000000003f7edbf874ef7f91fb836303a04 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0x3ffc4c3ffebfff73fffffffffffe69724ffffffffffffffffffffafffdcfffffffc4fff9bfcbffff47fc7fc3ffffffffe9fff77ffd3ffffff2e6ff2fff93ffffff0fffff0ffffff8fffff4cefffcfffe5cbffe41bffffffffffc3ffebfffffffd3fcb1bffe6ffffff93fff1ffffffffffffffffffffffffffffe3fe2c9a65283fc7fc3f33ffffffffff7fffd2ffffff8ffff26bffe0ff1ff0ffffffffffffffffff48cfc7cffffffdafff83fc7fc3ffffffffe9ffffd9fffffffff8ff8b24fffffff1ff08bffffffffffffffff4fffc7ffffffcbf38a83fc7fc3ffffffffffffffdafd3fca1ff8ffffffcefe0ff1ff0ffffffffffffffffff4cefc7cfffffffffca83fc7fc3ffffc3ffe9fffffffd3fffff38c7fffffffe0fffffffffff0fffa7ffff6bf4ce287fe3ffffffffffffc7ffdbfffffffebfffffffd2fff13ffdffff77ffcdff1ff0fffffffffaffffffff48dfffcff7fffdd67fffffffc3ffffffffebffffffffffffffffdffff74e4bf731ff0fffffffffa7fffffffffffffccb7fffddfff47fc7fc3ffc4c3ffeb97ffffffffffff3fdffff77f4bf73fffffffffffffafffffffffce2c4fff7ffffffff45cc7fc3ffc4c3ffebffffdbfd2ffffffffffff74efcdfffffffffffffffafffff6ff4bffc4fffffffdd3bf37ffffc3ffffffffe9fffffffd1fffffffdffff77f2bfff1ff0fffff0ffffffffffff48efffcffffffddfff19cc7fffffffc3ffebffffd9fd238b1bfffffff77ffffff1ffffff530fffafffffffffccfffcfffdbfff67f47ffffffffffc3ffebfffffffd1fffff3ffffff69957fffffff6ccffffffaff8fffd4ffffffffffffcbf652ffffffc3ffffffffebfe3fff53f33fffffffff2fd94bffffff0ffffffffffff8dffff4bffffffffffc9afff37ffffc3ffffc3fffffe37ff55237fffffffff26bfffffffffffff530fffafffff6fffffffffffffffd3395fccc7fffffd4c3ffebfff7dbfff33f1fffffff24fffffff1ffffff530ffffffffffff4fffc7fcbffffff39537fc7fffffffc3fffffffffffd3fcbffffc7ffffce54d331ffffffff0ffffffffffff4ff2c7ffffffffffd537fc7fffffffc3ffff97fffffd333fff3fc7ffffff546fffffffffff0fffae6fff6bf4cd2c7ffffffffffd5fffc7fffffffffffffffffdbffffffff32ffff24cefffff1ff0fffffffffafffdf6d4fff2fffffffffd33bffffc7fc3ffffffffe9fe27fffff3bffff2ffff2ffffd1ff1ff0fffff0fffae5fdcfffffffffcff1fffd3ffffffffffffffffffffffe2fff513fff1fffffff2fff28dff1ff0fffff0fffafffddfd54ffffffff1ffcbf3bfffffffffffffc3ffebfe37da553fcb1fffffffffcefffff1ffffffff0fffa6681ffff4cefffccbfffcbffcaffffffffffffc3ffeb92377f5533bfffffc7ff2ffffffffffffffffe8fffffffdcfff47fffffff9a55edfe4ffffffffffeca3fffffffffffffffffefbbf97fb69911fffffffffb28ffffffffffd747f23ffffffffeda64ffffffffffffa3fffffffffffd1ffffefffffffb6957f73fffffffb28ffffff8bf6ff4bffc5ffffff7adfff37ffffffffffa3ffffffffdb55237ffefffffffb69fff73ffffffffe8ffffffffffff48cfffbff1dbfeda7f1bffffffffffa3ffff97f73ffd1ffffffbbffd7b7f57ffffffffffb28cbffffffffffffffffbffffffeda52fff17fffffeca3ffff97ffff5ff33f16fbbffffb69491ffffffffffe8fffffffde6ff4bfffffffffffedfff34c17fffffffa3fffffff79bfd2fff17fffffffb69fcdffffffffffe8fffffffff6ff48cfffbffffffeda7f1bfffffff73ffffffffffffffff3bf16ffe6fdefff920fffb3ffffffffffffffdcffffccfc5bff9bf5edfff83ffecfe573fff0ffffffffffff3bffefbbffdefff93ffc8b3f95cfffffffff83fffffce23fbeefff7bffe4ffffffffffffffffe8ffffff5ff33ffefbbfffffd9906fffb3ffffffffffa3fffffd7fcdfc6bff9bffff664ffffecffffffff1fe8fe073ffff37ffefba6957fffffffffffffffb3ffffa7ffdefd7fcefc5bee9bfffffff47ffffffffffff2ffffff799fff3bf1affe6fffb7fffffc8b3ffffffffffffffff67ffcefffbeefe5fedfe41bf16cffffffffffe9fe07995d13881afbbffffffffffffffff8bffffffffe4ffffffffffc5bff7fffff3bfffffecfe273fff0fff93fffffff3bffeffdfffffffffffc5fff8bffffffffe4fffffffcefc5bff7ffffffff83ffffffffffffffff9bffff55233f1effffffffd9fe0fffb3f88cfffc7ffe6ffffffffffffbfffff5edfd5ffffffffffffff1fff9bfffffff33ffeffff897fff560ffffffffffffffffe4fdc67ffcefffbff1e2fedffffffffffe2fffff1fff9bf7d95523bf1efffffffffffe0fffffffffffffffa3f8bfffffff23ffee7ff7bffd537ffffffffffffffe897fffffff3481affdfffffff57ffffb3fffffffffffff8bfffffff2bffeefff7bf3bffdc17fffffffffffe8fe2fff57ffca17fbbffdefcefffffffffffffffc3ffe5fffffffcefffbff7ff7bffca1bf23fffffffff0fff97fffffff3bf1affdfffffffffffc8fffffffffc3ffe58bfffffce2bfbff7fffffffffdc17fffffffff1fe9920fff57f38a1affdffffffffffffffffffffffc3ffe683fffffcdfffbfffdb5ff655fffffffdbfffff2fff9bfffffffffffefffffffb7f28dfc8b3f6ccfffffffe4fdefffffffffbee1fffffffffffffffdb33fff2fff9bf7ff5fffca1efbbffffb59fcdfffb3fffffffffffe6ffffd744dfffbffffffff64affffffffffffffffe893fffffff33ffeffc76fffd9fc6ffffff6fffffcbffe683ffd7fcd287bffffffff67fffffffffffffff1fff9a2ffffff33f1efffffd7fff551ffffffffffffffffffffffffffffc7feefff5edfff34c22cffffffffffe8fe27ffffffc8fffbbffd7ffffff33ffffffffffc3ffe6fdf6fffcdfffbfffff5fffd5fff23fffffecffffff9a27ff5fffc8fffbbfffffce4bf33ffffffffffcbffe6fffffffcefc7bfffffffffd247f23fffffffff2fe99bffff5ff3881effffffffff491fffffffffffffffa3ffde6fffffffffff1fffed38afcc23fffffffffffffffffdb5fffff1fffffffffce28dfc8b3ffffffffffa3f89e6fffff2bffeeffffffffffcc17fffffffffffe997f7bffff3bffefb87ffffff2bfffffffffffffcbffe6fdf65744efc7bfffffffffcafff23fffffd4a3fffffffffffd333f17ffe6ffffff920ffffffffffffffffffffffd44ccfc5fff9bfffffe483ffffa3fffffffb3fffffff5d1ffffe7ffffff6a993fffffe8ffffe8fedfff83ffff4ff23f9ebfff5fffe4fffffffe533ffffb3ffffffffffffffe7afffff4ff93fffffe8fffffffecffffffffffccfff9eb9a5fd3a7f47ffffa25ffffffffffffffffd3fff13ffe6ffffff90dfc8fe8fccfffffffffffffd74ff23ffebfffffffe437ffffa3ffffffffffffffda5d337ffe7fffffffe993ffc8fe8ffffe8fedfff83f6974cd23ffffffffffa64fffffffe273ffffffffffffffffffffffafffde7694a0ffffe88bfffffecfffffffff4bffff3eb7fffddfff83ffffa3f73ffffffffffffffd23ff17fffffff769fe0ffffe8ffffffcffffffdcfff48ffc4fffffffdaa7f83ffffa3ffd4a3fffffffffffffffffffaff8974e9560ffffffffffe8ffffffffffff4cffffffffe2fffa5583f17fffffffff3fff9ff73f53ffc817faff8bf4e94bfffffe8ffffe8ffffe7fdd6954cffc5fffffffffa7f83fffffdbffffffffffffffffd1fffffffdffde77f2bffc8fe8fff528ffffff8bfffffcfffffebfff7bffff45cfffffffd4a3ffffffffdbfd1ffffffffffff76957ffc8fffffffe8feffffffffff47f23ffebffffddfd5fdcffffffffffffffffe2ffffffffffcfadffdefe9491ffffe8ffffffcfffffffffffffffc4ffffff7bfa7f45c23fa3fffffffffffe2fff53f3c8fffafffdeffffd1ffffe8fffffffecfff8bf6ff4bffc5febffffddfff37ffffa3ffffffffffffffdb511ffffffffffff7692bffc8fe8ffffe8feffff83ffd548f2bffebfff79dffffffffffdbfffff3fffffffffffffff13fafffff6a9491fc8fe8fff128cffffffffffffffffffebfdbfdaa5247f17fffffc4a3fbfffffffffd23fffffafffff6a9fc6ffffffffffe8feffe781efff4bf286febffffdafffffffffffffffa33ffffff73ffffffffffafffd74ff57ffc5fffffffe8feffff89cffffff205febfff5d3fffffffffffffffa3fffffe2ffffd33fffffafffd7fe9546ffffffffffe8feffe781dfff4ff206febfffffffd5ffffffffffffff2b3f97f7bfffffc8fcfafffff4fffffffffe8ffffffcffffffde6fffcffc4fffffffffa7f47f23fa3ffc4a33bffffffdb5ffffffffffffff4e9ffffc5ffffff128ffffffffffd74fffff3ffffffffa4a37f23fffffffff2fff97fffffd3fff13ffffffffe928dfc8fe8ffffe8cadfffffffff4ff2bf3ebfffffffff37f17fffffffa3fffffe2fff5d33ffffffffffffe9286ffffffffffe8ffffe7fde6974cffc6fffffffffa4affffffffffffa3fbffffffda5d33caffffffffffe9fc6fc5fff97ffffffffffffffd4ffffff9e39bf79d3a483fffffff73fff0ffffffffffff3bf127ffffde77ffe0fc8ffffdcffffecffffffffffce2059e39bfffffff83fffffe533fffffe8ffffdafffffffff8e6fd7fce93ffff53fffffffc2dffffffffffccfff9e3fff5ffffffff154fffffffffb68fffffffff33f1678ffffffff920fff53ffffffffeca7ffdcffffce23f9e39bffd3ffffffffffe5fffffffe8fff75a53ffc8fff8ffffffce93fffffffffffffc2dffffddffffcefc49e3fffffffff83f23ffff73ffffbbffffffffff37ffe7ffffff75993ffff53ffdcffffecffffffffffcdfff9cbfff7bf67ffffffffff73fffffffffffff53f34bfe7ffffdefd993fffffff97ffffffffff8fffffffffc5fff9bf79d3bf37ffd4fe573ffffffffe3ffffff3bf167ffffdeffffd1ffffff97ffffffffff8fffd4ffffc5fff9bf7bf3a437fffffff73fff0b3ffe0fd9fff3bffe72fffff77fffffffffffdcffffeefff8ff67f44e2ff9ffffffddfe4fffffffffffffffbbffffffffff33ffe7fe6fd7699fc6fff53ffffffffeeffffdcffffcdfc69ff9bffda67fffffd4fffffffffbabffffff5ff33f127fe6ffffd9fd1ffffff94cffffffffffdefffffffc49ff9bffdafff37f23ffe533ffffffffe3ffffffffffe7fe6fff6bf90dfc513ffffffffeca3ffdefd7fcdfff9cb9bffff67ffffffffffffffffbbfffffff5ff33ffe7fffffffd9fc6fff13f94cffffffffffff6bffff2ffffffff5ff3a437f17ffe5ffffffffffe375affffff17ffe6fd7fcefcdffffffffffffc2efff8ff6bffccfff9fffff5ffffffff154ffffd4ff1babfe375afff37f1a7ffffd7ffffffffffff94cffffffaff8deffffff2c5fff9bffd33bf47ffffffffc4ff2bbfffffd9fff3bffe7ffffff4ffffffc5fffffffffcaeaff8de67ffcefc59ffffffd3fff47fffffe5fffffffffffffda5ffffffff2ffffffce90dfc813f97fffffffa3ffff6bfffffc4fff9bffff3bffff23ffe5fffffffffffffda5fffcbffffffffffce93ffc5fff97fffffffaff8de6974ff2c5fff9bffff3bfffffffffffffff2b7fffffff5ff3bffe72fffffffffc6fc813fffffffcada7f81e6bffcefc69cbfffffffffffffffffffc4ff2bbfffffda5d338bfe7fffffffffffffc5ffffdcffffffa3ffffffffcfffffe37fffdd64a83fffffff73fffffe8fffffffff3fffff8fffff759fe0fff13ffdcffffffa3ffffffffcf284fe3ffffdd67f83fffffff73fffffe99ffffffff3c817f8dfffffff4a0ffffff8bfffffeca24ffffffffffc53e37fffffffffffffffe273ffffffffffffffff3fffff8fffde77f2a0fc813f89cfffffffe7fff67ffcffc4fff7ffffffff83f23ffff73ffffbffffffd9fff3cafff8fffff77ffe0fc5ffffdcffffefa67fff67f48f285fffffffddfff83ffffffffffffffe89ffffffff3fffff8c7fff699560fff53ffffffffefa3ffffffffcffc7fe3ffffda67f83ffd4fe2fffff0b3f9bf7ffffffcafcf8fffff6bffffffffffffffffcffa3ffdffd4fcffc7fe3ffffff64a83fffffffffffffbe8fff73f57f3fffff8ffffffd9fe0fff13f8bffffc2dfe6ffffffffffff3fffffffffd5fff214fe2fffff1b7f9bffffffffc8fcf8ffffffff57ffffffffffffffffa27fdd6bf4cfffffff1e25fffd583ffffffffd4fffbff9fffdafd33c81fffffffffff560ffffff8bffffcefa67fdf67ffcf207fe3ffffd3fff83fffffe2fffff0b7f9bffda53fffffcffffffffff2bffc8fff8bffffc7ffe6fdf695fff2bf3e3ffffff3bfffffffffffffff3fff9ff7dafd33ff1ffffffffffffe0fc8fffffffffcefa67fdd6954cf2bfffffffffffff83fffffdb73fffffe8fffffffff3fffff2dfffffd957ffff53ffdcffffffaff8ffffffcfffffff7fffdd6551bfffffdbffffffbbf93fffffffffffcffdffdefd9ffffff13f6fffffc3ffe48fffffffffc43ff7ffffffff37fffffff73fffffe89e0fff53f3fffffffffdefd92bffffffffdcffffffaff8fffd5fcffffffffff7bf67f1bfffffff73fff3feb9e3fff57f3cb1bfffffdefd9fffffffffffffffc3fffffff6fffff2fffffffffdd395fdc17ffffffffffbbf963fffffffff14ffdffdeffffcdfff53ffffffffefa27fff6fffcffc6fff7ffffffd5fdc214fff73ffffbeb9ffffffd13cb1bffdffff77f57fffffffffffffc7fae58fffd4fff2ffffffff7bf392ffffffffffffff3fe9fe2ffffff3ff13fffffdeffffd1708fffffffffcfffff8ff6fffcf2ffffffff7bffd245c17ffff73fff3feb9e3ffffff3cb17ffdffdeffffd1ffffffffffffc2effffff6d5fff2fffffffffdd3bffdc17ffffffffffbfffe2ffffff3fffff2fffde77ffc670813ffdcfffceffff8ff67f48f2fffffffffddfff1bfffffffffffffbe8fe07fffff3fffff2fffd7699ffffffffffffffffffae78dcffffcfffffff1db5da67f1bffffffffffff3beb9e37fffd13cb1fffffffffd9ffffffffffff13ffffae7ffffd7fcfffffff1fffff65247ffffffffffff3feb9e3fff5ff3ff1fffffffffd9491ffffff6fffffcacfe6ffffffffffff3ffffffdafcafff23ffdbffffffbbf93f7bffffffffcffc7fff6bffffffffff6fffffcaefe68dffff4bf2c73ffffffdaffffffffffffffffffbff9e07ff5d13fffffffffff6992bffffffffff13ffefae78defd748fffffffffffff67f1bffffffffffff1bbffff7dbfffffffcfffffd74fffff33ffffffffffcffaff8dc6fffcffffffffff5d3fff47f17fffffd4ff3bebfe37fffff3ff1ffffffd7ffffd1fffffffffffffffffffff6ffffffff3cb1ff5ff395fcc23fffffffff0b7ffe2fffffffff1ffffffd7ffffcdfc853fffffffc3ffe5fdd6fffff2fffffffffff395fcc17ffff33fff1bbf9a37fffd3fcb1ffffffd7ffffcdfffffffffffffffa3f89dfff4cfffffcbfff5fffff1bffffffffffff3bfffe07dafff3ff1ff2fffd7fffffffc8fffffffffcacffffdf6d7ffffc73ffffffd33bffff23ffff33fff2bab9bf7ff5fffcbfcfffffff4ce4bffffffffffffffefa7f89effffcfffffcb1fffd3fff47ffffffffffff3be9fff7d9fff3ff1ffffffff4fffd1fc8fffffffffcffae78de657fcf2fffff1ffffffff47fffffffffffffb6897ffdb5fffffffffffffffce2bffc813ffccfffcaeae4fde697fff2fffffffffff3bffff17ffffffffffbe99ff7bf5d33ffffffc7ffffff286ffffff >>> (174*i)) &&& 0x3fffffffffffffffffffffffffffffffffffffffffff

-- For a left row and residual mask, the six-bit entry names a positive witness.
-- A sentinel of 63 contributes an empty board. Board bits index right rows.
private def flag (i w : Nat) := ((packed (i)) >>> (6*w)) &&& 63
private def contribution (i w : Nat) : Nat :=
  let k := flag i w
  if k < 52 ∧ omittedFlags.testBit k = false ∧
     (positiveWords (k)) &&& ((negativeWords (i)) ||| (mins (w))) = (positiveWords (k))
  then (boards (w)) else 0

private def union (i : Nat) (ws : List Nat) : Nat :=
  ws.foldr (fun w b => contribution i w ||| b) 0

private theorem member {i j : Nat} (ws : List Nat) (yes : (union i ws).testBit j = true) :
    ∃ w ∈ ws, (contribution i w).testBit j = true := by
  induction ws with
  | nil => simp [union] at yes
  | cons w ws ih =>
    change (contribution i w ||| union i ws).testBit j = true at yes
    rw [Nat.testBit_or,Bool.or_eq_true] at yes
    rcases yes with head | tail
    · exact ⟨w,by simp,head⟩
    · obtain ⟨v,hv,on⟩ := ih tail
      exact ⟨v,List.mem_cons_of_mem _ hv,on⟩

set_option maxRecDepth 12000 in
private theorem bits0 : ∀ j : Fin 257, (boards (0)).testBit j.val = true → (mins (0)) &&& (negativeWords (j.val)) = (mins (0)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits1 : ∀ j : Fin 257, (boards (1)).testBit j.val = true → (mins (1)) &&& (negativeWords (j.val)) = (mins (1)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits2 : ∀ j : Fin 257, (boards (2)).testBit j.val = true → (mins (2)) &&& (negativeWords (j.val)) = (mins (2)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits3 : ∀ j : Fin 257, (boards (3)).testBit j.val = true → (mins (3)) &&& (negativeWords (j.val)) = (mins (3)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits4 : ∀ j : Fin 257, (boards (4)).testBit j.val = true → (mins (4)) &&& (negativeWords (j.val)) = (mins (4)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits5 : ∀ j : Fin 257, (boards (5)).testBit j.val = true → (mins (5)) &&& (negativeWords (j.val)) = (mins (5)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits6 : ∀ j : Fin 257, (boards (6)).testBit j.val = true → (mins (6)) &&& (negativeWords (j.val)) = (mins (6)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits7 : ∀ j : Fin 257, (boards (7)).testBit j.val = true → (mins (7)) &&& (negativeWords (j.val)) = (mins (7)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits8 : ∀ j : Fin 257, (boards (8)).testBit j.val = true → (mins (8)) &&& (negativeWords (j.val)) = (mins (8)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits9 : ∀ j : Fin 257, (boards (9)).testBit j.val = true → (mins (9)) &&& (negativeWords (j.val)) = (mins (9)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits10 : ∀ j : Fin 257, (boards (10)).testBit j.val = true → (mins (10)) &&& (negativeWords (j.val)) = (mins (10)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits11 : ∀ j : Fin 257, (boards (11)).testBit j.val = true → (mins (11)) &&& (negativeWords (j.val)) = (mins (11)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits12 : ∀ j : Fin 257, (boards (12)).testBit j.val = true → (mins (12)) &&& (negativeWords (j.val)) = (mins (12)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits13 : ∀ j : Fin 257, (boards (13)).testBit j.val = true → (mins (13)) &&& (negativeWords (j.val)) = (mins (13)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits14 : ∀ j : Fin 257, (boards (14)).testBit j.val = true → (mins (14)) &&& (negativeWords (j.val)) = (mins (14)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits15 : ∀ j : Fin 257, (boards (15)).testBit j.val = true → (mins (15)) &&& (negativeWords (j.val)) = (mins (15)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits16 : ∀ j : Fin 257, (boards (16)).testBit j.val = true → (mins (16)) &&& (negativeWords (j.val)) = (mins (16)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits17 : ∀ j : Fin 257, (boards (17)).testBit j.val = true → (mins (17)) &&& (negativeWords (j.val)) = (mins (17)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits18 : ∀ j : Fin 257, (boards (18)).testBit j.val = true → (mins (18)) &&& (negativeWords (j.val)) = (mins (18)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits19 : ∀ j : Fin 257, (boards (19)).testBit j.val = true → (mins (19)) &&& (negativeWords (j.val)) = (mins (19)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits20 : ∀ j : Fin 257, (boards (20)).testBit j.val = true → (mins (20)) &&& (negativeWords (j.val)) = (mins (20)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits21 : ∀ j : Fin 257, (boards (21)).testBit j.val = true → (mins (21)) &&& (negativeWords (j.val)) = (mins (21)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits22 : ∀ j : Fin 257, (boards (22)).testBit j.val = true → (mins (22)) &&& (negativeWords (j.val)) = (mins (22)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits23 : ∀ j : Fin 257, (boards (23)).testBit j.val = true → (mins (23)) &&& (negativeWords (j.val)) = (mins (23)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits24 : ∀ j : Fin 257, (boards (24)).testBit j.val = true → (mins (24)) &&& (negativeWords (j.val)) = (mins (24)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits25 : ∀ j : Fin 257, (boards (25)).testBit j.val = true → (mins (25)) &&& (negativeWords (j.val)) = (mins (25)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits26 : ∀ j : Fin 257, (boards (26)).testBit j.val = true → (mins (26)) &&& (negativeWords (j.val)) = (mins (26)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits27 : ∀ j : Fin 257, (boards (27)).testBit j.val = true → (mins (27)) &&& (negativeWords (j.val)) = (mins (27)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits28 : ∀ j : Fin 257, (boards (28)).testBit j.val = true → (mins (28)) &&& (negativeWords (j.val)) = (mins (28)) := by decide +kernel
private theorem boardOK (w : Fin 29) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
  match w with
  | ⟨0,_⟩ => exact bits0 j
  | ⟨1,_⟩ => exact bits1 j
  | ⟨2,_⟩ => exact bits2 j
  | ⟨3,_⟩ => exact bits3 j
  | ⟨4,_⟩ => exact bits4 j
  | ⟨5,_⟩ => exact bits5 j
  | ⟨6,_⟩ => exact bits6 j
  | ⟨7,_⟩ => exact bits7 j
  | ⟨8,_⟩ => exact bits8 j
  | ⟨9,_⟩ => exact bits9 j
  | ⟨10,_⟩ => exact bits10 j
  | ⟨11,_⟩ => exact bits11 j
  | ⟨12,_⟩ => exact bits12 j
  | ⟨13,_⟩ => exact bits13 j
  | ⟨14,_⟩ => exact bits14 j
  | ⟨15,_⟩ => exact bits15 j
  | ⟨16,_⟩ => exact bits16 j
  | ⟨17,_⟩ => exact bits17 j
  | ⟨18,_⟩ => exact bits18 j
  | ⟨19,_⟩ => exact bits19 j
  | ⟨20,_⟩ => exact bits20 j
  | ⟨21,_⟩ => exact bits21 j
  | ⟨22,_⟩ => exact bits22 j
  | ⟨23,_⟩ => exact bits23 j
  | ⟨24,_⟩ => exact bits24 j
  | ⟨25,_⟩ => exact bits25 j
  | ⟨26,_⟩ => exact bits26 j
  | ⟨27,_⟩ => exact bits27 j
  | ⟨28,_⟩ => exact bits28 j
  | ⟨a+29,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 29) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 29) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 29) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 29) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 29) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 29) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 29) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 29) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 29) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 29) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 29) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 29) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 29) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 29) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 29) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 29) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 29) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 29) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 29) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 29) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 29) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 29) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 29) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 29) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 29) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 29) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 29) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 29) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 29) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 29) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 29) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 29) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 29) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 29) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 29) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
    match q with
    | ⟨0,_⟩ => exact block0 ⟨r,hr⟩
    | ⟨1,_⟩ => exact block1 ⟨r,hr⟩
    | ⟨2,_⟩ => exact block2 ⟨r,hr⟩
    | ⟨3,_⟩ => exact block3 ⟨r,hr⟩
    | ⟨4,_⟩ => exact block4 ⟨r,hr⟩
    | ⟨5,_⟩ => exact block5 ⟨r,hr⟩
    | ⟨6,_⟩ => exact block6 ⟨r,hr⟩
    | ⟨7,_⟩ => exact block7 ⟨r,hr⟩
    | ⟨8,_⟩ => exact block8 ⟨r,hr⟩
    | ⟨9,_⟩ => exact block9 ⟨r,hr⟩
    | ⟨10,_⟩ => exact block10 ⟨r,hr⟩
    | ⟨11,_⟩ => exact block11 ⟨r,hr⟩
    | ⟨12,_⟩ => exact block12 ⟨r,hr⟩
    | ⟨13,_⟩ => exact block13 ⟨r,hr⟩
    | ⟨14,_⟩ => exact block14 ⟨r,hr⟩
    | ⟨15,_⟩ => exact block15 ⟨r,hr⟩
    | ⟨16,_⟩ => exact block16 ⟨r,hr⟩
    | ⟨17,_⟩ => exact block17 ⟨r,hr⟩
    | ⟨18,_⟩ => exact block18 ⟨r,hr⟩
    | ⟨19,_⟩ => exact block19 ⟨r,hr⟩
    | ⟨20,_⟩ => exact block20 ⟨r,hr⟩
    | ⟨21,_⟩ => exact block21 ⟨r,hr⟩
    | ⟨22,_⟩ => exact block22 ⟨r,hr⟩
    | ⟨23,_⟩ => exact block23 ⟨r,hr⟩
    | ⟨24,_⟩ => exact block24 ⟨r,hr⟩
    | ⟨25,_⟩ => exact block25 ⟨r,hr⟩
    | ⟨26,_⟩ => exact block26 ⟨r,hr⟩
    | ⟨27,_⟩ => exact block27 ⟨r,hr⟩
    | ⟨28,_⟩ => exact block28 ⟨r,hr⟩
    | ⟨29,_⟩ => exact block29 ⟨r,hr⟩
    | ⟨30,_⟩ => exact block30 ⟨r,hr⟩
    | ⟨31,_⟩ => exact block31 ⟨r,hr⟩
    | ⟨32,_⟩ => exact block32 ⟨r,by change r + 256 < 257 at hs; omega⟩
    | ⟨a+33,ha⟩ => omega
  have eq : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [eq] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega)

private theorem positiveRows : ∀ p : Fin 52, (positiveWords (p.val)) = pos p.val := by decide +kernel
private abbrev rowMatches (v : Nat) := (indices (v)) < 468 ∧ (negativeWords (v)) = neg (indices (v))
private theorem negBlock0 : ∀ r : Fin 8, rowMatches (r.val+0) := by decide +kernel
private theorem negBlock1 : ∀ r : Fin 8, rowMatches (r.val+8) := by decide +kernel
private theorem negBlock2 : ∀ r : Fin 8, rowMatches (r.val+16) := by decide +kernel
private theorem negBlock3 : ∀ r : Fin 8, rowMatches (r.val+24) := by decide +kernel
private theorem negBlock4 : ∀ r : Fin 8, rowMatches (r.val+32) := by decide +kernel
private theorem negBlock5 : ∀ r : Fin 8, rowMatches (r.val+40) := by decide +kernel
private theorem negBlock6 : ∀ r : Fin 8, rowMatches (r.val+48) := by decide +kernel
private theorem negBlock7 : ∀ r : Fin 8, rowMatches (r.val+56) := by decide +kernel
private theorem negBlock8 : ∀ r : Fin 8, rowMatches (r.val+64) := by decide +kernel
private theorem negBlock9 : ∀ r : Fin 8, rowMatches (r.val+72) := by decide +kernel
private theorem negBlock10 : ∀ r : Fin 8, rowMatches (r.val+80) := by decide +kernel
private theorem negBlock11 : ∀ r : Fin 8, rowMatches (r.val+88) := by decide +kernel
private theorem negBlock12 : ∀ r : Fin 8, rowMatches (r.val+96) := by decide +kernel
private theorem negBlock13 : ∀ r : Fin 8, rowMatches (r.val+104) := by decide +kernel
private theorem negBlock14 : ∀ r : Fin 8, rowMatches (r.val+112) := by decide +kernel
private theorem negBlock15 : ∀ r : Fin 8, rowMatches (r.val+120) := by decide +kernel
private theorem negBlock16 : ∀ r : Fin 8, rowMatches (r.val+128) := by decide +kernel
private theorem negBlock17 : ∀ r : Fin 8, rowMatches (r.val+136) := by decide +kernel
private theorem negBlock18 : ∀ r : Fin 8, rowMatches (r.val+144) := by decide +kernel
private theorem negBlock19 : ∀ r : Fin 8, rowMatches (r.val+152) := by decide +kernel
private theorem negBlock20 : ∀ r : Fin 8, rowMatches (r.val+160) := by decide +kernel
private theorem negBlock21 : ∀ r : Fin 8, rowMatches (r.val+168) := by decide +kernel
private theorem negBlock22 : ∀ r : Fin 8, rowMatches (r.val+176) := by decide +kernel
private theorem negBlock23 : ∀ r : Fin 8, rowMatches (r.val+184) := by decide +kernel
private theorem negBlock24 : ∀ r : Fin 8, rowMatches (r.val+192) := by decide +kernel
private theorem negBlock25 : ∀ r : Fin 8, rowMatches (r.val+200) := by decide +kernel
private theorem negBlock26 : ∀ r : Fin 8, rowMatches (r.val+208) := by decide +kernel
private theorem negBlock27 : ∀ r : Fin 8, rowMatches (r.val+216) := by decide +kernel
private theorem negBlock28 : ∀ r : Fin 8, rowMatches (r.val+224) := by decide +kernel
private theorem negBlock29 : ∀ r : Fin 8, rowMatches (r.val+232) := by decide +kernel
private theorem negBlock30 : ∀ r : Fin 8, rowMatches (r.val+240) := by decide +kernel
private theorem negBlock31 : ∀ r : Fin 8, rowMatches (r.val+248) := by decide +kernel
private theorem negBlock32 : ∀ r : Fin 1, rowMatches (r.val+256) := by decide +kernel
private theorem negativeRows (i : Fin 257) : rowMatches i.val := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : rowMatches (r+8*q.val) := by
    match q with
    | ⟨0,_⟩ => exact negBlock0 ⟨r,hr⟩
    | ⟨1,_⟩ => exact negBlock1 ⟨r,hr⟩
    | ⟨2,_⟩ => exact negBlock2 ⟨r,hr⟩
    | ⟨3,_⟩ => exact negBlock3 ⟨r,hr⟩
    | ⟨4,_⟩ => exact negBlock4 ⟨r,hr⟩
    | ⟨5,_⟩ => exact negBlock5 ⟨r,hr⟩
    | ⟨6,_⟩ => exact negBlock6 ⟨r,hr⟩
    | ⟨7,_⟩ => exact negBlock7 ⟨r,hr⟩
    | ⟨8,_⟩ => exact negBlock8 ⟨r,hr⟩
    | ⟨9,_⟩ => exact negBlock9 ⟨r,hr⟩
    | ⟨10,_⟩ => exact negBlock10 ⟨r,hr⟩
    | ⟨11,_⟩ => exact negBlock11 ⟨r,hr⟩
    | ⟨12,_⟩ => exact negBlock12 ⟨r,hr⟩
    | ⟨13,_⟩ => exact negBlock13 ⟨r,hr⟩
    | ⟨14,_⟩ => exact negBlock14 ⟨r,hr⟩
    | ⟨15,_⟩ => exact negBlock15 ⟨r,hr⟩
    | ⟨16,_⟩ => exact negBlock16 ⟨r,hr⟩
    | ⟨17,_⟩ => exact negBlock17 ⟨r,hr⟩
    | ⟨18,_⟩ => exact negBlock18 ⟨r,hr⟩
    | ⟨19,_⟩ => exact negBlock19 ⟨r,hr⟩
    | ⟨20,_⟩ => exact negBlock20 ⟨r,hr⟩
    | ⟨21,_⟩ => exact negBlock21 ⟨r,hr⟩
    | ⟨22,_⟩ => exact negBlock22 ⟨r,hr⟩
    | ⟨23,_⟩ => exact negBlock23 ⟨r,hr⟩
    | ⟨24,_⟩ => exact negBlock24 ⟨r,hr⟩
    | ⟨25,_⟩ => exact negBlock25 ⟨r,hr⟩
    | ⟨26,_⟩ => exact negBlock26 ⟨r,hr⟩
    | ⟨27,_⟩ => exact negBlock27 ⟨r,hr⟩
    | ⟨28,_⟩ => exact negBlock28 ⟨r,hr⟩
    | ⟨29,_⟩ => exact negBlock29 ⟨r,hr⟩
    | ⟨30,_⟩ => exact negBlock30 ⟨r,hr⟩
    | ⟨31,_⟩ => exact negBlock31 ⟨r,hr⟩
    | ⟨32,_⟩ => exact negBlock32 ⟨r,by change r + 256 < 257 at hs; omega⟩
    | ⟨a+33,ha⟩ => omega
  have eq : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [eq] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega)

private def idx (i : Fin 257) : Fin 468 := ⟨(indices (i.val)), (negativeRows i).1⟩

private theorem bitLift (p a m b : Bool) (c : (p && (a || m)) = p) (d : (m && b) = m) : (p && (a || b)) = p := by
  cases p <;> cases a <;> cases m <;> cases b <;> simp_all

private theorem retained (i j : Fin 257) (lt : i.val < j.val) :
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
      pos p.val &&& (neg (idx i).val ||| neg (idx j).val) = pos p.val := by
  have full := congrArg (fun x : Nat => x.testBit j.val) (checked i)
  have one : (1 <<< i.val : Nat).testBit j.val = false := by
    rw [Nat.one_shiftLeft,Nat.testBit_two_pow]
    simp [show i.val ≠ j.val by omega]
  have bit : ((2:Nat)^257-1).testBit j.val = true := by
    rw [Nat.testBit_two_pow_sub_one]
    simp [j.isLt]
  simp only [Nat.testBit_or,one,Bool.or_false,bit] at full
  obtain ⟨w,hw,on⟩ := member (List.range 29) full
  let k := flag i.val w
  by_cases ok : k < 52 ∧ omittedFlags.testBit k = false ∧ (positiveWords (k)) &&& ((negativeWords (i.val)) ||| (mins (w))) = (positiveWords (k))
  · simp only [contribution,← show k = flag i.val w from rfl,ite_eq_left ok] at on
    obtain ⟨bound,off,cov⟩ := ok
    let p : Fin 52 := ⟨k,bound⟩
    have sub := boardOK ⟨w,List.mem_range.mp hw⟩ j on
    refine ⟨p,off,?_⟩
    change pos p.val &&& (neg (indices (i.val)) ||| neg (indices (j.val))) = pos p.val
    rw [← positiveRows p,← (negativeRows i).2,← (negativeRows j).2]
    apply Nat.eq_of_testBit_eq
    intro b
    have c := congrArg (fun t : Nat => t.testBit b) cov
    have d := congrArg (fun t : Nat => t.testBit b) sub
    simp only [Nat.testBit_and,Nat.testBit_or] at c d ⊢
    change ((positiveWords (k)).testBit b && ((negativeWords (i.val)).testBit b || (negativeWords (j.val)).testBit b)) = (positiveWords (k)).testBit b
    exact bitLift _ _ _ _ c d
  · simp only [contribution,← show k = flag i.val w from rfl,ite_eq_right ok,Nat.zero_testBit] at on
    contradiction

def ix (i : Fin 257) := indices i.val
theorem neg_match (i : Fin 257) : ix i < 468 := (negativeRows i).1
theorem pairGuard (i j : Fin 257) (lt : i < j) :
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
      pos p.val &&& (neg (ix i) ||| neg (ix j)) = pos p.val := retained i j lt
def initial : List Column := List.ofFn (fun k : Fin 28 => input k.val)

theorem initial_good (p : Fin 52) (a b : Fin 468)
    (h : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ initial, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hw
  have e := congrArg (fun x : Nat => x.testBit k.val) h
  simp only [Nat.testBit_and,Nat.testBit_or] at e
  intro hp
  have yes : (pos p.val).testBit k.val = true := by simpa [input,p.isLt] using hp
  rw [yes,Bool.true_and,Bool.or_eq_true] at e
  simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using e
def c := mix true (input 15) (input 27)
def d := mix true (input 17) (input 26)
def base (i : Fin 30) : Column :=
  if i.val < 28 then input i.val else if i.val = 28 then c else d

end PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthGuard


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthTransport
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape (input mix pos neg extend)
-- Each triple selects part of a word and shifts it to its new coordinates.
private def permute : List (Nat × Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (mask,l,r)::tail, x => (((x &&& mask) <<< l) >>> r) ||| permute tail x
private def segments : Array (List (Nat × Nat × Nat)) := #[[(0x1ffefff,1,0), (0x2001000,0,12)], [(0x2001,0,0), (0x4002,2,0), (0x8004,4,0), (0x10008,6,0), (0x20010,8,0), (0x40020,0,3), (0x80040,0,1), (0x100080,1,0), (0x200100,3,0), (0x400200,0,8), (0x800400,0,6), (0x1000800,0,4), (0x2001000,0,2)], [(0x68220b,0,0), (0x8024,5,0), (0x10,7,0), (0x140140,0,4), (0x10080,0,1), (0x800400,2,0), (0x800,0,3), (0x1000,0,7), (0x4000,10,0), (0x20000,6,0), (0x1000000,0,6), (0x2000000,0,8)]]
private def act (g : Fin 3) (x : Nat) := extend (permute segments[g.val]! x)
private theorem permJoin (s : List (Nat × Nat × Nat)) (x y : Nat) :
    permute s (x ||| y) = permute s x ||| permute s y := by
  induction s with
  | nil => simp [permute]
  | cons h t ih =>
    rcases h with ⟨m,l,r⟩
    simp only [permute,Nat.and_or_distrib_right,Nat.shiftLeft_or_distrib,Nat.shiftRight_or_distrib,ih]
    ac_rfl
private def Hom (f : Nat → Nat) := ∀ x y, f (x ||| y) = f x ||| f y
private theorem glue {f g : Nat → Nat} (hf : Hom f) (hg : Hom g) : Hom (fun v => f v ||| g v) := by
  intro x y
  change f _ ||| g _ = (f x ||| g x) ||| (f y ||| g y)
  rw [hf,hg]
  ac_rfl
private theorem pushed {f : Nat → Nat} (h : Hom f) (k : Nat) : Hom (fun v => f v <<< k) := by
  intro x y
  exact (congrArg (fun z => z <<< k) (h x y)).trans Nat.shiftLeft_or_distrib
private theorem bitHom (k : Nat) : Hom (fun x => (x >>> k) &&& 1) := by
  intro x y
  simp only [Nat.shiftRight_or_distrib,Nat.and_or_distrib_right]
private theorem extendJoin : Hom extend :=
  glue (glue (fun _ _ => rfl) (pushed (glue (bitHom 0) (bitHom 1)) 26))
    (pushed (glue (bitHom 3) (bitHom 9)) 27)
private theorem join (g : Fin 3) (x y : Nat) : act g (x ||| y) = act g x ||| act g y := by
  exact (congrArg extend (permJoin _ x y)).trans (extendJoin _ _)

private def pm : Array Nat := #[0x3081c33cb1beeb6ca2baa99e69648e28607de75c6da6585d65544134913ce34c2ca2481c6144, 0xaaba687dd79c4d14901c6105b6cbaf8238625175562ca209cb1cf09a49e56986d934f38c043080, 0x4914d0557594cb3c709279668628233cd38c6d961a1851c4a6aae82882c979f71dbeeb6c0c2040]
private def nm : Array Nat := #[0xe5f1f89bcdce6f2b91c7e370d84c1602fd75b9dc6db6bb2d8ec15aac55ead52a752e87409c4c25b2a93c7a39198842e13067fbf1f2f579badcce471379aed4693419cca61afd7abb5bad158aa54a9d4c9348231007d3e1e8f075399c8e06f34990c4572a1449c4d259249046229087a3b1c0c45a2b1409848210f87436190b85428130903c160903818080300803a7d2e8f439fcee6f3395c9e471b8bc3e170781bfdf6f777badc6df6db5da6cf65b1d86bf5dadd66af55a9d469f4da5d268f45a1d067f3d9dce66b3398cbe5b2993c96431d8cc5e2b1388c3e170781bfdf6f97bbd5e6f177bb5d2e570b7dbad96ab4da2cf66b258ac35faf576b95bacd56a953a8d429f4da652a9348a3d1a8b44a15067f3e9ecf2773a9ccde6d359a4ce653197cba592b94ca24d259248e45219047e3b1b8d4622f168ac52271288c3e1d0d8642a110782c12070280c01fcfd7dbe9f0f77b3d1e4f1783bddced763a9d2e873b95c6e17037dbadc6db69b2d86b355a6d167b3598cb64b218ec662b1184c1602f978ba5cae16cb559ac962b057ab95aab5429548a351285409f4f275389b4d26530974b255289248a3d1c8d45a29128843a190a8441a09027f3f1ecf2773b1d0e26e369b0d66a3419ccc6531984c05f2f174b85b2d164b0562a94ca4502793094472210c82401f8f8783a1c8dc6c351a0cc6430178b8582a1489c4a23110803c1c0d0602c11080381a0c050200a02, 0x703318ec863543a74fa7535c2df6f37596ca64eb59ec4d7ebb58ce66b1587465d2c582afa4d4e8f456cbc5b8d55cb0966b0773a5d0c0597429944a0b6362db6934571a95aab952a8d368d7abc562ad4dd1aa523a5cfaad4aa34ba550e85407935dadb8d9ecb60f077b69a8d3686a96eb6db6a1d6ea5a6d74fa476b9dc8e35faf95aa7dbed357a576399cae25daa8722fbd0b4586a529a4d03a1c0def62ecedf2f2914823c602b9444f911588998d864318d08636190a6f175ba1007a3c150a27f2993c9a2f3a8c45b93398971f8d389bc5220a33699548a2371acce62220cd309449a4884411a8c739764b2347d9ecde6aff7ebeddee6974aa39183f1dbf77d317d5a44e1003017275c441e8f21b0d00e43cd9ec7a3bc282c137f007e3ef7b3097bfdfcf93095cad892e93499a2c66213c5c25dcad56813094241107d7eba200e8701004cc64adf6eaf2250e7c3d9e03e1e0c81f993c91c6a5cf87a6ea692b8641dec525017c9e9b2411f4182c0a64b0450702b2d66b0a2d027e11030ee7238808018fc756ab35642a08ea743785c2c1300cfa4b208ff3b97ca9dc92451c8dc67830f81c078bc09b4ca1d02de6ee6b2d9643613087bbcf89c3dccce550b85419ea602a944a0a14f978a853276870f84c1a75345b2c9288d9fc5e2b0d85c0270b449b3d8ec424118341399cae52e370b2d92c08a401fcfa2105e47215baba190676380602997c6db6d96bac210e615, 0xb55cad3c2b4185b3212b9587505090444e2612ae872106652572381bc101fa2cc64f3b92c66279b88b7d7ef95eb75eb7d5cbdefebb79debc54b3d4f225d2913e1ed10ee43cc4f479a9ba1208f984bcf0dc2e971c0d53513498693447a3a4b1007c3cb36451d6500040c1fefe03b04361a613003a1c0cac68caf17bf40c05168b1f40363ac18d45173f1f60415be73396db6572966b3d96c9c5b8dc35361d574751c1b1d8b816050a81e53e4fa0528803fa2d3136451faa8eb754e92692991f4ab202a14cbe6092979b05227b5dac512847c9c0e1b032060d8c0d6040b21888890f1208c84418708570b51a02864cb5badaa0ca64d21691719c04131618e8371a1cfedf3d97c7e3b6bb4ce647219bcd63717b2c3e1b0bb3e762b63ccc16076184c1f2f9580bfdb6d9a6bc56ab3a7d7696b777ac6bfa5abbf5f789c3b5f4347c8badd37556d6e93a7ace7f26edbcddd5f8fc6b9ee5e09d52271373c4cbbd469a9fa8a76854325d08773a9d1cee6729d91c739a209db557625a6a834acce5c7238cacdee471d4aa2e29ca365b2c384e26e8c9516cdd242d37da8d3254a4cf1c8d925b66c91961c2da36964d72269344cc4823ca0c8638d115bcdd681948d279318a32408605c2d0d0c0fe170a0aaba88ac55be00515153d802ada7b168742553de28f5a62f5783d1e41c26cf5faf99ccda5d29763e84c20283b832a551415344c52f40044450c453d3a9ac3a0449e710]
private def lm : Array Nat := #[0xcba987654321, 0xa741b852c9630, 0x45c98361a27b0]
private def imageP (g : Fin 3) (p : Fin 52) : Fin 52 :=
  Fin.ofNat 52 (((pm[g.val]! >>> (6*p.val)) &&& 63))
private def imageN (g : Fin 3) (n : Fin 468) : Fin 468 :=
  Fin.ofNat 468 (((nm[g.val]! >>> (9*n.val)) &&& 511))
private def line (g : Fin 3) (a : Nat) := (lm[g.val]! >>> (4*a)) &&& 15
set_option maxRecDepth 16000 in
private theorem posOK : ∀ (g : Fin 3) (p : Fin 52), pos (imageP g p).val = act g (pos p.val) ∧
    (imageP g p).val / 4 = line g (p.val/4) := by decide +kernel
private def nw (i : Fin 468) := (0xb900230b880038b840218b804228b800238b280428b220448b2040683202460b200468b108250b1042603102070b100270b0c04183082430b080438b060608b048610b040618b028640b024248b020648300a450b008650b0042683002470ee0008aec8001aac400986c08092ec0009aea8002a6a100a2aa040a8ea000aa6980032e910222e908212e900232e88003aa848290a844288a840298e818282a8142a0e8102a2e808292a8042a8e62004a66080c2a6040c8e6000ca65808126520842650805225028506500852a4c0818e4a080ae48081aa4448882442890a440898a424848e42084a240a0d064080d224068c0a4048c824028d0e2a040a6290422e28042a6228442e22044a621848222124a062104a2220a4c062084c222060e0a2040e822024e0619082221828306180832e130a02e128242a124a40e120a42a114a20e110a22e1082522106860a104a602102870a0e0c0820c2c10a0c0c1860b0c02e0a0c0a2092c206090c222082c30a070e00a064a08a060e08a058680a054a802052c80a050e80204a490a048690a044a882042c90e038602e030e02e028642a024a48e01868220168a0a014aa02012ca0200a4d020068e09c801189c4001c9c2010c1c021149c0011c9940214991022419020349900234988412818821309880138986020c984021c98303049824308982030c981432018121249810324980432818021345700045d64000d962004cd604049d60004d5540015550805115020545500055d4c00195488111d484109d480119d44001d94241481422144942014c540c141140a1505408151d40414914021545310025530406113020645300065d2c04095290421d284029d280429926040c5250405d24040d1222444922044c12124245210425d2040691202464d150205d148211d140215d114221d110225d10c241d108251d104261110207450c8411d0c04195098501509412110925205090521108a5105088511d08412910825309070604906060cd058601d050605d048611903870010325049030704902c340102a540902874090243481022544d01c301d018701d0143211012524d00c341100a5508e4008cce2000e4e10086ce0008ecca010a4c88112cc8011a0c420948c4009c4c30106cc2010e4c181820c121844c101860c0a1904c081920c021944b810224b210064b100260b030244b01026caa100a8a85028ca8102a8a6100c8a450880a430848a4108cca2100e0a120a44a100a60a070a08a050a80a030a44989012098303049810328961204894921009430148941214c930206c929202c921206c910226c909212090303448a910288a5108c8a110a088b11048891120887120888512808831308865208886120c884d280084b090884929088452880843094c838302c830306882d300c8293028825308881c380c81838208161a088143a008121a4080f180880d380080b19008071a047200464710007470804347000474650085c644089c64008dc62004e46180834610087460c0c146080c3c6040c945c0811459080345880134580813455080505428144540815453080605228444520846451080745080530502854c4c4809c4c081944b090284a4908c4a090a4498103449490144909034488113c484909445488104528844450885c444889044289404329044430906042694084249480422944441c1814418183041698044149810412984040e1c0440c1c1040a1d004069c043900234389003438502143810234329042032304443210464310027430d041430904303070604305061030306482e140842c9401c2c5009c2c140942a9402c2a140a429840342904234289403c2850290263404826140c425848102524844250485424d081024b4804249481c2450890243484022b44042294420223444421848302124a4020f0c0420d0c1020b4c002070e041c901141c580101c381041c18114194821419082341890130187820418582101838308170a048165a0001638048161a04c154a01c150a05c14d201c149211c145a010143814c130a06812d240c12924201278408125a400123844c114a21c10d241010786080e580800e3c0080e1c0800cb41040c9411c0c580900c3c1040b850200b2d0040b0d0200ab50040a950200a790080a590800a3d004098503009692040949210092d20008b51000879200072c048070e048065a080063c04c05c281c058681c054a810052c84c04d281004b490c0387020032d04002f140802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i.val)) &&& 0xfffffff
set_option maxRecDepth 8192 in
private theorem original : ∀ i : Fin 468, nw i = neg i.val := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
private theorem n0 (n : Fin 468) : nw (imageN 0 n) = act 0 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n1b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
private theorem n1 (n : Fin 468) : nw (imageN 1 n) = act 1 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n2b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
private theorem n2 (n : Fin 468) : nw (imageN 2 n) = act 2 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b442 j
  omega
private theorem negOK (g : Fin 3) (n : Fin 468) : neg (imageN g n).val = act g (neg n.val) := by
  rw [←original,←original n]
  match g with
  | ⟨0,_⟩ => exact n0 n
  | ⟨1,_⟩ => exact n1 n
  | ⟨2,_⟩ => exact n2 n
  | ⟨m+3,hm⟩ => omega
def W (m : Nat) := ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, m.testBit p.val = false ∧
      pos p.val ||| (neg (f i).val ||| neg (f j).val) = neg (f i).val ||| neg (f j).val
private theorem hop (a b : Nat) (g : Fin 3) (old : W a)
    (perm : ∀ p : Fin 52, a.testBit p.val = false → b.testBit (imageP g p).val = false) : W b := by
  obtain ⟨f,h⟩ := old
  refine ⟨fun i => imageN g (f i),?_⟩
  intro i j lt
  obtain ⟨p,off,ok⟩ := h i j lt
  exact ⟨imageP g p,perm p off,by simpa only [(posOK g p).1,negOK,join] using congrArg (act g) ok⟩
private def masks : Array Nat := #[4406657483279, 282031175959056, 565432176148992, 2326566607454784, 36284958458400, 2199434366752, 9835609424384, 35734161526564, 140771919466244, 74766807543560, 4292495550784000, 26663225074176, 1125934333763330, 16498077794816, 140871706149440, 4316922497]
private def slot : Array (Fin 16) := #[0, 0, 0, 0, 1, 4, 3, 15, 5, 0, 5, 5, 12, 9, 4, 6, 0, 1, 1, 1, 13, 3, 0, 5, 0, 7, 8, 5, 2, 2, 2, 1, 1, 0, 14, 8, 6, 6, 2, 1, 4, 2, 0, 6, 11, 4, 3, 8, 1, 2, 10, 3]
private def mask (k : Fin 16) := masks[k.val]!
private theorem h0 (first : W 4406657483279) : W 2252903955824687 :=
  hop 4406657483279 2252903955824687 2 first (by decide +kernel)
private theorem h1 (first : W 4406657483279) : W 17666274231025 :=
  hop 2252903955824687 17666274231025 0 (h0 first) (by decide +kernel)
private theorem h2 (first : W 4406657483279) : W 140772250808353 :=
  hop 17666274231025 140772250808353 1 (h1 first) (by decide +kernel)
private theorem h3 (first : W 4406657483279) : W 282031175959056 :=
  hop 140772250808353 282031175959056 0 (h2 first) (by decide +kernel)
private theorem h4 (first : W 4406657483279) : W 70506519732464 :=
  hop 4406657483279 70506519732464 0 first (by decide +kernel)
private theorem h5 (first : W 4406657483279) : W 567481004560 :=
  hop 70506519732464 567481004560 1 (h4 first) (by decide +kernel)
private theorem h6 (first : W 4406657483279) : W 17678353846080 :=
  hop 567481004560 17678353846080 2 (h5 first) (by decide +kernel)
private theorem h7 (first : W 4406657483279) : W 17678605516832 :=
  hop 17678353846080 17678605516832 1 (h6 first) (by decide +kernel)
private theorem h8 (first : W 4406657483279) : W 565432176148992 :=
  hop 17678605516832 565432176148992 0 (h7 first) (by decide +kernel)
private theorem h9 (first : W 4406657483279) : W 264020271568912 :=
  hop 70506519732464 264020271568912 2 (h4 first) (by decide +kernel)
private theorem h10 (first : W 4406657483279) : W 4226523368423680 :=
  hop 264020271568912 4226523368423680 0 (h9 first) (by decide +kernel)
private theorem h11 (first : W 4406657483279) : W 2268575990677504 :=
  hop 4226523368423680 2268575990677504 1 (h10 first) (by decide +kernel)
private theorem h12 (first : W 4406657483279) : W 2326566607454784 :=
  hop 2268575990677504 2326566607454784 1 (h11 first) (by decide +kernel)
private theorem h13 (first : W 4406657483279) : W 351843859432463 :=
  hop 4406657483279 351843859432463 1 first (by decide +kernel)
private theorem h14 (first : W 4406657483279) : W 2251802030391538 :=
  hop 351843859432463 2251802030391538 0 (h13 first) (by decide +kernel)
private theorem h15 (first : W 4406657483279) : W 263882824515970 :=
  hop 2251802030391538 263882824515970 2 (h14 first) (by decide +kernel)
private theorem h16 (first : W 4406657483279) : W 4222125191796768 :=
  hop 263882824515970 4222125191796768 0 (h15 first) (by decide +kernel)
private theorem h17 (first : W 4406657483279) : W 36284958458400 :=
  hop 4222125191796768 36284958458400 2 (h16 first) (by decide +kernel)
private theorem h18 (first : W 4406657483279) : W 8798383177775 :=
  hop 351843859432463 8798383177775 2 (h13 first) (by decide +kernel)
private theorem h19 (first : W 4406657483279) : W 281479273269263 :=
  hop 8798383177775 281479273269263 1 (h18 first) (by decide +kernel)
private theorem h20 (first : W 4406657483279) : W 68745199858 :=
  hop 281479273269263 68745199858 0 (h19 first) (by decide +kernel)
private theorem h21 (first : W 4406657483279) : W 2199434366752 :=
  hop 68745199858 2199434366752 0 (h20 first) (by decide +kernel)
private theorem h22 (first : W 4406657483279) : W 145152723206159 :=
  hop 2252903955824687 145152723206159 1 (h0 first) (by decide +kernel)
private theorem h23 (first : W 4406657483279) : W 352118734586096 :=
  hop 145152723206159 352118734586096 0 (h22 first) (by decide +kernel)
private theorem h24 (first : W 4406657483279) : W 1126999956451904 :=
  hop 352118734586096 1126999956451904 1 (h23 first) (by decide +kernel)
private theorem h25 (first : W 4406657483279) : W 9835609424384 :=
  hop 1126999956451904 9835609424384 1 (h24 first) (by decide +kernel)
private theorem h26 (first : W 4406657483279) : W 299138029848591 :=
  hop 145152723206159 299138029848591 1 (h22 first) (by decide +kernel)
private theorem h27 (first : W 4406657483279) : W 565183338545394 :=
  hop 299138029848591 565183338545394 0 (h26 first) (by decide +kernel)
private theorem h28 (first : W 4406657483279) : W 35734161526564 :=
  hop 565183338545394 35734161526564 0 (h27 first) (by decide +kernel)
private theorem h29 (first : W 4406657483279) : W 2256203245948672 :=
  hop 70506519732464 2256203245948672 0 (h4 first) (by decide +kernel)
private theorem h30 (first : W 4406657483279) : W 708120104009728 :=
  hop 2256203245948672 708120104009728 1 (h29 first) (by decide +kernel)
private theorem h31 (first : W 4406657483279) : W 2289185372374016 :=
  hop 708120104009728 2289185372374016 1 (h30 first) (by decide +kernel)
private theorem h32 (first : W 4406657483279) : W 571748198416624 :=
  hop 2289185372374016 571748198416624 2 (h31 first) (by decide +kernel)
private theorem h33 (first : W 4406657483279) : W 140771919466244 :=
  hop 571748198416624 140771919466244 0 (h32 first) (by decide +kernel)
private theorem h34 (first : W 4406657483279) : W 1383114678528 :=
  hop 567481004560 1383114678528 0 (h5 first) (by decide +kernel)
private theorem h35 (first : W 4406657483279) : W 26527881498624 :=
  hop 1383114678528 26527881498624 0 (h34 first) (by decide +kernel)
private theorem h36 (first : W 4406657483279) : W 1130435393389296 :=
  hop 26527881498624 1130435393389296 2 (h35 first) (by decide +kernel)
private theorem h37 (first : W 4406657483279) : W 74766807543560 :=
  hop 1130435393389296 74766807543560 0 (h36 first) (by decide +kernel)
private theorem h38 (first : W 4406657483279) : W 298522372999168 :=
  hop 1383114678528 298522372999168 2 (h34 first) (by decide +kernel)
private theorem h39 (first : W 4406657483279) : W 141845659058304 :=
  hop 298522372999168 141845659058304 1 (h38 first) (by decide +kernel)
private theorem h40 (first : W 4406657483279) : W 4292495550784000 :=
  hop 141845659058304 4292495550784000 1 (h39 first) (by decide +kernel)
private theorem h41 (first : W 4406657483279) : W 2252899880010767 :=
  hop 351843859432463 2252899880010767 1 (h13 first) (by decide +kernel)
private theorem h42 (first : W 4406657483279) : W 17601061208305 :=
  hop 2252899880010767 17601061208305 0 (h41 first) (by decide +kernel)
private theorem h43 (first : W 4406657483279) : W 263887153795329 :=
  hop 17601061208305 263887153795329 2 (h42 first) (by decide +kernel)
private theorem h44 (first : W 4406657483279) : W 4222194460790800 :=
  hop 263887153795329 4222194460790800 0 (h43 first) (by decide +kernel)
private theorem h45 (first : W 4406657483279) : W 26663225074176 :=
  hop 4222194460790800 26663225074176 2 (h44 first) (by decide +kernel)
private theorem h46 (first : W 4406657483279) : W 1162183924809807 :=
  hop 8798383177775 1162183924809807 2 (h18 first) (by decide +kernel)
private theorem h47 (first : W 4406657483279) : W 1143494240437496 :=
  hop 1162183924809807 1143494240437496 0 (h46 first) (by decide +kernel)
private theorem h48 (first : W 4406657483279) : W 290275649974274 :=
  hop 1143494240437496 290275649974274 1 (h47 first) (by decide +kernel)
private theorem h49 (first : W 4406657483279) : W 1125934333763330 :=
  hop 290275649974274 1125934333763330 2 (h48 first) (by decide +kernel)
private theorem h50 (first : W 4406657483279) : W 266631712407568 :=
  hop 352118734586096 266631712407568 2 (h23 first) (by decide +kernel)
private theorem h51 (first : W 4406657483279) : W 4258410817126656 :=
  hop 266631712407568 4258410817126656 0 (h50 first) (by decide +kernel)
private theorem h52 (first : W 4406657483279) : W 16498077794816 :=
  hop 4258410817126656 16498077794816 1 (h51 first) (by decide +kernel)
private theorem h53 (first : W 4406657483279) : W 145136104244226 :=
  hop 263882824515970 145136104244226 2 (h15 first) (by decide +kernel)
private theorem h54 (first : W 4406657483279) : W 10758524676 :=
  hop 145136104244226 10758524676 1 (h53 first) (by decide +kernel)
private theorem h55 (first : W 4406657483279) : W 8804481663012 :=
  hop 10758524676 8804481663012 2 (h54 first) (by decide +kernel)
private theorem h56 (first : W 4406657483279) : W 140871706149440 :=
  hop 8804481663012 140871706149440 0 (h55 first) (by decide +kernel)
private theorem h57 (first : W 4406657483279) : W 281477191581727 :=
  hop 2252899880010767 281477191581727 2 (h41 first) (by decide +kernel)
private theorem h58 (first : W 4406657483279) : W 564122487885839 :=
  hop 281477191581727 564122487885839 1 (h57 first) (by decide +kernel)
private theorem h59 (first : W 4406657483279) : W 19860063125748 :=
  hop 564122487885839 19860063125748 0 (h58 first) (by decide +kernel)
private theorem h60 (first : W 4406657483279) : W 2251800083492904 :=
  hop 19860063125748 2251800083492904 1 (h59 first) (by decide +kernel)
private theorem h61 (first : W 4406657483279) : W 4316922497 :=
  hop 2251800083492904 4316922497 0 (h60 first) (by decide +kernel)
private theorem allMasks (first : W 4406657483279) (k : Fin 16) : W (mask k) := by
  match k with
  | ⟨0,_⟩ => exact first
  | ⟨1,_⟩ => exact h3 first
  | ⟨2,_⟩ => exact h8 first
  | ⟨3,_⟩ => exact h12 first
  | ⟨4,_⟩ => exact h17 first
  | ⟨5,_⟩ => exact h21 first
  | ⟨6,_⟩ => exact h25 first
  | ⟨7,_⟩ => exact h28 first
  | ⟨8,_⟩ => exact h33 first
  | ⟨9,_⟩ => exact h37 first
  | ⟨10,_⟩ => exact h40 first
  | ⟨11,_⟩ => exact h45 first
  | ⟨12,_⟩ => exact h49 first
  | ⟨13,_⟩ => exact h52 first
  | ⟨14,_⟩ => exact h56 first
  | ⟨15,_⟩ => exact h61 first
  | ⟨a+16,ha⟩ => omega
private theorem covers : ∀ u : Fin 52, let m := mask (slot[u.val]!)
    m.testBit 9 = true ∧ m.testBit 16 = true ∧ m.testBit u.val = true := by decide +kernel
end PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthTransport
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthTransport PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape in
theorem PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthTransport : W 4406657483279 → ∀ u : Fin 52,
    ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, p.val ≠ 9 ∧ p.val ≠ 16 ∧ p ≠ u ∧
      pos p.val ||| (neg (f i).val ||| neg (f j).val) = neg (f i).val ||| neg (f j).val := by
  intro first u
  obtain ⟨f,h⟩ := allMasks first (slot[u.val]!)
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,off,cov⟩ := h i j lt
  obtain ⟨a,b,c⟩ := covers u
  exact ⟨p,by rintro e; rw [e,a] at off; contradiction,
    by rintro e; rw [e,b] at off; contradiction,
    by rintro rfl; rw [c] at off; contradiction,cov⟩


namespace PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35EveryFifthAndBudget
open PlaneFirstAndSeparation PlaneFirstAndBudget
open PlaneCase35FifthAndShape (input mix pos neg extend)
open PlaneCase35FifthGuard
private def Cov (p : Fin 52) (a b : Fin 468) :=
  pos p.val &&& (neg a.val ||| neg b.val) = pos p.val
private def Pair (p : Fin 52) (a b : Fin 468) :=
  p.val ≠ 9 ∧ p.val ≠ 16 ∧ Cov p a b
private def G (w : Column) (p : Fin 52) (a b : Fin 468) :=
  good p.val (52+a.val) (52+b.val) w
private def Cert (e : Column) :=
  ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, Pair p (f i) (f j) ∧ G e p (f i) (f j)
private theorem toJoin (x y : Nat) : x &&& y = x ↔ x ||| y = y := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
    have e := congrArg (fun v : Nat => v.testBit k) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and] at e ⊢ <;>
    cases ex : x.testBit k <;> cases ey : y.testBit k <;> simp_all
private theorem first : PlaneCase35FifthTransport.W 4406657483279 := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j lt
  obtain ⟨p,h,cov⟩ := pairGuard i j lt
  exact ⟨p,h,(toJoin _ _).mp cov⟩
private theorem single (u : Fin 52) : ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, Pair p (f i) (f j) ∧ p ≠ u := by
  obtain ⟨f,h⟩ := PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthTransport first u
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,h1,h2,h3,h4⟩ := h i j lt
  exact ⟨p,⟨h1,h2,(toJoin _ _).mpr h4⟩,h3⟩
private theorem seedOff : ∀ p : Fin 52, omittedFlags.testBit p.val = false →
    p.val ≠ 9 ∧ p.val ≠ 16 ∧ p.val ≠ 0 ∧ p.val ≠ 1 ∧ p.val ≠ 2 ∧ p.val ≠ 3 := by decide +kernel
private theorem cdOff : ∀ p : Fin 52, p.val ≠ 9 → p.val ≠ 16 →
    c p.val = false ∧ d p.val = false := by decide +kernel
private theorem raw (k : Fin 30) {p a b} (h : Pair p a b) : G (base k) p a b := by
  obtain ⟨h1,h2,h3⟩ := h
  by_cases lt : k.val < 28
  · have mem : input k.val ∈ initial := List.mem_ofFn.mpr ⟨(⟨k.val,lt⟩ : Fin 28),rfl⟩
    simpa [base,lt,G] using initial_good p a b h3 (input k.val) mem
  · obtain ⟨hc,hd⟩ := cdOff p h1 h2
    by_cases eq : k.val = 28 <;> simp [base,lt,eq,G,good,hc,hd]
private theorem inherit (e : Column) (h : ∀ p a b, Pair p a b → G e p a b) : Cert e := by
  obtain ⟨f,hf⟩ := single 0
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,hp,_⟩ := hf i j lt
  exact ⟨p,hp,h _ _ _ hp⟩
private theorem sparse (e : Column)
    (support : ∀ p : Fin 52, e p.val = true → p.val < 4) : Cert e := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j lt
  obtain ⟨p,off,cov⟩ := pairGuard i j lt
  obtain ⟨a,b,h0,h1,h2,h3⟩ := seedOff p off
  refine ⟨p,⟨a,b,cov⟩,?_⟩
  intro on
  have := support p on
  omega
private theorem verified (op : Bool) (a b : Fin 30) : Cert (mix op (base a) (base b)) := by
  cases op
  · apply inherit
    intro p x y hp on
    rcases Bool.or_eq_true_iff.mp on with h | h
    · rcases raw a hp h with h | h <;> simp [mix,h]
    · rcases raw b hp h with h | h <;> simp [mix,h]
  · rcases PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape a b with ha | hb | ⟨u,hu⟩ | h | h
    · apply inherit; intro p x y h
      have eq : mix true (base a) (base b) = base a := funext ha
      rw [eq]; exact raw a h
    · apply inherit; intro p x y h
      have eq : mix true (base a) (base b) = base b := funext hb
      rw [eq]; exact raw b h
    · obtain ⟨f,hf⟩ := single u
      refine ⟨f,?_⟩
      intro i j lt
      obtain ⟨p,hp,ne⟩ := hf i j lt
      exact ⟨p,hp,fun on => False.elim (ne (hu p on))⟩
    · apply sparse; intro p hp; rcases h p hp with h | h <;> omega
    · apply sparse; intro p hp; rcases h p hp with h | h <;> omega
end PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35EveryFifthAndBudget
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35FifthDirect.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthGuard
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35FifthAndShape (mix)
open PEqualNP.Research.PlaneCase35FifthDirect.PlaneCase35EveryFifthAndBudget in
theorem PEqualNP.Research.PlaneCase35FifthDirect : ∀ (op : Bool) (a b : Fin 30) (gs : List Gate) (o : Nat),
    let e := mix op (base a) (base b)
    let pool := (initial ++ [c,d,e]) ++ [fun _ => false, fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro op a b gs o e pool hp hn
  apply separated_bound _ gs o _ hp hn
  obtain ⟨f,hf⟩ := verified op a b
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,hp,he⟩ := hf i j lt
  obtain ⟨h9,h16,cov⟩ := hp
  obtain ⟨hc,hd⟩ := cdOff p h9 h16
  refine ⟨p,?_⟩
  intro v hv
  rcases List.mem_append.mp hv with prev | con
  · rcases List.mem_append.mp prev with raw | ext
    · exact initial_good p _ _ cov v raw
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ext
      rcases ext with rfl | rfl | rfl
      · simp [good,hc]
      · simp [good,hd]
      · exact he
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at con
    rcases con with rfl | rfl <;> simp [good]
