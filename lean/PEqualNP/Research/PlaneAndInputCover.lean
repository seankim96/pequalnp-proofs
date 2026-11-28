import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

namespace PEqualNP.Research.PlaneAndInputCover
open PEqualNP.CircuitLowerBounds

def gateValue (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => w.getD i false))
def addGate (w : List Bool) (g : Gate) := w ++ [gateValue w g]
private def mix (p a b : List Bool) := ∀ i, p.getD i false = true →
  a.getD i false = true ∨ b.getD i false = true
def covers {m : Nat} (pick : Fin m → Nat) (gs : List Gate) :=
  ∀ g ∈ gs, ∀ i j, g.op = .and → g.inputs = [i,j] → i ≠ j →
    ∃ k, pick k = i ∨ pick k = j
private theorem old_wire (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (gs.foldl addGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons t ts ih =>
    change (ts.foldl addGate (addGate w t)).getD i false = _
    rw [ih (addGate w t) (by simpa [addGate] using Nat.lt_succ_of_lt h)]
    exact List.getD_append _ _ _ _ h
private theorem write_mix {p a b : List Bool} {vp va vb : Bool} (h : mix p a b)
    (ha : a.length = p.length) (hb : b.length = p.length)
    (v : vp = true → va = true ∨ vb = true) :
    mix (p ++ [vp]) (a ++ [va]) (b ++ [vb]) := by
  intro i
  by_cases hi : i < p.length
  · simpa only [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (ha.symm ▸ hi),
      List.getD_append _ _ _ _ (hb.symm ▸ hi)] using h i
  · have hn := Nat.le_of_not_gt hi
    rw [List.getD_append_right _ _ _ _ hn, List.getD_append_right _ _ _ _ (ha.symm ▸ hn),
      List.getD_append_right _ _ _ _ (hb.symm ▸ hn), ha, hb]
    cases i - p.length with
    | zero => exact v
    | succ i => simp [List.getD]
private theorem meet_mix {pa pb aa ab ba bb : Bool}
    (x : pa = true → aa = true ∨ ba = true)
    (y : pb = true → ab = true ∨ bb = true)
    (same : aa = ba ∨ ab = bb) :
    (pa && pb) = true → (aa && ab) = true ∨ (ba && bb) = true := by
  cases pa <;> cases pb <;> cases aa <;> cases ab <;> cases ba <;> cases bb <;> simp_all
private theorem propagate {m : Nat} (pick : Fin m → Nat) (gs : List Gate)
    (p a b : List Bool) (ha : a.length = p.length) (hb : b.length = p.length)
    (h : mix p a b) (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (cover : covers pick gs)
    (eqv : ∀ k, (gs.foldl addGate a).getD (pick k) false = (gs.foldl addGate b).getD (pick k) false) :
    mix (gs.foldl addGate p) (gs.foldl addGate a) (gs.foldl addGate b) := by
  induction gs generalizing p a b with
  | nil => exact h
  | cons g gs ih =>
    have ok := mono g (by simp)
    have eqnow (k : Fin m) : a.getD (pick k) false = b.getD (pick k) false := by
      by_cases hk : pick k < p.length
      · simpa only [old_wire (g::gs) _ _ (ha.symm ▸ hk),old_wire (g::gs) _ _ (hb.symm ▸ hk)] using eqv k
      · exact (List.getD_eq_default a false (by omega : a.length ≤ pick k)).trans
          (List.getD_eq_default b false (by omega : b.length ≤ pick k)).symm
    apply ih (addGate p g) (addGate a g) (addGate b g) (by simp [addGate,ha]) (by simp [addGate,hb])
    · apply write_mix h ha hb
      rcases g with ⟨op,ins⟩
      rcases ok with ⟨hop,hlen⟩
      rcases hop with hop | hop
      · change op = GateOp.and at hop
        subst op
        cases ins with
        | nil => simp [gateValue,GateOp.eval]
        | cons i tail =>
          cases tail with
          | nil => simpa [gateValue,GateOp.eval] using h i
          | cons j tail =>
            have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
            subst tail
            by_cases hij : i = j
            · subst j
              simpa [gateValue,GateOp.eval] using h i
            · obtain ⟨k, hk | hk⟩ := cover ⟨.and,[i,j]⟩ (by simp) i j rfl rfl hij
              · simpa [gateValue,GateOp.eval] using meet_mix (h i) (h j) (Or.inl (hk ▸ eqnow k))
              · simpa [gateValue,GateOp.eval] using meet_mix (h i) (h j) (Or.inr (hk ▸ eqnow k))
      · change op = GateOp.or at hop
        subst op
        simp only [gateValue,GateOp.eval,List.any_eq_true,List.mem_map]
        rintro ⟨_, ⟨i, hi, rfl⟩, hp⟩
        rcases h i hp with h1 | h2
        · exact Or.inl ⟨_,⟨i,hi,rfl⟩,h1⟩
        · exact Or.inr ⟨_,⟨i,hi,rfl⟩,h2⟩
    · exact fun t ht => mono t (by simp [ht])
    · exact fun t ht => cover t (by simp [ht])
    · exact eqv

def differences : Finset (Fin 13) := {0,1,3,9}
def reps : List (Nat × Nat) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
def multipliers : List (Fin 13) := [1,3,9]
def flag (p w : Fin 13) : Fin 26 → Bool :=
  fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
def orbit (z : Nat × Nat) (a t : Fin 13) (dual : Bool) : Fin 26 → Bool :=
  let bit := fun (u v : Nat) (i : Fin 13) =>
    if dual then v.testBit (-(a*i+t)).val else u.testBit (a*i+t).val
  Fin.append (bit z.1 z.2) (bit z.2 z.1)

def bits (n : Nat) : List Bool := List.ofFn (fun i : Fin 26 => n.testBit i.val)
private theorem bit_at (n : Nat) (i : Fin 26) : (bits n).getD i.val false = n.testBit i.val := by
  rw [List.getD_eq_getElem _ _ (by simp [bits])]
  simp only [bits,List.getElem_ofFn]

private def pm (i : Fin 52) : Nat :=
  (if i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 8193 else (if i.val < 2 then 8194 else 8200)) else (if i.val < 4 then 8704 else (if i.val < 5 then 16386 else 16388))) else (if i.val < 9 then (if i.val < 7 then 16400 else (if i.val < 8 then 17408 else 32772)) else (if i.val < 11 then (if i.val < 10 then 32776 else 32800) else (if i.val < 12 then 34816 else 65544)))) else (if i.val < 19 then (if i.val < 16 then (if i.val < 14 then 65552 else (if i.val < 15 then 65600 else 69632)) else (if i.val < 17 then 131073 else (if i.val < 18 then 131088 else 131104))) else (if i.val < 22 then (if i.val < 20 then 131200 else (if i.val < 21 then 262146 else 262176)) else (if i.val < 24 then (if i.val < 23 then 262208 else 262400) else (if i.val < 25 then 524292 else 524352))))) else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then (if i.val < 27 then 524416 else (if i.val < 28 then 524800 else 1048584)) else (if i.val < 30 then 1048704 else (if i.val < 31 then 1048832 else 1049600))) else (if i.val < 35 then (if i.val < 33 then 2097168 else (if i.val < 34 then 2097408 else 2097664)) else (if i.val < 37 then (if i.val < 36 then 2099200 else 4194336) else (if i.val < 38 then 4194816 else 4195328)))) else (if i.val < 45 then (if i.val < 42 then (if i.val < 40 then 4198400 else (if i.val < 41 then 8388609 else 8388672)) else (if i.val < 43 then 8389632 else (if i.val < 44 then 8390656 else 16777218))) else (if i.val < 48 then (if i.val < 46 then 16777344 else (if i.val < 47 then 16779264 else 16781312)) else (if i.val < 50 then (if i.val < 49 then 33554433 else 33554436) else (if i.val < 51 then 33554688 else 33558528))))))

private structure Entry where
  mask : Nat
  rep : Nat × Nat
  a : Fin 13
  t : Fin 13
  dual : Bool
  word0 : Nat
  word1 : Nat
  word2 : Nat
private def chooseFlag (e : Entry) (k : Fin 26) : Fin 52 :=
  let w := if k.val < 10 then e.word0 else if k.val < 20 then e.word1 else e.word2
  ⟨((w >>> (6 * (k.val % 10))) % 64) % 52, Nat.mod_lt _ (by decide)⟩
private def valid (e : Entry) : Prop :=
  e.rep ∈ reps ∧ e.a ∈ multipliers ∧
  List.ofFn (orbit e.rep e.a e.t e.dual) = bits e.mask ∧
  ∀ k : Fin 26, e.mask.testBit k.val = false →
    pm (chooseFlag e k) &&& (e.mask ||| 2^k.val) = pm (chooseFlag e k)
private instance (e : Entry) : Decidable (valid e) := by unfold valid; infer_instance
private def row0 : Entry := ⟨61888,(7,904),1,11,true,0xc0000286085040,0x6564ce0000002c7,0xcada6785d⟩
private theorem check0 : valid row0 := by decide
private def row1 : Entry := ⟨92576,(13,2848),1,10,true,0xc000e006085040,0x69548028000f007,0xcadae485d⟩
private theorem check1 : valid row1 := by decide
private def row2 : Entry := ⟨115585,(7,904),1,10,true,0xe286245100,0x69740000000f2c7,0xc2da2585d⟩
private theorem check2 : valid row2 := by decide
private def row3 : Entry := ⟨162112,(25,2656),1,9,true,0xc04c0486085040,0x65600e2c0000007,0xcaea6785e⟩
private theorem check3 : valid row3 := by decide
private def row4 : Entry := ⟨177472,(21,2720),1,9,true,0xc04c0291088040,0x65600e0070002c0,0xcafa6685e⟩
private theorem check4 : valid row4 := by decide
private def row5 : Entry := ⟨185152,(13,2848),1,9,true,0x4c0286245110,0x65600e0000c02c7,0xcafa6585e⟩
private theorem check5 : valid row5 := by decide
private def row6 : Entry := ⟨192832,(37,2440),9,11,false,0xc04c0286085040,0x65600e0000002c7,0xcafa6785e⟩
private theorem check6 : valid row6 := by decide
private def row7 : Entry := ⟨208132,(19,708),1,9,true,0xc04ce48d080040,0x61700020500f000,0xc6eaa685e⟩
private theorem check7 : valid row7 := by decide
private def row8 : Entry := ⟨231170,(7,904),1,9,true,0x4ce28d248010,0x6d400000404f2c0,0xcacaa585e⟩
private theorem check8 : valid row8 := by decide
private def row9 : Entry := ⟨308368,(41,2370),1,8,true,0xd7016280088040,0x68044d0060002c0,0xcedaa681d⟩
private theorem check9 : valid row9 := by decide
private def row10 : Entry := ⟨316033,(25,2656),1,8,true,0x17016286245100,0x68040f0000002c7,0xc2da2589d⟩
private theorem check10 : valid row10 := by decide
private def row11 : Entry := ⟨339076,(37,2440),1,8,true,0xd700e54d080040,0x6004c020500f000,0xc6daa68dd⟩
private theorem check11 : valid row11 := by decide
private def row12 : Entry := ⟨346753,(21,2720),1,8,true,0x1700e546305100,0x6804002c000f007,0xc2da2589d⟩
private theorem check12 : valid row12 := by decide
private def row13 : Entry := ⟨362113,(13,2848),1,8,true,0x1700e28d248500,0x68040000700f2c0,0xc2da2589d⟩
private theorem check13 : valid row13 := by decide
private def row14 : Entry := ⟨377473,(37,2440),9,2,false,0x1700e286245100,0x68040000000f2c7,0xc2da2589d⟩
private theorem check14 : valid row14 := by decide
private def row15 : Entry := ⟨408580,(13,2848),3,11,true,0xd74d6491080040,0x60000f205000000,0xc6eaa68df⟩
private theorem check15 : valid row15 := by decide
private def row16 : Entry := ⟨416264,(19,708),1,8,true,0x174d6486005110,0x6c000c240080007,0xceeae589c⟩
private theorem check16 : valid row16 := by decide
private def row17 : Entry := ⟨462340,(7,904),1,8,true,0x174ce48d300510,0x6000002050cf000,0xc6eaa589f⟩
private theorem check17 : valid row17 := by decide
private def row18 : Entry := ⟨470020,(13,2848),3,9,false,0xd74ce48d080040,0x60000020500f000,0xc6eaa68df⟩
private theorem check18 : valid row18 := by decide
private def row19 : Entry := ⟨555296,(37,2440),3,8,true,0xc0699006085040,0x1548f280000007,0xcaeae485e⟩
private theorem check19 : valid row19 := by decide
private def row20 : Entry := ⟨570640,(41,2370),9,8,true,0xc0699280088040,0x1744d0060002c0,0xcafaa681e⟩
private theorem check20 : valid row20 := by decide
private def row21 : Entry := ⟨601376,(7,904),9,11,true,0xc068e00d098040,0x1548028700f000,0xcaeaa485e⟩
private theorem check21 : valid row21 := by decide
private def row22 : Entry := ⟨608545,(41,2370),1,7,true,0x6c068e006305100,0x1540028000f007,0xc2ea2485e⟩
private theorem check22 : valid row22 := by decide
private def row23 : Entry := ⟨616736,(7,904),9,7,false,0xc068e006085040,0x1548028000f007,0xcaeae485e⟩
private theorem check23 : valid row23 := by decide
private def row24 : Entry := ⟨623875,(25,2656),1,7,true,0x6c068e28d248000,0x1440000400f2c0,0xc2ca2685e⟩
private theorem check24 : valid row24 := by decide
private def row25 : Entry := ⟨670976,(37,2440),9,11,true,0xc04d9491098040,0x1700f2c7000000,0xcaeaa685e⟩
private theorem check25 : valid row25 := by decide
private def row26 : Entry := ⟨678152,(37,2440),1,7,true,0x6c04d9486005110,0x1700c240080007,0xcaeae785c⟩
private theorem check26 : valid row26 := by decide
private def row27 : Entry := ⟨686336,(25,2656),1,5,false,0xc04d9486085040,0x1700f2c0000007,0xcaeae785e⟩
private theorem check27 : valid row27 := by decide
private def row28 : Entry := ⟨693506,(21,2720),1,7,true,0x6c04d9291248010,0x1400f0040402c0,0xcacaa685e⟩
private theorem check28 : valid row28 := by decide
private def row29 : Entry := ⟨701696,(21,2720),1,5,false,0xc04d9291088040,0x1700f0070002c0,0xcafaa685e⟩
private theorem check29 : valid row29 := by decide
private def row30 : Entry := ⟨724226,(13,2848),1,7,true,0x6c04ce48d318010,0x140002c404f000,0xcacaa685e⟩
private theorem check30 : valid row30 := by decide
private def row31 : Entry := ⟨732416,(13,2848),1,5,false,0xc04ce48d098040,0x170002c700f000,0xcaeaa685e⟩
private theorem check31 : valid row31 := by decide
private def row32 : Entry := ⟨754946,(37,2440),9,6,false,0x6c04ce28d248010,0x1400000404f2c0,0xcacaa685e⟩
private theorem check32 : valid row32 := by decide
private def row33 : Entry := ⟨801808,(41,2370),3,8,true,0xd7696540098040,0x44d2c6000000,0xceeaa681f⟩
private theorem check33 : valid row33 := by decide
private def row34 : Entry := ⟨808969,(13,2848),3,8,true,0x6d7696546005100,0x40c240000007,0xc2ea278dc⟩
private theorem check34 : valid row34 := by decide
private def row35 : Entry := ⟨824337,(19,708),1,7,true,0x6d7696280248500,0x40d0060002c0,0xc2fa2681f⟩
private theorem check35 : valid row35 := by decide
private def row36 : Entry := ⟨832528,(133,808),1,3,false,0xd7696280088040,0x44d0060002c0,0xcefaa681f⟩
private theorem check36 : valid row36 := by decide
private def row37 : Entry := ⟨924680,(7,904),1,7,true,0x6d74d6491018510,0xc247080000,0xceeaa68dc⟩
private theorem check37 : valid row37 := by decide
private def row38 : Entry := ⟨932864,(7,904),1,3,false,0xd74d6491098040,0xf2c7000000,0xceeaa68df⟩
private theorem check38 : valid row38 := by decide
private def row39 : Entry := ⟨940040,(13,2848),3,6,false,0x6d74d6486005110,0xc240080007,0xceeae78dc⟩
private theorem check39 : valid row39 := by decide
private def row40 : Entry := ⟨1079392,(21,2720),9,0,true,0xde740006085040,0x65548e280000007,0xceea648c0⟩
private theorem check40 : valid row40 := by decide
private def row41 : Entry := ⟨1102401,(37,2440),3,5,true,0x1e740286245100,0x65640e0000002c7,0xc2fa25880⟩
private theorem check41 : valid row41 := by decide
private def row42 : Entry := ⟨1133089,(41,2370),9,12,true,0x1e74e006305100,0x6d540028000f007,0xc2ea24880⟩
private theorem check42 : valid row42 := by decide
private def row43 : Entry := ⟨1194052,(13,2848),9,0,true,0xde4c0491080040,0x61600e20500001f,0xc6ea678c0⟩
private theorem check43 : valid row43 := by decide
private def row44 : Entry := ⟨1202752,(7,904),9,2,true,0x1e4c0486705110,0x65600e2c00c0007,0xceea65880⟩
private theorem check44 : valid row44 := by decide
private def row45 : Entry := ⟨1210432,(37,2440),3,8,false,0xde4c0486085040,0x65600e2c0000007,0xceea678c0⟩
private theorem check45 : valid row45 := by decide
private def row46 : Entry := ⟨1217090,(41,2370),1,6,true,0x1e4c0291248010,0x65400e0040402df,0xceca65880⟩
private theorem check46 : valid row46 := by decide
private def row47 : Entry := ⟨1233472,(7,904),9,11,false,0x1e4c0286245110,0x65600e0000c02c7,0xcefa65880⟩
private theorem check47 : valid row47 := by decide
private def row48 : Entry := ⟨1247750,(25,2656),1,6,true,0x1e4ce48d300010,0x61400020404f01f,0xc6cae5880⟩
private theorem check48 : valid row48 := by decide
private def row49 : Entry := ⟨1325076,(133,808),1,6,true,0xd7756540080040,0x60044d20500001f,0xc6eae7800⟩
private theorem check49 : valid row49 := by decide
private def row50 : Entry := ⟨1333761,(37,2440),9,2,true,0x17756546705100,0x6c040f2c0000007,0xc2ea25880⟩
private theorem check50 : valid row50 := by decide
private def row51 : Entry := ⟨1348113,(37,2440),1,6,true,0x17756280248500,0x6c040d0060002df,0xc2fa25800⟩
private theorem check51 : valid row51 := by decide
private def row52 : Entry := ⟨1364481,(25,2656),1,4,false,0x17756286245100,0x6c040f0000002c7,0xc2fa25880⟩
private theorem check52 : valid row52 := by decide
private def row53 : Entry := ⟨1378821,(21,2720),1,6,true,0x1774e54d300500,0x60040020500f01f,0xc2ea25880⟩
private theorem check53 : valid row53 := by decide
private def row54 : Entry := ⟨1395201,(21,2720),1,4,false,0x1774e546305100,0x6c04002c000f007,0xc2ea25880⟩
private theorem check54 : valid row54 := by decide
private def row55 : Entry := ⟨1448452,(13,2848),1,6,true,0x174d6491700510,0x60000f2050c001f,0xc6eae5880⟩
private theorem check55 : valid row55 := by decide
private def row56 : Entry := ⟨1456132,(19,708),1,2,false,0xd74d6491080040,0x60000f20500001f,0xc6eae78c0⟩
private theorem check56 : valid row56 := by decide
private def row57 : Entry := ⟨1464832,(13,2848),1,4,false,0x174d6486705110,0x6c000f2c00c0007,0xceeae5880⟩
private theorem check57 : valid row57 := by decide
private def row58 : Entry := ⟨1509892,(37,2440),9,10,false,0x174ce48d300510,0x6000002050cf01f,0xc6eae5880⟩
private theorem check58 : valid row58 := by decide
private def row59 : Entry := ⟨1587248,(21,2720),9,11,true,0xde699000098040,0x1544d28600001f,0xceeae4800⟩
private theorem check59 : valid row59 := by decide
private def row60 : Entry := ⟨1595425,(41,2370),3,5,true,0x6de699006705100,0x1540f280000007,0xc2ea248c0⟩
private theorem check60 : valid row60 := by decide
private def row61 : Entry := ⟨1603616,(21,2720),9,9,false,0xde699006085040,0x1548f280000007,0xceeae48c0⟩
private theorem check61 : valid row61 := by decide
private def row62 : Entry := ⟨1609747,(13,2848),3,5,true,0x6de699280248000,0x1440d0040002df,0xc2ca27800⟩
private theorem check62 : valid row62 := by decide
private def row63 : Entry := ⟨1640483,(19,708),1,6,true,0x6de68e00d318000,0x1440028400f01f,0xc2ca248c0⟩
private theorem check63 : valid row63 := by decide
private def row64 : Entry := ⟨1656865,(133,808),1,2,false,0x6de68e006305100,0x1540028000f007,0xc2ea248c0⟩
private theorem check64 : valid row64 := by decide
private def row65 : Entry := ⟨1841169,(7,904),1,6,true,0x6d7696540718500,0x40d2c600001f,0xc2ea27800⟩
private theorem check65 : valid row65 := by decide
private def row66 : Entry := ⟨1849360,(41,2370),3,6,false,0xd7696540098040,0x44d2c600001f,0xceeae7800⟩
private theorem check66 : valid row66 := by decide
private def row67 : Entry := ⟨1857537,(7,904),1,2,false,0x6d7696546705100,0x40f2c0000007,0xc2ea278c0⟩
private theorem check67 : valid row67 := by decide
private def row68 : Entry := ⟨1871889,(13,2848),3,3,false,0x6d7696280248500,0x40d0060002df,0xc2fa27800⟩
private theorem check68 : valid row68 := by decide
private def row69 : Entry := ⟨2126048,(41,2370),3,10,true,0xe1000006085040,0x65548e2800008c7,0xceda6401d⟩
private theorem check69 : valid row69 := by decide
private def row70 : Entry := ⟨2143424,(133,808),1,11,true,0xe10002a0088040,0x6564ce0070002c0,0xceda6601d⟩
private theorem check70 : valid row70 := by decide
private def row71 : Entry := ⟨2150593,(21,2720),9,4,true,0x8a1000286245100,0x65640e0000002c7,0xc2da2701d⟩
private theorem check71 : valid row71 := by decide
private def row72 : Entry := ⟨2158784,(41,2370),3,8,false,0xe1000286085040,0x6564ce0000002c7,0xceda6701d⟩
private theorem check72 : valid row72 := by decide
private def row73 : Entry := ⟨2172068,(21,2720),3,0,true,0xe100e00d080040,0x61548020500f8c0,0xc6daa401d⟩
private theorem check73 : valid row73 := by decide
private def row74 : Entry := ⟨2196611,(37,2440),3,2,true,0x8a100e28d248000,0x69440000400f2c0,0xc2ca2601d⟩
private theorem check74 : valid row74 := by decide
private def row75 : Entry := ⟨2241604,(7,904),3,0,true,0xe14c0491080040,0x61600e2050008c0,0xc6fa6601f⟩
private theorem check75 : valid row75 := by decide
private def row76 : Entry := ⟨2266178,(41,2370),9,3,true,0x8a14c0291248010,0x65400e0040402c0,0xceca6601f⟩
private theorem check76 : valid row76 := by decide
private def row77 : Entry := ⟨2274368,(41,2370),9,1,false,0xe14c0291088040,0x65600e0070002c0,0xcefa6601f⟩
private theorem check77 : valid row77 := by decide
private def row78 : Entry := ⟨2372740,(21,2720),3,11,true,0xd7016560080040,0x6004cf2050008c0,0xc6daa601d⟩
private theorem check78 : valid row78 := by decide
private def row79 : Entry := ⟨2379913,(13,2848),9,4,true,0x897016546005100,0x68040c2400008c7,0xc2da2701c⟩
private theorem check79 : valid row79 := by decide
private def row80 : Entry := ⟨2397313,(7,904),9,6,true,0x8970162a0248500,0x68040f0070002c0,0xc2da2601d⟩
private theorem check80 : valid row80 := by decide
private def row81 : Entry := ⟨2405504,(41,2370),1,6,false,0xd70162a0088040,0x6804cf0070002c0,0xcedaa601d⟩
private theorem check81 : valid row81 := by decide
private def row82 : Entry := ⟨2412673,(37,2440),3,5,false,0x897016286245100,0x68040f0000002c7,0xc2da2701d⟩
private theorem check82 : valid row82 := by decide
private def row83 : Entry := ⟨2425989,(41,2370),1,5,true,0x89700e54d300500,0x60040020500f8c0,0xc2da2601d⟩
private theorem check83 : valid row83 := by decide
private def row84 : Entry := ⟨2434180,(21,2720),3,9,false,0xd700e54d080040,0x6004c020500f8c0,0xc6daa601d⟩
private theorem check84 : valid row84 := by decide
private def row85 : Entry := ⟨2458753,(7,904),9,2,false,0x89700e28d248500,0x68040000700f2c0,0xc2da2601d⟩
private theorem check85 : valid row85 := by decide
private def row86 : Entry := ⟨2495500,(25,2656),1,5,true,0x8974d6491000510,0x60000c2050808c0,0xc6faa601c⟩
private theorem check86 : valid row86 := by decide
private def row87 : Entry := ⟨2503684,(37,2440),1,3,false,0xd74d6491080040,0x60000f2050008c0,0xc6faa601f⟩
private theorem check87 : valid row87 := by decide
private def row88 : Entry := ⟨2641961,(133,808),1,5,true,0x6e1699006005100,0x1540c2400008c7,0xc2fa2401c⟩
private theorem check88 : valid row88 := by decide
private def row89 : Entry := ⟨2659331,(37,2440),9,6,true,0x6e16992a0248000,0x1440f0040002c0,0xc2ca2601f⟩
private theorem check89 : valid row89 := by decide
private def row90 : Entry := ⟨2688035,(37,2440),1,5,true,0x6e168e00d318000,0x1440028400f8c0,0xc2ca2401f⟩
private theorem check90 : valid row90 := by decide
private def row91 : Entry := ⟨2720771,(25,2656),1,3,false,0x6e168e28d248000,0x1440000400f2c0,0xc2ca2601f⟩
private theorem check91 : valid row91 := by decide
private def row92 : Entry := ⟨2757642,(21,2720),1,5,true,0x6e14d9491018010,0x1400c2440408c0,0xcecaa601c⟩
private theorem check92 : valid row92 := by decide
private def row93 : Entry := ⟨2790402,(21,2720),1,3,false,0x6e14d9291248010,0x1400f0040402c0,0xcecaa601f⟩
private theorem check93 : valid row93 := by decide
private def row94 : Entry := ⟨2888713,(13,2848),1,5,true,0x6d7696560018500,0x40c2470008c0,0xc2fa2601c⟩
private theorem check94 : valid row94 := by decide
private def row95 : Entry := ⟨2904073,(19,708),1,1,false,0x6d7696546005100,0x40c2400008c7,0xc2fa2701c⟩
private theorem check95 : valid row95 := by decide
private def row96 : Entry := ⟨2921473,(13,2848),1,3,false,0x6d76962a0248500,0x40f0070002c0,0xc2fa2601f⟩
private theorem check96 : valid row96 := by decide
private def row97 : Entry := ⟨3019784,(37,2440),9,1,false,0x6d74d6491018510,0xc2470808c0,0xcefaa601c⟩
private theorem check97 : valid row97 := by decide
private def row98 : Entry := ⟨3158116,(37,2440),3,0,true,0xde740020080040,0x61548e2050008df,0xc6fa64000⟩
private theorem check98 : valid row98 := by decide
private def row99 : Entry := ⟨3166305,(21,2720),9,2,true,0x89e740006705100,0x65540e2800008c7,0xc2fa24000⟩
private theorem check99 : valid row99 := by decide
private def row100 : Entry := ⟨3174496,(21,2720),9,11,false,0xde740006085040,0x65548e2800008c7,0xcefa64000⟩
private theorem check100 : valid row100 := by decide
private def row101 : Entry := ⟨3182659,(41,2370),3,2,true,0x89e7402a0248000,0x65440e0040002df,0xc2ca27000⟩
private theorem check101 : valid row101 := by decide
private def row102 : Entry := ⟨3199041,(21,2720),9,0,false,0x89e740286245100,0x65640e0000002c7,0xc2fa27000⟩
private theorem check102 : valid row102 := by decide
private def row103 : Entry := ⟨3211303,(13,2848),3,2,true,0x89e74e00d300000,0x61440020400f8df,0xc2ca24000⟩
private theorem check103 : valid row103 := by decide
private def row104 : Entry := ⟨3280966,(19,708),1,5,true,0x89e4c0491700010,0x61400e2040408df,0xc6ca67000⟩
private theorem check104 : valid row104 := by decide
private def row105 : Entry := ⟨3289156,(13,2848),9,11,false,0xde4c0491080040,0x61600e2050008df,0xc6fa67000⟩
private theorem check105 : valid row105 := by decide
private def row106 : Entry := ⟨3313730,(133,808),1,1,false,0x89e4c0291248010,0x65400e0040402df,0xceca67000⟩
private theorem check106 : valid row106 := by decide
private def row107 : Entry := ⟨3674147,(7,904),1,5,true,0x6de699020718000,0x1440f2840008df,0xc2ca24000⟩
private theorem check107 : valid row107 := by decide
private def row108 : Entry := ⟨3690529,(41,2370),3,3,false,0x6de699006705100,0x1540f2800008c7,0xc2fa24000⟩
private theorem check108 : valid row108 := by decide
private def row109 : Entry := ⟨3706883,(7,904),1,1,false,0x6de6992a0248000,0x1440f0040002df,0xc2ca27000⟩
private theorem check109 : valid row109 := by decide
private def row110 : Entry := ⟨3735587,(13,2848),3,0,false,0x6de68e00d318000,0x1440028400f8df,0xc2ca24000⟩
private theorem check110 : valid row110 := by decide
private def row111 : Entry := ⟨4221376,(13,2848),3,10,true,0xc0000906085040,0x6564ce2c0027007,0xcada4085d⟩
private theorem check111 : valid row111 := by decide
private def row112 : Entry := ⟨4235728,(37,2440),9,8,true,0xc0000280088040,0x65644d0060272e6,0xcada4081d⟩
private theorem check112 : valid row112 := by decide
private def row113 : Entry := ⟨4243905,(41,2370),3,7,true,0x940000286245100,0x65640e0000272c7,0xc2da0085d⟩
private theorem check113 : valid row113 := by decide
private def row114 : Entry := ⟨4252096,(7,904),1,7,false,0xc0000286085040,0x6564ce0000272c7,0xcada4085d⟩
private theorem check114 : valid row114 := by decide
private def row115 : Entry := ⟨4270468,(13,2848),9,10,true,0xc000e90d080040,0x6174c020500f026,0xc6dac085d⟩
private theorem check115 : valid row115 := by decide
private def row116 : Entry := ⟨4278657,(133,808),1,10,true,0x94000e906305100,0x6974002c000f007,0xc2da0085d⟩
private theorem check116 : valid row116 := by decide
private def row117 : Entry := ⟨4286848,(19,708),1,6,false,0xc000e906085040,0x6974c02c000f007,0xcadac085d⟩
private theorem check117 : valid row117 := by decide
private def row118 : Entry := ⟨4292995,(21,2720),9,8,true,0x94000e28d248000,0x69440000400f2e6,0xc2ca0085d⟩
private theorem check118 : valid row118 := by decide
private def row119 : Entry := ⟨4309377,(41,2370),3,5,false,0x94000e286245100,0x69740000000f2c7,0xc2da0085d⟩
private theorem check119 : valid row119 := by decide
private def row120 : Entry := ⟨4335940,(7,904),3,12,true,0xc04c0491080040,0x61600e205027026,0xc6ea4085e⟩
private theorem check120 : valid row120 := by decide
private def row121 : Entry := ⟨4344136,(21,2720),3,10,true,0x9404c0486005110,0x65600c2400a7007,0xcaea4085c⟩
private theorem check121 : valid row121 := by decide
private def row122 : Entry := ⟨4352320,(37,2440),1,7,false,0xc04c0486085040,0x65600e2c0027007,0xcaea4085e⟩
private theorem check122 : valid row122 := by decide
private def row123 : Entry := ⟨4393222,(37,2440),3,12,true,0x9404ce48d300010,0x61400020404f026,0xc6cac085e⟩
private theorem check123 : valid row123 := by decide
private def row124 : Entry := ⟨4401412,(13,2848),9,8,false,0xc04ce48d080040,0x61700020500f026,0xc6eac085e⟩
private theorem check124 : valid row124 := by decide
private def row125 : Entry := ⟨4466836,(7,904),3,11,true,0xd7016540080040,0x60044d205027026,0xc6dac081d⟩
private theorem check125 : valid row125 := by decide
private def row126 : Entry := ⟨4475017,(7,904),3,10,true,0x957016546005100,0x68040c240027007,0xc2da008dc⟩
private theorem check126 : valid row126 := by decide
private def row127 : Entry := ⟨4524165,(41,2370),9,7,true,0x95700e54d300500,0x60040020500f026,0xc2da008dd⟩
private theorem check127 : valid row127 := by decide
private def row128 : Entry := ⟨4532356,(7,904),3,7,false,0xd700e54d080040,0x6004c020500f026,0xc6dac08dd⟩
private theorem check128 : valid row128 := by decide
private def row129 : Entry := ⟨4540545,(41,2370),9,5,false,0x95700e546305100,0x6804002c000f007,0xc2da008dd⟩
private theorem check129 : valid row129 := by decide
private def row130 : Entry := ⟨4737289,(21,2720),3,8,true,0x6c0699906005100,0x1740c240027007,0xc2ea0085c⟩
private theorem check130 : valid row130 := by decide
private def row131 : Entry := ⟨4751635,(13,2848),9,8,true,0x6c0699280248000,0x1440d0040272e6,0xc2ca0081e⟩
private theorem check131 : valid row131 := by decide
private def row132 : Entry := ⟨4786435,(7,904),9,10,true,0x6c068e90d318000,0x144002c400f026,0xc2ca0085e⟩
private theorem check132 : valid row132 := by decide
private def row133 : Entry := ⟨4802817,(41,2370),1,5,false,0x6c068e906305100,0x174002c000f007,0xc2ea0085e⟩
private theorem check133 : valid row133 := by decide
private def row134 : Entry := ⟨4817155,(37,2440),3,2,false,0x6c068e28d248000,0x1440000400f2e6,0xc2ca0085e⟩
private theorem check134 : valid row134 := by decide
private def row135 : Entry := ⟨4851978,(41,2370),1,4,true,0x6c04d9491018010,0x1400c244067026,0xcacac085c⟩
private theorem check135 : valid row135 := by decide
private def row136 : Entry := ⟨4868360,(21,2720),3,6,false,0x6c04d9486005110,0x1700c2400a7007,0xcaeac085c⟩
private theorem check136 : valid row136 := by decide
private def row137 : Entry := ⟨4917506,(7,904),9,6,false,0x6c04ce48d318010,0x140002c404f026,0xcacac085e⟩
private theorem check137 : valid row137 := by decide
private def row138 : Entry := ⟨4982809,(25,2656),1,4,true,0x6d7696540018500,0x40c246027026,0xc2ea0081c⟩
private theorem check138 : valid row138 := by decide
private def row139 : Entry := ⟨4999177,(37,2440),1,2,false,0x6d7696546005100,0x40c240027007,0xc2ea008dc⟩
private theorem check139 : valid row139 := by decide
private def row140 : Entry := ⟨5253204,(41,2370),9,10,true,0xde740900080040,0x61644d20502701f,0xc6ea40800⟩
private theorem check140 : valid row140 := by decide
private def row141 : Entry := ⟨5275731,(133,808),1,4,true,0x95e740280248000,0x65440d0040272df,0xc2ca00800⟩
private theorem check141 : valid row141 := by decide
private def row142 : Entry := ⟨5310471,(37,2440),9,10,true,0x95e74e90d300000,0x61440020400f01f,0xc2ca008c0⟩
private theorem check142 : valid row142 := by decide
private def row143 : Entry := ⟨5376070,(37,2440),1,4,true,0x95e4c0491700010,0x61400e20406701f,0xc6ca408c0⟩
private theorem check143 : valid row143 := by decide
private def row144 : Entry := ⟨5384260,(7,904),3,8,false,0xde4c0491080040,0x61600e20502701f,0xc6ea408c0⟩
private theorem check144 : valid row144 := by decide
private def row145 : Entry := ⟨5441542,(25,2656),1,2,false,0x95e4ce48d300010,0x61400020404f01f,0xc6cac08c0⟩
private theorem check145 : valid row145 := by decide
private def row146 : Entry := ⟨5507093,(21,2720),1,4,true,0x957756540700500,0x60040d20502701f,0xc2ea00800⟩
private theorem check146 : valid row146 := by decide
private def row147 : Entry := ⟨5515284,(41,2370),9,8,false,0xd7756540080040,0x60044d20502701f,0xc6eac0800⟩
private theorem check147 : valid row147 := by decide
private def row148 : Entry := ⟨5572613,(21,2720),1,2,false,0x95774e54d300500,0x60040020500f01f,0xc2ea008c0⟩
private theorem check148 : valid row148 := by decide
private def row149 : Entry := ⟨5769235,(13,2848),1,4,true,0x6de699900718000,0x1440d2c402701f,0xc2ca00800⟩
private theorem check149 : valid row149 := by decide
private def row150 : Entry := ⟨5799955,(19,708),1,0,false,0x6de699280248000,0x1440d0040272df,0xc2ca00800⟩
private theorem check150 : valid row150 := by decide
private def row151 : Entry := ⟨5834755,(13,2848),1,2,false,0x6de68e90d318000,0x144002c400f01f,0xc2ca008c0⟩
private theorem check151 : valid row151 := by decide
private def row152 : Entry := ⟨6031377,(37,2440),9,5,false,0x6d7696540718500,0x40d2c602701f,0xc2ea00800⟩
private theorem check152 : valid row152 := by decide
private def row153 : Entry := ⟨6308041,(37,2440),3,10,true,0x8a1000906005100,0x65640c2400278c7,0xc2da0001c⟩
private theorem check153 : valid row153 := by decide
private def row154 : Entry := ⟨6324419,(21,2720),9,6,true,0x8a10002a0248000,0x65440e0040272e6,0xc2ca0001d⟩
private theorem check154 : valid row154 := by decide
private def row155 : Entry := ⟨6340801,(21,2720),9,2,false,0x8a1000286245100,0x65640e0000272c7,0xc2da0001d⟩
private theorem check155 : valid row155 := by decide
private def row156 : Entry := ⟨6357127,(41,2370),3,12,true,0x8a100e90d300000,0x61440020400f8e6,0xc2ca0001d⟩
private theorem check156 : valid row156 := by decide
private def row157 : Entry := ⟨6389891,(21,2720),9,4,false,0x8a100e28d248000,0x69440000400f2e6,0xc2ca0001d⟩
private theorem check157 : valid row157 := by decide
private def row158 : Entry := ⟨6422606,(13,2848),3,12,true,0x8a14c0491000010,0x61400c2040678e6,0xc6ca4001c⟩
private theorem check158 : valid row158 := by decide
private def row159 : Entry := ⟨6553741,(19,708),1,4,true,0x897016560000500,0x60040c2050278e6,0xc2da0001c⟩
private theorem check159 : valid row159 := by decide
private def row160 : Entry := ⟨6570121,(13,2848),9,2,false,0x897016546005100,0x68040c2400278c7,0xc2da0001c⟩
private theorem check160 : valid row160 := by decide
private def row161 : Entry := ⟨6619269,(133,808),1,0,false,0x89700e54d300500,0x60040020500f8e6,0xc2da0001d⟩
private theorem check161 : valid row161 := by decide
private def row162 : Entry := ⟨7340103,(7,904),1,4,true,0x89e740920700000,0x61440e2040278df,0xc2ca00000⟩
private theorem check162 : valid row162 := by decide
private def row163 : Entry := ⟨7372867,(41,2370),3,0,false,0x89e7402a0248000,0x65440e0040272df,0xc2ca00000⟩
private theorem check163 : valid row163 := by decide
private def row164 : Entry := ⟨7405575,(7,904),1,0,false,0x89e74e90d300000,0x61440020400f8df,0xc2ca00000⟩
private theorem check164 : valid row164 := by decide
private def row165 : Entry := ⟨7471174,(13,2848),3,10,false,0x89e4c0491700010,0x61400e2040678df,0xc6ca40000⟩
private theorem check165 : valid row165 := by decide
private def row166 : Entry := ⟨8417696,(19,708),1,12,true,0xc0029006085040,0x69548f280000ac7,0xcad02485d⟩
private theorem check166 : valid row166 := by decide
private def row167 : Entry := ⟨8434064,(37,2440),1,11,true,0xc0029280088040,0x69744d0060002ea,0xcad02781d⟩
private theorem check167 : valid row167 := by decide
private def row168 : Entry := ⟨8442752,(13,2848),3,7,true,0x29286245128,0x6974cf0000c02c7,0xcad02585d⟩
private theorem check168 : valid row168 := by decide
private def row169 : Entry := ⟨8450432,(13,2848),3,5,false,0xc0029286085040,0x6974cf0000002c7,0xcad02785d⟩
private theorem check169 : valid row169 := by decide
private def row170 : Entry := ⟨8462756,(7,904),9,12,true,0xc000e00d080040,0x61548020500faea,0xc6d02485d⟩
private theorem check170 : valid row170 := by decide
private def row171 : Entry := ⟨8471456,(37,2440),9,12,true,0xe006305128,0x6954802800cfac7,0xcad02485d⟩
private theorem check171 : valid row171 := by decide
private def row172 : Entry := ⟨8479136,(13,2848),1,8,false,0xc000e006085040,0x69548028000fac7,0xcad02485d⟩
private theorem check172 : valid row172 := by decide
private def row173 : Entry := ⟨8487810,(41,2370),3,4,true,0xe28d248028,0x6944c000404f2ea,0xcac02585d⟩
private theorem check173 : valid row173 := by decide
private def row174 : Entry := ⟨8504192,(7,904),1,6,false,0xe286245128,0x6974c00000cf2c7,0xcad02585d⟩
private theorem check174 : valid row174 := by decide
private def row175 : Entry := ⟨8540936,(13,2848),9,1,true,0x4e9486005110,0x6d700c240080ac7,0xcaf02585c⟩
private theorem check175 : valid row175 := by decide
private def row176 : Entry := ⟨8557314,(133,808),1,9,true,0x4e9291248010,0x6d400f0040402ea,0xcac02585e⟩
private theorem check176 : valid row176 := by decide
private def row177 : Entry := ⟨8573696,(19,708),1,5,false,0x4e9286245110,0x6d700f0000c02c7,0xcaf02585e⟩
private theorem check177 : valid row177 := by decide
private def row178 : Entry := ⟨8585990,(21,2720),9,12,true,0x4ce48d300010,0x61400020404faea,0xc6c02585e⟩
private theorem check178 : valid row178 := by decide
private def row179 : Entry := ⟨8618754,(41,2370),3,2,false,0x4ce28d248010,0x6d400000404f2ea,0xcac02585e⟩
private theorem check179 : valid row179 := by decide
private def row180 : Entry := ⟨8663188,(21,2720),3,9,true,0xd7016540080040,0x60044d205000aea,0xc6d02781d⟩
private theorem check180 : valid row180 := by decide
private def row181 : Entry := ⟨8671880,(7,904),3,9,true,0x17016546005128,0x6804cc240080ac7,0xced02589c⟩
private theorem check181 : valid row181 := by decide
private def row182 : Entry := ⟨8688272,(21,2720),3,7,true,0x17016280248528,0x68044d0060c02ea,0xced02581d⟩
private theorem check182 : valid row182 := by decide
private def row183 : Entry := ⟨8695952,(21,2720),3,5,false,0xd7016280088040,0x68044d0060002ea,0xced02781d⟩
private theorem check183 : valid row183 := by decide
private def row184 : Entry := ⟨8704640,(37,2440),1,6,false,0x17016286245128,0x6804cf0000c02c7,0xced02589d⟩
private theorem check184 : valid row184 := by decide
private def row185 : Entry := ⟨8786444,(37,2440),3,9,true,0x174d6491000510,0x60000c205080aea,0xc6f02589c⟩
private theorem check185 : valid row185 := by decide
private def row186 : Entry := ⟨8802824,(13,2848),9,12,false,0x174d6486005110,0x6c000c240080ac7,0xcef02589c⟩
private theorem check186 : valid row186 := by decide
private def row187 : Entry := ⟨8925488,(13,2848),9,11,true,0xc0699000098040,0x1544d286000aea,0xcaf02481e⟩
private theorem check187 : valid row187 := by decide
private def row188 : Entry := ⟨8933672,(7,904),3,8,true,0x6c0699006005128,0x1548c240080ac7,0xcaf02485c⟩
private theorem check188 : valid row188 := by decide
private def row189 : Entry := ⟨8941856,(13,2848),9,9,false,0xc0699006085040,0x1548f280000ac7,0xcaf02485e⟩
private theorem check189 : valid row189 := by decide
private def row190 : Entry := ⟨8950034,(7,904),3,7,true,0x6c0699280248028,0x1444d0040402ea,0xcac02781e⟩
private theorem check190 : valid row190 := by decide
private def row191 : Entry := ⟨8958224,(7,904),3,3,false,0xc0699280088040,0x1744d0060002ea,0xcaf02781e⟩
private theorem check191 : valid row191 := by decide
private def row192 : Entry := ⟨9048330,(41,2370),9,11,true,0x6c04d9491018010,0x1400c244040aea,0xcac02785c⟩
private theorem check192 : valid row192 := by decide
private def row193 : Entry := ⟨9064712,(7,904),3,4,false,0x6c04d9486005110,0x1700c240080ac7,0xcaf02785c⟩
private theorem check193 : valid row193 := by decide
private def row194 : Entry := ⟨9081090,(41,2370),9,9,false,0x6c04d9291248010,0x1400f0040402ea,0xcac02785e⟩
private theorem check194 : valid row194 := by decide
private def row195 : Entry := ⟨9449524,(7,904),9,0,true,0xde769000080040,0x61544d205000adf,0xc6f024800⟩
private theorem check195 : valid row195 := by decide
private def row196 : Entry := ⟨9474578,(21,2720),3,5,true,0x1e769280248028,0x6d444d0040402df,0xcec025800⟩
private theorem check196 : valid row196 := by decide
private def row197 : Entry := ⟨9503270,(13,2848),9,12,true,0x1e74e00d300028,0x61448020404fadf,0xc6c024880⟩
private theorem check197 : valid row197 := by decide
private def row198 : Entry := ⟨9572870,(7,904),9,1,true,0x1e4e9491700010,0x61400f204040adf,0xc6c025880⟩
private theorem check198 : valid row198 := by decide
private def row199 : Entry := ⟨9605634,(41,2370),1,4,false,0x1e4e9291248010,0x6d400f0040402df,0xcec025880⟩
private theorem check199 : valid row199 := by decide
private def row200 : Entry := ⟨9634310,(37,2440),3,12,false,0x1e4ce48d300010,0x61400020404fadf,0xc6c025880⟩
private theorem check200 : valid row200 := by decide
private def row201 : Entry := ⟨9703956,(41,2370),1,3,true,0x17756540700528,0x60044d2050c0adf,0xc6f025800⟩
private theorem check201 : valid row201 := by decide
private def row202 : Entry := ⟨9711636,(41,2370),1,1,false,0xd7756540080040,0x60044d205000adf,0xc6f027800⟩
private theorem check202 : valid row202 := by decide
private def row203 : Entry := ⟨9736720,(21,2720),3,3,false,0x17756280248528,0x6c044d0060c02df,0xcef025800⟩
private theorem check203 : valid row203 := by decide
private def row204 : Entry := ⟨9835012,(7,904),9,10,false,0x174d6491700510,0x60000f2050c0adf,0xc6f025880⟩
private theorem check204 : valid row204 := by decide
private def row205 : Entry := ⟨9965618,(25,2656),1,3,true,0x6de699000718028,0x1444d284040adf,0xcec024800⟩
private theorem check205 : valid row205 := by decide
private def row206 : Entry := ⟨9973808,(37,2440),3,3,false,0xde699000098040,0x1544d286000adf,0xcef024800⟩
private theorem check206 : valid row206 := by decide
private def row207 : Entry := ⟨9998354,(37,2440),1,1,false,0x6de699280248028,0x1444d0040402df,0xcec027800⟩
private theorem check207 : valid row207 := by decide
private def row208 : Entry := ⟨10498212,(41,2370),1,0,true,0xe1029020080040,0x61548f2050008ea,0xc6d02401d⟩
private theorem check208 : valid row208 := by decide
private def row209 : Entry := ⟨10506408,(41,2370),9,1,true,0x8a1029006005128,0x69548c2400808c7,0xced02401c⟩
private theorem check209 : valid row209 := by decide
private def row210 : Entry := ⟨10514592,(133,808),1,8,false,0xe1029006085040,0x69548f2800008c7,0xced02401d⟩
private theorem check210 : valid row210 := by decide
private def row211 : Entry := ⟨10551462,(133,808),1,3,true,0x8a100e00d300028,0x61448020404f8ea,0xc6c02401d⟩
private theorem check211 : valid row211 := by decide
private def row212 : Entry := ⟨10559652,(41,2370),1,11,false,0xe100e00d080040,0x61548020500f8ea,0xc6d02401d⟩
private theorem check212 : valid row212 := by decide
private def row213 : Entry := ⟨10620942,(37,2440),9,1,true,0x8a14e9491000010,0x61400c2040408ea,0xc6c02701c⟩
private theorem check213 : valid row213 := by decide
private def row214 : Entry := ⟨10752140,(37,2440),1,3,true,0x897016560000528,0x6004cc2050808ea,0xc6d02701c⟩
private theorem check214 : valid row214 := by decide
private def row215 : Entry := ⟨10760324,(21,2720),3,7,false,0xd7016560080040,0x6004cf2050008ea,0xc6d02701d⟩
private theorem check215 : valid row215 := by decide
private def row216 : Entry := ⟨10768520,(7,904),3,5,false,0x897016546005128,0x6804cc2400808c7,0xced02701c⟩
private theorem check216 : valid row216 := by decide
private def row217 : Entry := ⟨10883084,(25,2656),1,1,false,0x8974d6491000510,0x60000c2050808ea,0xc6f02701c⟩
private theorem check217 : valid row217 := by decide
private def row218 : Entry := ⟨11014186,(21,2720),1,3,true,0x6e1699020018028,0x1448c2440408ea,0xcec02401c⟩
private theorem check218 : valid row218 := by decide
private def row219 : Entry := ⟨11030568,(41,2370),9,12,false,0x6e1699006005128,0x1548c2400808c7,0xcef02401c⟩
private theorem check219 : valid row219 := by decide
private def row220 : Entry := ⟨11145226,(21,2720),1,1,false,0x6e14d9491018010,0x1400c2440408ea,0xcec02701c⟩
private theorem check220 : valid row220 := by decide
private def row221 : Entry := ⟨11538470,(13,2848),1,3,true,0x89e769020700028,0x61448f2040408df,0xc6c024000⟩
private theorem check221 : valid row221 := by decide
private def row222 : Entry := ⟨11546660,(7,904),9,9,false,0xde769020080040,0x61548f2050008df,0xc6f024000⟩
private theorem check222 : valid row222 := by decide
private def row223 : Entry := ⟨11599910,(19,708),1,12,false,0x89e74e00d300028,0x61448020404f8df,0xc6c024000⟩
private theorem check223 : valid row223 := by decide
private def row224 : Entry := ⟨11669510,(13,2848),1,1,false,0x89e4e9491700010,0x61400f2040408df,0xc6c027000⟩
private theorem check224 : valid row224 := by decide
private def row225 : Entry := ⟨12062754,(37,2440),9,9,false,0x6de699020718028,0x1448f2840408df,0xcec024000⟩
private theorem check225 : valid row225 := by decide
private def row226 : Entry := ⟨12591508,(25,2656),1,0,true,0xc0029900080040,0x61744d205027ae6,0xc6d00081d⟩
private theorem check226 : valid row226 := by decide
private def row227 : Entry := ⟨12616082,(37,2440),3,7,true,0x940029280248028,0x69444d0040672e6,0xcac00081d⟩
private theorem check227 : valid row227 := by decide
private def row228 : Entry := ⟨12624272,(25,2656),1,9,false,0xc0029280088040,0x69744d0060272e6,0xcad00081d⟩
private theorem check228 : valid row228 := by decide
private def row229 : Entry := ⟨12648838,(21,2720),9,10,true,0x94000e90d300028,0x6144c020404fae6,0xc6c00085d⟩
private theorem check229 : valid row229 := by decide
private def row230 : Entry := ⟨12657028,(37,2440),3,7,false,0xc000e90d080040,0x6174c020500fae6,0xc6d00085d⟩
private theorem check230 : valid row230 := by decide
private def row231 : Entry := ⟨12681602,(21,2720),9,6,false,0x94000e28d248028,0x6944c000404f2e6,0xcac00085d⟩
private theorem check231 : valid row231 := by decide
private def row232 : Entry := ⟨12714254,(41,2370),3,9,true,0x9404e9491000010,0x61400c204067ae6,0xc6c00085c⟩
private theorem check232 : valid row232 := by decide
private def row233 : Entry := ⟨12779782,(21,2720),9,8,false,0x9404ce48d300010,0x61400020404fae6,0xc6c00085e⟩
private theorem check233 : valid row233 := by decide
private def row234 : Entry := ⟨12845212,(13,2848),3,9,true,0x957016540000528,0x60044c2050a7ae6,0xc6d00081c⟩
private theorem check234 : valid row234 := by decide
private def row235 : Entry := ⟨12853396,(37,2440),1,11,false,0xd7016540080040,0x60044d205027ae6,0xc6d00081d⟩
private theorem check235 : valid row235 := by decide
private def row236 : Entry := ⟨13107482,(19,708),1,3,true,0x6c0699900018028,0x1444c244067ae6,0xcac00081c⟩
private theorem check236 : valid row236 := by decide
private def row237 : Entry := ⟨13140242,(13,2848),9,6,false,0x6c0699280248028,0x1444d0040672e6,0xcac00081e⟩
private theorem check237 : valid row237 := by decide
private def row238 : Entry := ⟨13238538,(133,808),1,12,false,0x6c04d9491018010,0x1400c244067ae6,0xcac00085c⟩
private theorem check238 : valid row238 := by decide
private def row239 : Entry := ⟨14680206,(7,904),1,3,true,0x8a1029920000028,0x6144cc2040678e6,0xc6c00001c⟩
private theorem check239 : valid row239 := by decide
private def row240 : Entry := ⟨14745734,(41,2370),3,10,false,0x8a100e90d300028,0x6144c020404f8e6,0xc6c00001d⟩
private theorem check240 : valid row240 := by decide
private def row241 : Entry := ⟨14811150,(7,904),1,12,false,0x8a14e9491000010,0x61400c2040678e6,0xc6c00001c⟩
private theorem check241 : valid row241 := by decide
private def row242 : Entry := ⟨14942348,(13,2848),3,7,false,0x897016560000528,0x6004cc2050a78e6,0xc6d00001c⟩
private theorem check242 : valid row242 := by decide
private def row243 : Entry := ⟨16819536,(21,2720),1,11,true,0xc0b40280088040,0x65644d00602f2c0,0xc80a6681e⟩
private theorem check243 : valid row243 := by decide
private def row244 : Entry := ⟨16827201,(19,708),1,11,true,0xb40286245100,0x65640e00002f2c7,0xc00a2585e⟩
private theorem check244 : valid row244 := by decide
private def row245 : Entry := ⟨16852260,(41,2370),1,10,true,0xc0b4e00d080040,0x61548020500fb80,0xc40aa485e⟩
private theorem check245 : valid row245 := by decide
private def row246 : Entry := ⟨16859937,(37,2440),1,10,true,0xb4e006305100,0x6d540028000fb87,0xc00a2485e⟩
private theorem check246 : valid row246 := by decide
private def row247 : Entry := ⟨16877313,(13,2848),3,4,true,0xb4e28d248b00,0x6d740000700f2c0,0xc00a2585e⟩
private theorem check247 : valid row247 := by decide
private def row248 : Entry := ⟨16892673,(13,2848),3,2,false,0xb4e286245100,0x6d740000000f2c7,0xc00a2585e⟩
private theorem check248 : valid row248 := by decide
private def row249 : Entry := ⟨16917828,(41,2370),9,0,true,0xc04c0491080040,0x61600e20502fb80,0xc40a6685e⟩
private theorem check249 : valid row249 := by decide
private def row250 : Entry := ⟨16925512,(7,904),9,3,true,0x4c0486005110,0x65600c2400afb87,0xc80a6585c⟩
private theorem check250 : valid row250 := by decide
private def row251 : Entry := ⟨16942912,(37,2440),9,3,true,0x4c0291248b10,0x65600e0070ef2c0,0xc80a6585e⟩
private theorem check251 : valid row251 := by decide
private def row252 : Entry := ⟨16950592,(21,2720),1,7,false,0xc04c0291088040,0x65600e00702f2c0,0xc80a6685e⟩
private theorem check252 : valid row252 := by decide
private def row253 : Entry := ⟨16958272,(13,2848),1,7,false,0x4c0286245110,0x65600e0000ef2c7,0xc80a6585e⟩
private theorem check253 : valid row253 := by decide
private def row254 : Entry := ⟨16975620,(41,2370),3,1,true,0x4ce48d300b10,0x6170002050cfb80,0xc40aa585e⟩
private theorem check254 : valid row254 := by decide
private def row255 : Entry := ⟨16983300,(133,808),1,5,false,0xc04ce48d080040,0x61700020500fb80,0xc40aa685e⟩
private theorem check255 : valid row255 := by decide
private def row256 : Entry := ⟨17008384,(7,904),1,5,false,0x4ce28d248b10,0x6d70000070cf2c0,0xc80aa585e⟩
private theorem check256 : valid row256 := by decide
private def row257 : Entry := ⟨17073681,(13,2848),9,5,true,0x17b56280248500,0x6c040d00602f2c0,0xc00a2581f⟩
private theorem check257 : valid row257 := by decide
private def row258 : Entry := ⟨17106437,(133,808),1,8,true,0x17b4e54d300500,0x60040020500fb80,0xc00a2589f⟩
private theorem check258 : valid row258 := by decide
private def row259 : Entry := ⟨17139201,(19,708),1,4,false,0x17b4e28d248500,0x6c040000700f2c0,0xc00a2589f⟩
private theorem check259 : valid row259 := by decide
private def row260 : Entry := ⟨17171980,(21,2720),9,3,true,0x174d6491000510,0x60000c2050afb80,0xc40aa589c⟩
private theorem check260 : valid row260 := by decide
private def row261 : Entry := ⟨17237508,(41,2370),3,12,false,0x174ce48d300510,0x6000002050cfb80,0xc40aa589f⟩
private theorem check261 : valid row261 := by decide
private def row262 : Entry := ⟨17311024,(133,808),1,0,true,0xc0699000098040,0x1544d28602fb80,0xc80aa481e⟩
private theorem check262 : valid row262 := by decide
private def row263 : Entry := ⟨17318185,(21,2720),3,6,true,0x6c0699006005100,0x1540c24002fb87,0xc00a2485c⟩
private theorem check263 : valid row263 := by decide
private def row264 : Entry := ⟨17335569,(7,904),3,6,true,0x6c0699280248b00,0x1740d00602f2c0,0xc00a2681e⟩
private theorem check264 : valid row264 := by decide
private def row265 : Entry := ⟨17343760,(41,2370),9,6,false,0xc0699280088040,0x1744d00602f2c0,0xc80aa681e⟩
private theorem check265 : valid row265 := by decide
private def row266 : Entry := ⟨17368353,(21,2720),3,4,true,0x6c068e00d318b00,0x1540028700fb80,0xc00a2485e⟩
private theorem check266 : valid row266 := by decide
private def row267 : Entry := ⟨17376544,(41,2370),1,8,false,0xc068e00d098040,0x1548028700fb80,0xc80aa485e⟩
private theorem check267 : valid row267 := by decide
private def row268 : Entry := ⟨17383713,(21,2720),3,2,false,0x6c068e006305100,0x1540028000fb87,0xc00a2485e⟩
private theorem check268 : valid row268 := by decide
private def row269 : Entry := ⟨17401089,(37,2440),1,5,false,0x6c068e28d248b00,0x1740000700f2c0,0xc00a2685e⟩
private theorem check269 : valid row269 := by decide
private def row270 : Entry := ⟨17564697,(37,2440),3,6,true,0x6d7696540018500,0x40c24602fb80,0xc00a2681c⟩
private theorem check270 : valid row270 := by decide
private def row271 : Entry := ⟨17597457,(13,2848),9,3,false,0x6d7696280248500,0x40d00602f2c0,0xc00a2681f⟩
private theorem check271 : valid row271 := by decide
private def row272 : Entry := ⟨17834100,(37,2440),9,0,true,0xde740000080040,0x61544d20502fb9f,0xc40a64800⟩
private theorem check272 : valid row272 := by decide
private def row273 : Entry := ⟨17842785,(13,2848),9,2,true,0x1e740006705100,0x65540e28002fb87,0xc00a24880⟩
private theorem check273 : valid row273 := by decide
private def row274 : Entry := ⟨17859153,(7,904),3,5,true,0x1e740280248b00,0x65640d00602f2df,0xc00a25800⟩
private theorem check274 : valid row274 := by decide
private def row275 : Entry := ⟨17875521,(13,2848),9,0,false,0x1e740286245100,0x65640e00002f2c7,0xc00a25880⟩
private theorem check275 : valid row275 := by decide
private def row276 : Entry := ⟨17891877,(7,904),3,4,true,0x1e74e00d300b00,0x61540020500fb9f,0xc00a24880⟩
private theorem check276 : valid row276 := by decide
private def row277 : Entry := ⟨17908257,(7,904),3,0,false,0x1e74e006305100,0x6d540028000fb87,0xc00a24880⟩
private theorem check277 : valid row277 := by decide
private def row278 : Entry := ⟨18088469,(41,2370),9,2,true,0x17756540700500,0x60040d20502fb9f,0xc00a25800⟩
private theorem check278 : valid row278 := by decide
private def row279 : Entry := ⟨18121233,(7,904),3,1,false,0x17756280248500,0x6c040d00602f2df,0xc00a25800⟩
private theorem check279 : valid row279 := by decide
private def row280 : Entry := ⟨18153989,(41,2370),9,0,false,0x1774e54d300500,0x60040020500fb9f,0xc00a25880⟩
private theorem check280 : valid row280 := by decide
private def row281 : Entry := ⟨18883684,(37,2440),1,0,true,0xe1b40020080040,0x61548e20502f8c0,0xc40a6401f⟩
private theorem check281 : valid row281 := by decide
private def row282 : Entry := ⟨18890857,(7,904),9,4,true,0x8a1b40006005100,0x65540c24002f8c7,0xc00a2401c⟩
private theorem check282 : valid row282 := by decide
private def row283 : Entry := ⟨18940965,(21,2720),3,2,true,0x8a1b4e00d300b00,0x61540020500f8c0,0xc00a2401f⟩
private theorem check283 : valid row283 := by decide
private def row284 : Entry := ⟨18949156,(21,2720),3,11,false,0xe1b4e00d080040,0x61548020500f8c0,0xc40aa401f⟩
private theorem check284 : valid row284 := by decide
private def row285 : Entry := ⟨19006540,(13,2848),9,3,true,0x8a14c0491000b10,0x61600c2050af8c0,0xc40a6601c⟩
private theorem check285 : valid row285 := by decide
private def row286 : Entry := ⟨19014724,(7,904),3,9,false,0xe14c0491080040,0x61600e20502f8c0,0xc40a6601f⟩
private theorem check286 : valid row286 := by decide
private def row287 : Entry := ⟨19137549,(7,904),9,5,true,0x897b56560000500,0x60040c20502f8c0,0xc00a2601c⟩
private theorem check287 : valid row287 := by decide
private def row288 : Entry := ⟨19203077,(41,2370),1,3,false,0x897b4e54d300500,0x60040020500f8c0,0xc00a2601f⟩
private theorem check288 : valid row288 := by decide
private def row289 : Entry := ⟨19268620,(37,2440),3,9,false,0x8974d6491000510,0x60000c2050af8c0,0xc40aa601c⟩
private theorem check289 : valid row289 := by decide
private def row290 : Entry := ⟨19399721,(41,2370),1,2,true,0x6e1699020018b00,0x1540c24702f8c0,0xc00a2401c⟩
private theorem check290 : valid row290 := by decide
private def row291 : Entry := ⟨19415081,(41,2370),1,0,false,0x6e1699006005100,0x1540c24002f8c7,0xc00a2401c⟩
private theorem check291 : valid row291 := by decide
private def row292 : Entry := ⟨19465249,(21,2720),3,0,false,0x6e168e00d318b00,0x1540028700f8c0,0xc00a2401f⟩
private theorem check292 : valid row292 := by decide
private def row293 : Entry := ⟨19661833,(7,904),9,1,false,0x6d7696560018500,0x40c24702f8c0,0xc00a2601c⟩
private theorem check293 : valid row293 := by decide
private def row294 : Entry := ⟨19923045,(25,2656),1,2,true,0x89e740020700b00,0x61540e20502f8df,0xc00a24000⟩
private theorem check294 : valid row294 := by decide
private def row295 : Entry := ⟨19931236,(25,2656),1,11,false,0xde740020080040,0x61548e20502f8df,0xc40a64000⟩
private theorem check295 : valid row295 := by decide
private def row296 : Entry := ⟨19939425,(37,2440),3,0,false,0x89e740006705100,0x65540e28002f8c7,0xc00a24000⟩
private theorem check296 : valid row296 := by decide
private def row297 : Entry := ⟨19988517,(37,2440),1,0,false,0x89e74e00d300b00,0x61540020500f8df,0xc00a24000⟩
private theorem check297 : valid row297 := by decide
private def row298 : Entry := ⟨20980052,(21,2720),1,0,true,0xc0b40900080040,0x61644d205027ba6,0xc40a4081e⟩
private theorem check298 : valid row298 := by decide
private def row299 : Entry := ⟨20988233,(41,2370),1,12,true,0x940b40906005100,0x65640c240027b87,0xc00a0085c⟩
private theorem check299 : valid row299 := by decide
private def row300 : Entry := ⟨21004625,(41,2370),9,5,true,0x940b40280248b00,0x65640d0060272e6,0xc00a0081e⟩
private theorem check300 : valid row300 := by decide
private def row301 : Entry := ⟨21012816,(21,2720),1,9,false,0xc0b40280088040,0x65644d0060272e6,0xc80a4081e⟩
private theorem check301 : valid row301 := by decide
private def row302 : Entry := ⟨21020993,(133,808),1,7,false,0x940b40286245100,0x65640e0000272c7,0xc00a0085e⟩
private theorem check302 : valid row302 := by decide
private def row303 : Entry := ⟨21102924,(133,808),1,2,true,0x9404c0491000b10,0x61600c2050a7ba6,0xc40a4085c⟩
private theorem check303 : valid row303 := by decide
private def row304 : Entry := ⟨21111108,(41,2370),9,11,false,0xc04c0491080040,0x61600e205027ba6,0xc40a4085e⟩
private theorem check304 : valid row304 := by decide
private def row305 : Entry := ⟨21119304,(41,2370),1,10,false,0x9404c0486005110,0x65600c2400a7b87,0xc80a4085c⟩
private theorem check305 : valid row305 := by decide
private def row306 : Entry := ⟨21233693,(37,2440),9,5,true,0x957b56540000500,0x60040c205027ba6,0xc00a0081c⟩
private theorem check306 : valid row306 := by decide
private def row307 : Entry := ⟨21496089,(37,2440),1,2,true,0x6c0699900018b00,0x1740c246027ba6,0xc00a0081c⟩
private theorem check307 : valid row307 := by decide
private def row308 : Entry := ⟨21512457,(21,2720),3,4,false,0x6c0699906005100,0x1740c240027b87,0xc00a0085c⟩
private theorem check308 : valid row308 := by decide
private def row309 : Entry := ⟨21528849,(7,904),3,2,false,0x6c0699280248b00,0x1740d0060272e6,0xc00a0081e⟩
private theorem check309 : valid row309 := by decide
private def row310 : Entry := ⟨21757977,(25,2656),1,0,false,0x6d7696540018500,0x40c246027ba6,0xc00a0081c⟩
private theorem check310 : valid row310 := by decide
private def row311 : Entry := ⟨22020181,(21,2720),1,2,true,0x95e740900700b00,0x61640d205027b9f,0xc00a00800⟩
private theorem check311 : valid row311 := by decide
private def row312 : Entry := ⟨22028372,(21,2720),1,11,false,0xde740900080040,0x61644d205027b9f,0xc40a40800⟩
private theorem check312 : valid row312 := by decide
private def row313 : Entry := ⟨22052945,(41,2370),9,3,false,0x95e740280248b00,0x65640d0060272df,0xc00a00800⟩
private theorem check313 : valid row313 := by decide
private def row314 : Entry := ⟨22282261,(21,2720),1,0,false,0x957756540700500,0x60040d205027b9f,0xc00a00800⟩
private theorem check314 : valid row314 := by decide
private def row315 : Entry := ⟨23068749,(13,2848),1,2,true,0x8a1b40920000b00,0x61640c2050278e6,0xc00a0001c⟩
private theorem check315 : valid row315 := by decide
private def row316 : Entry := ⟨23085129,(7,904),9,0,false,0x8a1b40906005100,0x65640c2400278c7,0xc00a0001c⟩
private theorem check316 : valid row316 := by decide
private def row317 : Entry := ⟨23199820,(19,708),1,11,false,0x8a14c0491000b10,0x61600c2050a78e6,0xc40a4001c⟩
private theorem check317 : valid row317 := by decide
private def row318 : Entry := ⟨23330829,(13,2848),1,0,false,0x897b56560000500,0x60040c2050278e6,0xc00a0001c⟩
private theorem check318 : valid row318 := by decide
private def row319 : Entry := ⟨24117317,(37,2440),9,0,false,0x89e740920700b00,0x61640e2050278df,0xc00a00000⟩
private theorem check319 : valid row319 := by decide
private def row320 : Entry := ⟨25174324,(13,2848),1,0,true,0xc0b69000080040,0x61544d20502faea,0xc4002481e⟩
private theorem check320 : valid row320 := by decide
private def row321 : Entry := ⟨25183016,(25,2656),1,12,true,0xb69006005128,0x6d548c2400afac7,0xc8002485c⟩
private theorem check321 : valid row321 := by decide
private def row322 : Entry := ⟨25232164,(37,2440),3,4,true,0xb4e00d300b28,0x6154802050cfaea,0xc4002485e⟩
private theorem check322 : valid row322 := by decide
private def row323 : Entry := ⟨25239844,(7,904),9,8,false,0xc0b4e00d080040,0x61548020500faea,0xc4002485e⟩
private theorem check323 : valid row323 := by decide
private def row324 : Entry := ⟨25248544,(25,2656),1,8,false,0xb4e006305128,0x6d54802800cfac7,0xc8002485e⟩
private theorem check324 : valid row324 := by decide
private def row325 : Entry := ⟨25297676,(21,2720),9,1,true,0x4e9491000b10,0x61700c2050afaea,0xc4002585c⟩
private theorem check325 : valid row325 := by decide
private def row326 : Entry := ⟨25314056,(37,2440),3,4,false,0x4e9486005110,0x6d700c2400afac7,0xc8002585c⟩
private theorem check326 : valid row326 := by decide
private def row327 : Entry := ⟨25363204,(21,2720),9,10,false,0x4ce48d300b10,0x6170002050cfaea,0xc4002585e⟩
private theorem check327 : valid row327 := by decide
private def row328 : Entry := ⟨25428508,(41,2370),3,6,true,0x17b56540000528,0x60044c2050afaea,0xc4002581c⟩
private theorem check328 : valid row328 := by decide
private def row329 : Entry := ⟨25559564,(21,2720),9,12,false,0x174d6491000510,0x60000c2050afaea,0xc4002589c⟩
private theorem check329 : valid row329 := by decide
private def row330 : Entry := ⟨25690424,(13,2848),3,6,true,0x6c0699000018b28,0x1544c2460afaea,0xc8002481c⟩
private theorem check330 : valid row330 := by decide
private def row331 : Entry := ⟨25698608,(19,708),1,9,false,0xc0699000098040,0x1544d28602faea,0xc8002481e⟩
private theorem check331 : valid row331 := by decide
private def row332 : Entry := ⟨25706792,(37,2440),1,10,false,0x6c0699006005128,0x1548c2400afac7,0xc8002485c⟩
private theorem check332 : valid row332 := by decide
private def row333 : Entry := ⟨26214964,(19,708),1,2,true,0x1e769000700b28,0x61544d2050efadf,0xc40024800⟩
private theorem check333 : valid row333 := by decide
private def row334 : Entry := ⟨26222644,(13,2848),1,11,false,0xde769000080040,0x61544d20502fadf,0xc40024800⟩
private theorem check334 : valid row334 := by decide
private def row335 : Entry := ⟨26280484,(13,2848),9,10,false,0x1e74e00d300b28,0x6154802050cfadf,0xc40024880⟩
private theorem check335 : valid row335 := by decide
private def row336 : Entry := ⟨26477076,(133,808),1,11,false,0x17756540700528,0x60044d2050efadf,0xc40025800⟩
private theorem check336 : valid row336 := by decide
private def row337 : Entry := ⟨29360412,(7,904),1,2,true,0x940b69900000b28,0x61744c2050a7ae6,0xc4000081c⟩
private theorem check337 : valid row337 := by decide
private def row338 : Entry := ⟨29368596,(37,2440),9,8,false,0xc0b69900080040,0x61744d205027ae6,0xc4000081e⟩
private theorem check338 : valid row338 := by decide
private def row339 : Entry := ⟨29491468,(41,2370),3,7,false,0x9404e9491000b10,0x61700c2050a7ae6,0xc4000085c⟩
private theorem check339 : valid row339 := by decide
private def row340 : Entry := ⟨29622300,(7,904),1,11,false,0x957b56540000528,0x60044c2050a7ae6,0xc4000081c⟩
private theorem check340 : valid row340 := by decide
private def row341 : Entry := ⟨29884696,(13,2848),3,4,false,0x6c0699900018b28,0x1744c2460a7ae6,0xc8000081c⟩
private theorem check341 : valid row341 := by decide
private def row342 : Entry := ⟨33581280,(7,904),1,12,true,0xf2000006085040,0x65548e280033007,0x2da648dd⟩
private theorem check342 : valid row342 := by decide
private def row343 : Entry := ⟨33596624,(13,2848),1,11,true,0xf2000280088040,0x65644d0060332c0,0x2da6681d⟩
private theorem check343 : valid row343 := by decide
private def row344 : Entry := ⟨33631392,(25,2656),1,10,true,0xf200e00d0b1040,0x69548028700f000,0x2daa48dd⟩
private theorem check344 : valid row344 := by decide
private def row345 : Entry := ⟨33639072,(21,2720),1,10,true,0x3200e006305130,0x6954802800cf007,0x2dae489d⟩
private theorem check345 : valid row345 := by decide
private def row346 : Entry := ⟨33646752,(37,2440),9,7,false,0xf200e006085040,0x69548028000f007,0x2dae48dd⟩
private theorem check346 : valid row346 := by decide
private def row347 : Entry := ⟨33654402,(19,708),1,10,true,0x3200e28d248030,0x6944c000404f2c0,0x2caa589d⟩
private theorem check347 : valid row347 := by decide
private def row348 : Entry := ⟨33704520,(41,2370),1,9,true,0x324c0486005110,0x65600c2400b3007,0x2ea6589c⟩
private theorem check348 : valid row348 := by decide
private def row349 : Entry := ⟨33719874,(37,2440),1,9,true,0x324c0291248010,0x65400e0040732c0,0x2ca6589f⟩
private theorem check349 : valid row349 := by decide
private def row350 : Entry := ⟨33754626,(13,2848),3,1,true,0x324ce48d331010,0x6d40002c404f000,0x2caa589f⟩
private theorem check350 : valid row350 := by decide
private def row351 : Entry := ⟨33785346,(13,2848),3,12,false,0x324ce28d248010,0x6d400000404f2c0,0x2caa589f⟩
private theorem check351 : valid row351 := by decide
private def row352 : Entry := ⟨33827984,(37,2440),3,11,true,0xd70165400b1040,0x68044d2c6033000,0x2daa681d⟩
private theorem check352 : valid row352 := by decide
private def row353 : Entry := ⟨33835656,(41,2370),9,4,true,0x17016546005130,0x6804cc2400b3007,0x2dae589c⟩
private theorem check353 : valid row353 := by decide
private def row354 : Entry := ⟨33851024,(7,904),9,7,true,0x17016280248530,0x68044d0060f32c0,0x2daa581d⟩
private theorem check354 : valid row354 := by decide
private def row355 : Entry := ⟨33858704,(7,904),9,3,false,0xd7016280088040,0x68044d0060332c0,0x2daa681d⟩
private theorem check355 : valid row355 := by decide
private def row356 : Entry := ⟨33885824,(37,2440),9,7,true,0x1700e54d331530,0x6804c02c70cf000,0x2daa589d⟩
private theorem check356 : valid row356 := by decide
private def row357 : Entry := ⟨33893504,(25,2656),1,6,false,0xd700e54d0b1040,0x6804c02c700f000,0x2daa68dd⟩
private theorem check357 : valid row357 := by decide
private def row358 : Entry := ⟨33901184,(21,2720),1,6,false,0x1700e546305130,0x6804c02c00cf007,0x2dae589d⟩
private theorem check358 : valid row358 := by decide
private def row359 : Entry := ⟨33916544,(13,2848),1,6,false,0x1700e28d248530,0x6804c00070cf2c0,0x2daa589d⟩
private theorem check359 : valid row359 := by decide
private def row360 : Entry := ⟨33951240,(41,2370),3,11,true,0x174d6491031510,0x6c000c2470b3000,0x2eaa589c⟩
private theorem check360 : valid row360 := by decide
private def row361 : Entry := ⟨33966600,(133,808),1,4,false,0x174d6486005110,0x6c000c2400b3007,0x2eae589c⟩
private theorem check361 : valid row361 := by decide
private def row362 : Entry := ⟨34016768,(7,904),1,4,false,0x174ce48d331510,0x6c00002c70cf000,0x2eaa589f⟩
private theorem check362 : valid row362 := by decide
private def row363 : Entry := ⟨34090032,(21,2720),9,9,true,0xf2699000098040,0x1544d286033000,0x2eaa481f⟩
private theorem check363 : valid row363 := by decide
private def row364 : Entry := ⟨34147362,(13,2848),9,9,true,0x6f268e00d318030,0x1448028404f000,0x2caa48df⟩
private theorem check364 : valid row364 := by decide
private def row365 : Entry := ⟨34155552,(37,2440),3,11,false,0xf268e00d098040,0x1548028700f000,0x2eaa48df⟩
private theorem check365 : valid row365 := by decide
private def row366 : Entry := ⟨34212874,(133,808),1,7,true,0x6f24d9491018010,0x1400c244073000,0x2caa68dc⟩
private theorem check366 : valid row366 := by decide
private def row367 : Entry := ⟨34278402,(19,708),1,3,false,0x6f24ce48d318010,0x140002c404f000,0x2caa68df⟩
private theorem check367 : valid row367 := by decide
private def row368 : Entry := ⟨34343960,(21,2720),9,7,true,0x6d7696540018530,0x44c2460b3000,0x2eaa681c⟩
private theorem check368 : valid row368 := by decide
private def row369 : Entry := ⟨34352144,(21,2720),9,5,false,0xd7696540098040,0x44d2c6033000,0x2eaa681f⟩
private theorem check369 : valid row369 := by decide
private def row370 : Entry := ⟨34475016,(41,2370),3,9,false,0x6d74d6491018510,0xc2470b3000,0x2eaa68dc⟩
private theorem check370 : valid row370 := by decide
private def row371 : Entry := ⟨34613360,(41,2370),3,0,true,0xde7400000b1040,0x65544d28603301f,0x2ea64800⟩
private theorem check371 : valid row371 := by decide
private def row372 : Entry := ⟨34622048,(133,808),1,12,true,0x1e740006705130,0x65548e2800f3007,0x2ea64880⟩
private theorem check372 : valid row372 := by decide
private def row373 : Entry := ⟨34629728,(41,2370),3,11,false,0xde740006085040,0x65548e280033007,0x2ea648c0⟩
private theorem check373 : valid row373 := by decide
private def row374 : Entry := ⟨34636370,(21,2720),3,3,true,0x1e740280248030,0x65444d0040732df,0x2ca65800⟩
private theorem check374 : valid row374 := by decide
private def row375 : Entry := ⟨34671138,(7,904),3,3,true,0x1e74e00d331030,0x6d448028404f01f,0x2cae4880⟩
private theorem check375 : valid row375 := by decide
private def row376 : Entry := ⟨34687520,(41,2370),9,10,false,0x1e74e006305130,0x6d54802800cf007,0x2eae4880⟩
private theorem check376 : valid row376 := by decide
private def row377 : Entry := ⟨34736706,(21,2720),3,1,true,0x1e4c0491731010,0x65400e2c407301f,0x2ca65880⟩
private theorem check377 : valid row377 := by decide
private def row378 : Entry := ⟨34753088,(41,2370),1,7,false,0x1e4c0486705110,0x65600e2c00f3007,0x2ea65880⟩
private theorem check378 : valid row378 := by decide
private def row379 : Entry := ⟨34767426,(21,2720),3,12,false,0x1e4c0291248010,0x65400e0040732df,0x2ca65880⟩
private theorem check379 : valid row379 := by decide
private def row380 : Entry := ⟨34802178,(37,2440),1,4,false,0x1e4ce48d331010,0x6d40002c404f01f,0x2cae5880⟩
private theorem check380 : valid row380 := by decide
private def row381 : Entry := ⟨35129394,(37,2440),3,3,true,0x6de699000718030,0x1444d28407301f,0x2cae4800⟩
private theorem check381 : valid row381 := by decide
private def row382 : Entry := ⟨35137584,(21,2720),9,7,false,0xde699000098040,0x1544d28603301f,0x2eae4800⟩
private theorem check382 : valid row382 := by decide
private def row383 : Entry := ⟨35194914,(13,2848),9,7,false,0x6de68e00d318030,0x1448028404f01f,0x2cae48c0⟩
private theorem check383 : valid row383 := by decide
private def row384 : Entry := ⟨35661024,(13,2848),3,0,true,0xe10000200b1040,0x65548e2870338c0,0x2da6401d⟩
private theorem check384 : valid row384 := by decide
private def row385 : Entry := ⟨35668200,(37,2440),9,4,true,0x8a1000006005130,0x65548c2400b38c7,0x2da6401c⟩
private theorem check385 : valid row385 := by decide
private def row386 : Entry := ⟨35676384,(7,904),1,8,false,0xe1000006085040,0x65548e2800338c7,0x2da6401d⟩
private theorem check386 : valid row386 := by decide
private def row387 : Entry := ⟨35685570,(13,2848),9,6,true,0x8a10002a0248030,0x6544ce0040732c0,0x2ca6601d⟩
private theorem check387 : valid row387 := by decide
private def row388 : Entry := ⟨35693760,(19,708),1,7,false,0xe10002a0088040,0x6564ce0070332c0,0x2da6601d⟩
private theorem check388 : valid row388 := by decide
private def row389 : Entry := ⟨35718306,(7,904),3,2,true,0x8a100e00d331030,0x69448028404f8c0,0x2caa401d⟩
private theorem check389 : valid row389 := by decide
private def row390 : Entry := ⟨35726496,(37,2440),1,8,false,0xe100e00d0b1040,0x69548028700f8c0,0x2daa401d⟩
private theorem check390 : valid row390 := by decide
private def row391 : Entry := ⟨35751042,(13,2848),9,4,false,0x8a100e28d248030,0x6944c000404f2c0,0x2caa601d⟩
private theorem check391 : valid row391 := by decide
private def row392 : Entry := ⟨35783754,(7,904),3,1,true,0x8a14c0491031010,0x65400c2440738c0,0x2ca6601c⟩
private theorem check392 : valid row392 := by decide
private def row393 : Entry := ⟨35816514,(7,904),3,10,false,0x8a14c0291248010,0x65400e0040732c0,0x2ca6601f⟩
private theorem check393 : valid row393 := by decide
private def row394 : Entry := ⟨36176938,(41,2370),9,6,true,0x6e1699020018030,0x1448c2440738c0,0x2caa401c⟩
private theorem check394 : valid row394 := by decide
private def row395 : Entry := ⟨36242466,(7,904),3,11,false,0x6e168e00d318030,0x1448028404f8c0,0x2caa401f⟩
private theorem check395 : valid row395 := by decide
private def row396 : Entry := ⟨36307978,(41,2370),9,4,false,0x6e14d9491018010,0x1400c2440738c0,0x2caa601c⟩
private theorem check396 : valid row396 := by decide
private def row397 : Entry := ⟨37759184,(19,708),1,0,true,0xf20009000b1040,0x65644d2c6027026,0x2da4081d⟩
private theorem check397 : valid row397 := by decide
private def row398 : Entry := ⟨37767368,(37,2440),1,12,true,0x972000906005130,0x6564cc2400a7007,0x2da408dc⟩
private theorem check398 : valid row398 := by decide
private def row399 : Entry := ⟨37775552,(13,2848),3,8,false,0xf2000906085040,0x6564ce2c0027007,0x2da408dd⟩
private theorem check399 : valid row399 := by decide
private def row400 : Entry := ⟨37781714,(7,904),9,8,true,0x972000280248030,0x65444d0040672e6,0x2ca4081d⟩
private theorem check400 : valid row400 := by decide
private def row401 : Entry := ⟨37789904,(13,2848),1,9,false,0xf2000280088040,0x65644d0060272e6,0x2da4081d⟩
private theorem check401 : valid row401 := by decide
private def row402 : Entry := ⟨37881930,(21,2720),3,12,true,0x9724c0491031010,0x65400c244067026,0x2ca408dc⟩
private theorem check402 : valid row402 := by decide
private def row403 : Entry := ⟨37898312,(21,2720),3,8,false,0x9724c0486005110,0x65600c2400a7007,0x2ea408dc⟩
private theorem check403 : valid row403 := by decide
private def row404 : Entry := ⟨38013080,(13,2848),9,7,true,0x957016540031530,0x68044c2460a7026,0x2dac081c⟩
private theorem check404 : valid row404 := by decide
private def row405 : Entry := ⟨38021264,(13,2848),9,5,false,0xd70165400b1040,0x68044d2c6027026,0x2dac081d⟩
private theorem check405 : valid row405 := by decide
private def row406 : Entry := ⟨38029448,(7,904),3,6,false,0x957016546005130,0x6804cc2400a7007,0x2dac08dc⟩
private theorem check406 : valid row406 := by decide
private def row407 : Entry := ⟨38275098,(7,904),9,9,true,0x6f2699900018030,0x1444c244067026,0x2cac081c⟩
private theorem check407 : valid row407 := by decide
private def row408 : Entry := ⟨38406154,(41,2370),1,2,false,0x6f24d9491018010,0x1400c244067026,0x2cac08dc⟩
private theorem check408 : valid row408 := by decide
private def row409 : Entry := ⟨38537240,(37,2440),3,6,false,0x6d7696540018530,0x44c2460a7026,0x2eac081c⟩
private theorem check409 : valid row409 := by decide
private def row410 : Entry := ⟨38799442,(41,2370),1,1,true,0x95e740900731030,0x65444d2c406701f,0x2ca40800⟩
private theorem check410 : valid row410 := by decide
private def row411 : Entry := ⟨38807632,(133,808),1,9,false,0xde7409000b1040,0x65644d2c602701f,0x2ea40800⟩
private theorem check411 : valid row411 := by decide
private def row412 : Entry := ⟨38830162,(41,2370),1,12,false,0x95e740280248030,0x65444d0040672df,0x2ca40800⟩
private theorem check412 : valid row412 := by decide
private def row413 : Entry := ⟨38930498,(21,2720),3,10,false,0x95e4c0491731010,0x65400e2c406701f,0x2ca408c0⟩
private theorem check413 : valid row413 := by decide
private def row414 : Entry := ⟨39323666,(7,904),9,5,false,0x6de699900718030,0x1444d2c406701f,0x2cac0800⟩
private theorem check414 : valid row414 := by decide
private def row415 : Entry := ⟨39846090,(25,2656),1,1,true,0x8a1000920031030,0x6544cc2440678e6,0x2ca4001c⟩
private theorem check415 : valid row415 := by decide
private def row416 : Entry := ⟨39862472,(25,2656),1,10,false,0x8a1000906005130,0x6564cc2400a78c7,0x2da4001c⟩
private theorem check416 : valid row416 := by decide
private def row417 : Entry := ⟨39878850,(37,2440),3,10,false,0x8a10002a0248030,0x6544ce0040672e6,0x2ca4001d⟩
private theorem check417 : valid row417 := by decide
private def row418 : Entry := ⟨39977034,(37,2440),1,12,false,0x8a14c0491031010,0x65400c2440678e6,0x2ca4001c⟩
private theorem check418 : valid row418 := by decide
private def row419 : Entry := ⟨41960104,(21,2720),1,12,true,0x32029006005128,0x69548c2400b3ac7,0x2d02489c⟩
private theorem check419 : valid row419 := by decide
private def row420 : Entry := ⟨41976466,(41,2370),1,11,true,0x32029280248028,0x69444d0040732ea,0x2c02581d⟩
private theorem check420 : valid row420 := by decide
private def row421 : Entry := ⟨42009250,(41,2370),9,9,true,0x3200e00d331028,0x69448028404faea,0x2c02489d⟩
private theorem check421 : valid row421 := by decide
private def row422 : Entry := ⟨42025632,(21,2720),1,8,false,0x3200e006305128,0x6954802800cfac7,0x2d02489d⟩
private theorem check422 : valid row422 := by decide
private def row423 : Entry := ⟨42041986,(133,808),1,6,false,0x3200e28d248028,0x6944c000404f2ea,0x2c02589d⟩
private theorem check423 : valid row423 := by decide
private def row424 : Entry := ⟨42205848,(133,808),1,1,true,0x17016540031528,0x68044c2460b3aea,0x2d02581c⟩
private theorem check424 : valid row424 := by decide
private def row425 : Entry := ⟨42222216,(41,2370),9,2,false,0x17016546005128,0x6804cc2400b3ac7,0x2d02589c⟩
private theorem check425 : valid row425 := by decide
private def row426 : Entry := ⟨42238608,(41,2370),1,9,false,0x17016280248528,0x68044d0060f32ea,0x2d02581d⟩
private theorem check426 : valid row426 := by decide
private def row427 : Entry := ⟨42467386,(37,2440),9,9,true,0x6f2699000018028,0x1444c244073aea,0x2c02481c⟩
private theorem check427 : valid row427 := by decide
private def row428 : Entry := ⟨42992178,(37,2440),1,1,true,0x1e769000731028,0x6d444d284073adf,0x2c024800⟩
private theorem check428 : valid row428 := by decide
private def row429 : Entry := ⟨43024914,(21,2720),3,1,false,0x1e769280248028,0x6d444d0040732df,0x2c025800⟩
private theorem check429 : valid row429 := by decide
private def row430 : Entry := ⟨43057698,(7,904),3,12,false,0x1e74e00d331028,0x6d448028404fadf,0x2c024880⟩
private theorem check430 : valid row430 := by decide
private def row431 : Entry := ⟨43515954,(25,2656),1,12,false,0x6de699000718028,0x1444d284073adf,0x2c024800⟩
private theorem check431 : valid row431 := by decide
private def row432 : Entry := ⟨44040362,(21,2720),1,1,true,0x8a1029020031028,0x69448c2440738ea,0x2c02401c⟩
private theorem check432 : valid row432 := by decide
private def row433 : Entry := ⟨44056744,(21,2720),1,10,false,0x8a1029006005128,0x69548c2400b38c7,0x2d02401c⟩
private theorem check433 : valid row433 := by decide
private def row434 : Entry := ⟨44105890,(41,2370),9,7,false,0x8a100e00d331028,0x69448028404f8ea,0x2c02401d⟩
private theorem check434 : valid row434 := by decide
private def row435 : Entry := ⟨44564522,(21,2720),1,12,false,0x6e1699020018028,0x1448c2440738ea,0x2c02401c⟩
private theorem check435 : valid row435 := by decide
private def row436 : Entry := ⟨46137498,(13,2848),1,1,true,0x972029900031028,0x69444c244067ae6,0x2c00081c⟩
private theorem check436 : valid row436 := by decide
private def row437 : Entry := ⟨46170258,(7,904),9,4,false,0x972029280248028,0x69444d0040672e6,0x2c00081d⟩
private theorem check437 : valid row437 := by decide
private def row438 : Entry := ⟨46399640,(19,708),1,10,false,0x957016540031528,0x68044c2460a7ae6,0x2d00081c⟩
private theorem check438 : valid row438 := by decide
private def row439 : Entry := ⟨46661658,(13,2848),1,12,false,0x6f2699900018028,0x1444c244067ae6,0x2c00081c⟩
private theorem check439 : valid row439 := by decide
private def row440 : Entry := ⟨48234634,(37,2440),9,4,false,0x8a1029920031028,0x6944cc2440678e6,0x2c00001c⟩
private theorem check440 : valid row440 := by decide
private def row441 : Entry := ⟨50340976,(7,904),1,0,true,0xf2b400000b1040,0x65544d28602fb80,0xa6481f⟩
private theorem check441 : valid row441 := by decide
private def row442 : Entry := ⟨50348648,(13,2848),1,12,true,0x32b40006005130,0x65548c2400afb87,0xa6489c⟩
private theorem check442 : valid row442 := by decide
private def row443 : Entry := ⟨50366032,(25,2656),1,11,true,0x32b40280248b30,0x65644d0060ef2c0,0xa6581f⟩
private theorem check443 : valid row443 := by decide
private def row444 : Entry := ⟨50373712,(37,2440),9,3,false,0xf2b40280088040,0x65644d00602f2c0,0xa6681f⟩
private theorem check444 : valid row444 := by decide
private def row445 : Entry := ⟨50464328,(37,2440),3,1,true,0x324c0491031b10,0x65600c2470afb80,0xa6589c⟩
private theorem check445 : valid row445 := by decide
private def row446 : Entry := ⟨50479688,(7,904),9,12,false,0x324c0486005110,0x65600c2400afb87,0xa6589c⟩
private theorem check446 : valid row446 := by decide
private def row447 : Entry := ⟨50497088,(25,2656),1,7,false,0x324c0291248b10,0x65600e0070ef2c0,0xa6589f⟩
private theorem check447 : valid row447 := by decide
private def row448 : Entry := ⟨50595352,(21,2720),9,5,true,0x17b56540031530,0x6c044c2460afb80,0xaa581c⟩
private theorem check448 : valid row448 := by decide
private def row449 : Entry := ⟨50628112,(37,2440),3,1,false,0x17b56280248530,0x6c044d0060ef2c0,0xaa581f⟩
private theorem check449 : valid row449 := by decide
private def row450 : Entry := ⟨50726408,(21,2720),9,1,false,0x174d6491031510,0x6c000c2470afb80,0xaa589c⟩
private theorem check450 : valid row450 := by decide
private def row451 : Entry := ⟨50857016,(41,2370),3,3,true,0x6f2699000018b30,0x1544c2460afb80,0xaa481c⟩
private theorem check451 : valid row451 := by decide
private def row452 : Entry := ⟨50865200,(41,2370),3,1,false,0xf2699000098040,0x1544d28602fb80,0xaa481f⟩
private theorem check452 : valid row452 := by decide
private def row453 : Entry := ⟨51119128,(21,2720),9,3,false,0x6d7696540018530,0x44c2460afb80,0xaa681c⟩
private theorem check453 : valid row453 := by decide
private def row454 : Entry := ⟨51380848,(13,2848),3,3,true,0x1e740000731b30,0x65544d2860efb9f,0xa64800⟩
private theorem check454 : valid row454 := by decide
private def row455 : Entry := ⟨51388528,(7,904),1,9,false,0xde7400000b1040,0x65544d28602fb9f,0xa64800⟩
private theorem check455 : valid row455 := by decide
private def row456 : Entry := ⟨51397216,(19,708),1,8,false,0x1e740006705130,0x65548e2800efb87,0xa64880⟩
private theorem check456 : valid row456 := by decide
private def row457 : Entry := ⟨51413584,(37,2440),1,9,false,0x1e740280248b30,0x65644d0060ef2df,0xa65800⟩
private theorem check457 : valid row457 := by decide
private def row458 : Entry := ⟨52429928,(19,708),1,1,true,0x8a1b40020031b30,0x65548c2470af8c0,0xa6401c⟩
private theorem check458 : valid row458 := by decide
private def row459 : Entry := ⟨52438112,(13,2848),3,11,false,0xe1b400200b1040,0x65548e28702f8c0,0xa6401f⟩
private theorem check459 : valid row459 := by decide
private def row460 : Entry := ⟨52445288,(13,2848),1,10,false,0x8a1b40006005130,0x65548c2400af8c7,0xa6401c⟩
private theorem check460 : valid row460 := by decide
private def row461 : Entry := ⟨52560968,(13,2848),9,1,false,0x8a14c0491031b10,0x65600c2470af8c0,0xa6601c⟩
private theorem check461 : valid row461 := by decide
private def row462 : Entry := ⟨52954152,(133,808),1,10,false,0x6e1699020018b30,0x1548c2470af8c0,0xaa401c⟩
private theorem check462 : valid row462 := by decide
private def row463 : Entry := ⟨58720824,(7,904),1,1,true,0x32b69000031b28,0x6d544c2460afaea,0x2481c⟩
private theorem check463 : valid row463 := by decide
private def row464 : Entry := ⟨58737192,(37,2440),9,12,false,0x32b69006005128,0x6d548c2400afac7,0x2489c⟩
private theorem check464 : valid row464 := by decide
private def row465 : Entry := ⟨58982936,(41,2370),3,4,false,0x17b56540031528,0x6c044c2460afaea,0x2581c⟩
private theorem check465 : valid row465 := by decide
private def row466 : Entry := ⟨59244600,(7,904),1,10,false,0x6f2699000018b28,0x1544c2460afaea,0x2481c⟩
private theorem check466 : valid row466 := by decide
private def row467 : Entry := ⟨59769392,(13,2848),3,1,false,0x1e769000731b28,0x6d544d2860efadf,0x24800⟩
private theorem check467 : valid row467 := by decide
private def group0 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row0 else row1) else (if t.val < 3 then row2 else row3)) else (if t.val < 6 then (if t.val < 5 then row4 else row5) else (if t.val < 7 then row6 else (if t.val < 8 then row7 else row8)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row9 else row10) else (if t.val < 12 then row11 else row12)) else (if t.val < 15 then (if t.val < 14 then row13 else row14) else (if t.val < 16 then row15 else (if t.val < 17 then row16 else row17)))))
private theorem groupOk0 (t : Fin 18) : valid (group0 t) := by
  fin_cases t
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
private def group1 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row18 else row19) else (if t.val < 3 then row20 else row21)) else (if t.val < 6 then (if t.val < 5 then row22 else row23) else (if t.val < 7 then row24 else (if t.val < 8 then row25 else row26)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row27 else row28) else (if t.val < 12 then row29 else row30)) else (if t.val < 15 then (if t.val < 14 then row31 else row32) else (if t.val < 16 then row33 else (if t.val < 17 then row34 else row35)))))
private theorem groupOk1 (t : Fin 18) : valid (group1 t) := by
  fin_cases t
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
private def group2 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row36 else row37) else (if t.val < 3 then row38 else row39)) else (if t.val < 6 then (if t.val < 5 then row40 else row41) else (if t.val < 7 then row42 else (if t.val < 8 then row43 else row44)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row45 else row46) else (if t.val < 12 then row47 else row48)) else (if t.val < 15 then (if t.val < 14 then row49 else row50) else (if t.val < 16 then row51 else (if t.val < 17 then row52 else row53)))))
private theorem groupOk2 (t : Fin 18) : valid (group2 t) := by
  fin_cases t
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
private def group3 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row54 else row55) else (if t.val < 3 then row56 else row57)) else (if t.val < 6 then (if t.val < 5 then row58 else row59) else (if t.val < 7 then row60 else (if t.val < 8 then row61 else row62)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row63 else row64) else (if t.val < 12 then row65 else row66)) else (if t.val < 15 then (if t.val < 14 then row67 else row68) else (if t.val < 16 then row69 else (if t.val < 17 then row70 else row71)))))
private theorem groupOk3 (t : Fin 18) : valid (group3 t) := by
  fin_cases t
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63
  · exact check64
  · exact check65
  · exact check66
  · exact check67
  · exact check68
  · exact check69
  · exact check70
  · exact check71
private def group4 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row72 else row73) else (if t.val < 3 then row74 else row75)) else (if t.val < 6 then (if t.val < 5 then row76 else row77) else (if t.val < 7 then row78 else (if t.val < 8 then row79 else row80)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row81 else row82) else (if t.val < 12 then row83 else row84)) else (if t.val < 15 then (if t.val < 14 then row85 else row86) else (if t.val < 16 then row87 else (if t.val < 17 then row88 else row89)))))
private theorem groupOk4 (t : Fin 18) : valid (group4 t) := by
  fin_cases t
  · exact check72
  · exact check73
  · exact check74
  · exact check75
  · exact check76
  · exact check77
  · exact check78
  · exact check79
  · exact check80
  · exact check81
  · exact check82
  · exact check83
  · exact check84
  · exact check85
  · exact check86
  · exact check87
  · exact check88
  · exact check89
private def group5 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row90 else row91) else (if t.val < 3 then row92 else row93)) else (if t.val < 6 then (if t.val < 5 then row94 else row95) else (if t.val < 7 then row96 else (if t.val < 8 then row97 else row98)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row99 else row100) else (if t.val < 12 then row101 else row102)) else (if t.val < 15 then (if t.val < 14 then row103 else row104) else (if t.val < 16 then row105 else (if t.val < 17 then row106 else row107)))))
private theorem groupOk5 (t : Fin 18) : valid (group5 t) := by
  fin_cases t
  · exact check90
  · exact check91
  · exact check92
  · exact check93
  · exact check94
  · exact check95
  · exact check96
  · exact check97
  · exact check98
  · exact check99
  · exact check100
  · exact check101
  · exact check102
  · exact check103
  · exact check104
  · exact check105
  · exact check106
  · exact check107
private def group6 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row108 else row109) else (if t.val < 3 then row110 else row111)) else (if t.val < 6 then (if t.val < 5 then row112 else row113) else (if t.val < 7 then row114 else (if t.val < 8 then row115 else row116)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row117 else row118) else (if t.val < 12 then row119 else row120)) else (if t.val < 15 then (if t.val < 14 then row121 else row122) else (if t.val < 16 then row123 else (if t.val < 17 then row124 else row125)))))
private theorem groupOk6 (t : Fin 18) : valid (group6 t) := by
  fin_cases t
  · exact check108
  · exact check109
  · exact check110
  · exact check111
  · exact check112
  · exact check113
  · exact check114
  · exact check115
  · exact check116
  · exact check117
  · exact check118
  · exact check119
  · exact check120
  · exact check121
  · exact check122
  · exact check123
  · exact check124
  · exact check125
private def group7 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row126 else row127) else (if t.val < 3 then row128 else row129)) else (if t.val < 6 then (if t.val < 5 then row130 else row131) else (if t.val < 7 then row132 else (if t.val < 8 then row133 else row134)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row135 else row136) else (if t.val < 12 then row137 else row138)) else (if t.val < 15 then (if t.val < 14 then row139 else row140) else (if t.val < 16 then row141 else (if t.val < 17 then row142 else row143)))))
private theorem groupOk7 (t : Fin 18) : valid (group7 t) := by
  fin_cases t
  · exact check126
  · exact check127
  · exact check128
  · exact check129
  · exact check130
  · exact check131
  · exact check132
  · exact check133
  · exact check134
  · exact check135
  · exact check136
  · exact check137
  · exact check138
  · exact check139
  · exact check140
  · exact check141
  · exact check142
  · exact check143
private def group8 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row144 else row145) else (if t.val < 3 then row146 else row147)) else (if t.val < 6 then (if t.val < 5 then row148 else row149) else (if t.val < 7 then row150 else (if t.val < 8 then row151 else row152)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row153 else row154) else (if t.val < 12 then row155 else row156)) else (if t.val < 15 then (if t.val < 14 then row157 else row158) else (if t.val < 16 then row159 else (if t.val < 17 then row160 else row161)))))
private theorem groupOk8 (t : Fin 18) : valid (group8 t) := by
  fin_cases t
  · exact check144
  · exact check145
  · exact check146
  · exact check147
  · exact check148
  · exact check149
  · exact check150
  · exact check151
  · exact check152
  · exact check153
  · exact check154
  · exact check155
  · exact check156
  · exact check157
  · exact check158
  · exact check159
  · exact check160
  · exact check161
private def group9 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row162 else row163) else (if t.val < 3 then row164 else row165)) else (if t.val < 6 then (if t.val < 5 then row166 else row167) else (if t.val < 7 then row168 else (if t.val < 8 then row169 else row170)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row171 else row172) else (if t.val < 12 then row173 else row174)) else (if t.val < 15 then (if t.val < 14 then row175 else row176) else (if t.val < 16 then row177 else (if t.val < 17 then row178 else row179)))))
private theorem groupOk9 (t : Fin 18) : valid (group9 t) := by
  fin_cases t
  · exact check162
  · exact check163
  · exact check164
  · exact check165
  · exact check166
  · exact check167
  · exact check168
  · exact check169
  · exact check170
  · exact check171
  · exact check172
  · exact check173
  · exact check174
  · exact check175
  · exact check176
  · exact check177
  · exact check178
  · exact check179
private def group10 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row180 else row181) else (if t.val < 3 then row182 else row183)) else (if t.val < 6 then (if t.val < 5 then row184 else row185) else (if t.val < 7 then row186 else (if t.val < 8 then row187 else row188)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row189 else row190) else (if t.val < 12 then row191 else row192)) else (if t.val < 15 then (if t.val < 14 then row193 else row194) else (if t.val < 16 then row195 else (if t.val < 17 then row196 else row197)))))
private theorem groupOk10 (t : Fin 18) : valid (group10 t) := by
  fin_cases t
  · exact check180
  · exact check181
  · exact check182
  · exact check183
  · exact check184
  · exact check185
  · exact check186
  · exact check187
  · exact check188
  · exact check189
  · exact check190
  · exact check191
  · exact check192
  · exact check193
  · exact check194
  · exact check195
  · exact check196
  · exact check197
private def group11 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row198 else row199) else (if t.val < 3 then row200 else row201)) else (if t.val < 6 then (if t.val < 5 then row202 else row203) else (if t.val < 7 then row204 else (if t.val < 8 then row205 else row206)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row207 else row208) else (if t.val < 12 then row209 else row210)) else (if t.val < 15 then (if t.val < 14 then row211 else row212) else (if t.val < 16 then row213 else (if t.val < 17 then row214 else row215)))))
private theorem groupOk11 (t : Fin 18) : valid (group11 t) := by
  fin_cases t
  · exact check198
  · exact check199
  · exact check200
  · exact check201
  · exact check202
  · exact check203
  · exact check204
  · exact check205
  · exact check206
  · exact check207
  · exact check208
  · exact check209
  · exact check210
  · exact check211
  · exact check212
  · exact check213
  · exact check214
  · exact check215
private def group12 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row216 else row217) else (if t.val < 3 then row218 else row219)) else (if t.val < 6 then (if t.val < 5 then row220 else row221) else (if t.val < 7 then row222 else (if t.val < 8 then row223 else row224)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row225 else row226) else (if t.val < 12 then row227 else row228)) else (if t.val < 15 then (if t.val < 14 then row229 else row230) else (if t.val < 16 then row231 else (if t.val < 17 then row232 else row233)))))
private theorem groupOk12 (t : Fin 18) : valid (group12 t) := by
  fin_cases t
  · exact check216
  · exact check217
  · exact check218
  · exact check219
  · exact check220
  · exact check221
  · exact check222
  · exact check223
  · exact check224
  · exact check225
  · exact check226
  · exact check227
  · exact check228
  · exact check229
  · exact check230
  · exact check231
  · exact check232
  · exact check233
private def group13 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row234 else row235) else (if t.val < 3 then row236 else row237)) else (if t.val < 6 then (if t.val < 5 then row238 else row239) else (if t.val < 7 then row240 else (if t.val < 8 then row241 else row242)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row243 else row244) else (if t.val < 12 then row245 else row246)) else (if t.val < 15 then (if t.val < 14 then row247 else row248) else (if t.val < 16 then row249 else (if t.val < 17 then row250 else row251)))))
private theorem groupOk13 (t : Fin 18) : valid (group13 t) := by
  fin_cases t
  · exact check234
  · exact check235
  · exact check236
  · exact check237
  · exact check238
  · exact check239
  · exact check240
  · exact check241
  · exact check242
  · exact check243
  · exact check244
  · exact check245
  · exact check246
  · exact check247
  · exact check248
  · exact check249
  · exact check250
  · exact check251
private def group14 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row252 else row253) else (if t.val < 3 then row254 else row255)) else (if t.val < 6 then (if t.val < 5 then row256 else row257) else (if t.val < 7 then row258 else (if t.val < 8 then row259 else row260)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row261 else row262) else (if t.val < 12 then row263 else row264)) else (if t.val < 15 then (if t.val < 14 then row265 else row266) else (if t.val < 16 then row267 else (if t.val < 17 then row268 else row269)))))
private theorem groupOk14 (t : Fin 18) : valid (group14 t) := by
  fin_cases t
  · exact check252
  · exact check253
  · exact check254
  · exact check255
  · exact check256
  · exact check257
  · exact check258
  · exact check259
  · exact check260
  · exact check261
  · exact check262
  · exact check263
  · exact check264
  · exact check265
  · exact check266
  · exact check267
  · exact check268
  · exact check269
private def group15 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row270 else row271) else (if t.val < 3 then row272 else row273)) else (if t.val < 6 then (if t.val < 5 then row274 else row275) else (if t.val < 7 then row276 else (if t.val < 8 then row277 else row278)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row279 else row280) else (if t.val < 12 then row281 else row282)) else (if t.val < 15 then (if t.val < 14 then row283 else row284) else (if t.val < 16 then row285 else (if t.val < 17 then row286 else row287)))))
private theorem groupOk15 (t : Fin 18) : valid (group15 t) := by
  fin_cases t
  · exact check270
  · exact check271
  · exact check272
  · exact check273
  · exact check274
  · exact check275
  · exact check276
  · exact check277
  · exact check278
  · exact check279
  · exact check280
  · exact check281
  · exact check282
  · exact check283
  · exact check284
  · exact check285
  · exact check286
  · exact check287
private def group16 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row288 else row289) else (if t.val < 3 then row290 else row291)) else (if t.val < 6 then (if t.val < 5 then row292 else row293) else (if t.val < 7 then row294 else (if t.val < 8 then row295 else row296)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row297 else row298) else (if t.val < 12 then row299 else row300)) else (if t.val < 15 then (if t.val < 14 then row301 else row302) else (if t.val < 16 then row303 else (if t.val < 17 then row304 else row305)))))
private theorem groupOk16 (t : Fin 18) : valid (group16 t) := by
  fin_cases t
  · exact check288
  · exact check289
  · exact check290
  · exact check291
  · exact check292
  · exact check293
  · exact check294
  · exact check295
  · exact check296
  · exact check297
  · exact check298
  · exact check299
  · exact check300
  · exact check301
  · exact check302
  · exact check303
  · exact check304
  · exact check305
private def group17 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row306 else row307) else (if t.val < 3 then row308 else row309)) else (if t.val < 6 then (if t.val < 5 then row310 else row311) else (if t.val < 7 then row312 else (if t.val < 8 then row313 else row314)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row315 else row316) else (if t.val < 12 then row317 else row318)) else (if t.val < 15 then (if t.val < 14 then row319 else row320) else (if t.val < 16 then row321 else (if t.val < 17 then row322 else row323)))))
private theorem groupOk17 (t : Fin 18) : valid (group17 t) := by
  fin_cases t
  · exact check306
  · exact check307
  · exact check308
  · exact check309
  · exact check310
  · exact check311
  · exact check312
  · exact check313
  · exact check314
  · exact check315
  · exact check316
  · exact check317
  · exact check318
  · exact check319
  · exact check320
  · exact check321
  · exact check322
  · exact check323
private def group18 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row324 else row325) else (if t.val < 3 then row326 else row327)) else (if t.val < 6 then (if t.val < 5 then row328 else row329) else (if t.val < 7 then row330 else (if t.val < 8 then row331 else row332)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row333 else row334) else (if t.val < 12 then row335 else row336)) else (if t.val < 15 then (if t.val < 14 then row337 else row338) else (if t.val < 16 then row339 else (if t.val < 17 then row340 else row341)))))
private theorem groupOk18 (t : Fin 18) : valid (group18 t) := by
  fin_cases t
  · exact check324
  · exact check325
  · exact check326
  · exact check327
  · exact check328
  · exact check329
  · exact check330
  · exact check331
  · exact check332
  · exact check333
  · exact check334
  · exact check335
  · exact check336
  · exact check337
  · exact check338
  · exact check339
  · exact check340
  · exact check341
private def group19 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row342 else row343) else (if t.val < 3 then row344 else row345)) else (if t.val < 6 then (if t.val < 5 then row346 else row347) else (if t.val < 7 then row348 else (if t.val < 8 then row349 else row350)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row351 else row352) else (if t.val < 12 then row353 else row354)) else (if t.val < 15 then (if t.val < 14 then row355 else row356) else (if t.val < 16 then row357 else (if t.val < 17 then row358 else row359)))))
private theorem groupOk19 (t : Fin 18) : valid (group19 t) := by
  fin_cases t
  · exact check342
  · exact check343
  · exact check344
  · exact check345
  · exact check346
  · exact check347
  · exact check348
  · exact check349
  · exact check350
  · exact check351
  · exact check352
  · exact check353
  · exact check354
  · exact check355
  · exact check356
  · exact check357
  · exact check358
  · exact check359
private def group20 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row360 else row361) else (if t.val < 3 then row362 else row363)) else (if t.val < 6 then (if t.val < 5 then row364 else row365) else (if t.val < 7 then row366 else (if t.val < 8 then row367 else row368)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row369 else row370) else (if t.val < 12 then row371 else row372)) else (if t.val < 15 then (if t.val < 14 then row373 else row374) else (if t.val < 16 then row375 else (if t.val < 17 then row376 else row377)))))
private theorem groupOk20 (t : Fin 18) : valid (group20 t) := by
  fin_cases t
  · exact check360
  · exact check361
  · exact check362
  · exact check363
  · exact check364
  · exact check365
  · exact check366
  · exact check367
  · exact check368
  · exact check369
  · exact check370
  · exact check371
  · exact check372
  · exact check373
  · exact check374
  · exact check375
  · exact check376
  · exact check377
private def group21 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row378 else row379) else (if t.val < 3 then row380 else row381)) else (if t.val < 6 then (if t.val < 5 then row382 else row383) else (if t.val < 7 then row384 else (if t.val < 8 then row385 else row386)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row387 else row388) else (if t.val < 12 then row389 else row390)) else (if t.val < 15 then (if t.val < 14 then row391 else row392) else (if t.val < 16 then row393 else (if t.val < 17 then row394 else row395)))))
private theorem groupOk21 (t : Fin 18) : valid (group21 t) := by
  fin_cases t
  · exact check378
  · exact check379
  · exact check380
  · exact check381
  · exact check382
  · exact check383
  · exact check384
  · exact check385
  · exact check386
  · exact check387
  · exact check388
  · exact check389
  · exact check390
  · exact check391
  · exact check392
  · exact check393
  · exact check394
  · exact check395
private def group22 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row396 else row397) else (if t.val < 3 then row398 else row399)) else (if t.val < 6 then (if t.val < 5 then row400 else row401) else (if t.val < 7 then row402 else (if t.val < 8 then row403 else row404)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row405 else row406) else (if t.val < 12 then row407 else row408)) else (if t.val < 15 then (if t.val < 14 then row409 else row410) else (if t.val < 16 then row411 else (if t.val < 17 then row412 else row413)))))
private theorem groupOk22 (t : Fin 18) : valid (group22 t) := by
  fin_cases t
  · exact check396
  · exact check397
  · exact check398
  · exact check399
  · exact check400
  · exact check401
  · exact check402
  · exact check403
  · exact check404
  · exact check405
  · exact check406
  · exact check407
  · exact check408
  · exact check409
  · exact check410
  · exact check411
  · exact check412
  · exact check413
private def group23 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row414 else row415) else (if t.val < 3 then row416 else row417)) else (if t.val < 6 then (if t.val < 5 then row418 else row419) else (if t.val < 7 then row420 else (if t.val < 8 then row421 else row422)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row423 else row424) else (if t.val < 12 then row425 else row426)) else (if t.val < 15 then (if t.val < 14 then row427 else row428) else (if t.val < 16 then row429 else (if t.val < 17 then row430 else row431)))))
private theorem groupOk23 (t : Fin 18) : valid (group23 t) := by
  fin_cases t
  · exact check414
  · exact check415
  · exact check416
  · exact check417
  · exact check418
  · exact check419
  · exact check420
  · exact check421
  · exact check422
  · exact check423
  · exact check424
  · exact check425
  · exact check426
  · exact check427
  · exact check428
  · exact check429
  · exact check430
  · exact check431
private def group24 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row432 else row433) else (if t.val < 3 then row434 else row435)) else (if t.val < 6 then (if t.val < 5 then row436 else row437) else (if t.val < 7 then row438 else (if t.val < 8 then row439 else row440)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row441 else row442) else (if t.val < 12 then row443 else row444)) else (if t.val < 15 then (if t.val < 14 then row445 else row446) else (if t.val < 16 then row447 else (if t.val < 17 then row448 else row449)))))
private theorem groupOk24 (t : Fin 18) : valid (group24 t) := by
  fin_cases t
  · exact check432
  · exact check433
  · exact check434
  · exact check435
  · exact check436
  · exact check437
  · exact check438
  · exact check439
  · exact check440
  · exact check441
  · exact check442
  · exact check443
  · exact check444
  · exact check445
  · exact check446
  · exact check447
  · exact check448
  · exact check449
private def group25 (t : Fin 18) : Entry :=
  (if t.val < 9 then (if t.val < 4 then (if t.val < 2 then (if t.val < 1 then row450 else row451) else (if t.val < 3 then row452 else row453)) else (if t.val < 6 then (if t.val < 5 then row454 else row455) else (if t.val < 7 then row456 else (if t.val < 8 then row457 else row458)))) else (if t.val < 13 then (if t.val < 11 then (if t.val < 10 then row459 else row460) else (if t.val < 12 then row461 else row462)) else (if t.val < 15 then (if t.val < 14 then row463 else row464) else (if t.val < 16 then row465 else (if t.val < 17 then row466 else row467)))))
private theorem groupOk25 (t : Fin 18) : valid (group25 t) := by
  fin_cases t
  · exact check450
  · exact check451
  · exact check452
  · exact check453
  · exact check454
  · exact check455
  · exact check456
  · exact check457
  · exact check458
  · exact check459
  · exact check460
  · exact check461
  · exact check462
  · exact check463
  · exact check464
  · exact check465
  · exact check466
  · exact check467
private def group (b : Fin 26) : Fin 18 → Entry :=
  (if b.val < 13 then (if b.val < 6 then (if b.val < 3 then (if b.val < 1 then group0 else (if b.val < 2 then group1 else group2)) else (if b.val < 4 then group3 else (if b.val < 5 then group4 else group5))) else (if b.val < 9 then (if b.val < 7 then group6 else (if b.val < 8 then group7 else group8)) else (if b.val < 11 then (if b.val < 10 then group9 else group10) else (if b.val < 12 then group11 else group12)))) else (if b.val < 19 then (if b.val < 16 then (if b.val < 14 then group13 else (if b.val < 15 then group14 else group15)) else (if b.val < 17 then group16 else (if b.val < 18 then group17 else group18))) else (if b.val < 22 then (if b.val < 20 then group19 else (if b.val < 21 then group20 else group21)) else (if b.val < 24 then (if b.val < 23 then group22 else group23) else (if b.val < 25 then group24 else group25)))))
private theorem groupOk (b : Fin 26) (t : Fin 18) : valid (group b t) := by
  fin_cases b
  · exact groupOk0 t
  · exact groupOk1 t
  · exact groupOk2 t
  · exact groupOk3 t
  · exact groupOk4 t
  · exact groupOk5 t
  · exact groupOk6 t
  · exact groupOk7 t
  · exact groupOk8 t
  · exact groupOk9 t
  · exact groupOk10 t
  · exact groupOk11 t
  · exact groupOk12 t
  · exact groupOk13 t
  · exact groupOk14 t
  · exact groupOk15 t
  · exact groupOk16 t
  · exact groupOk17 t
  · exact groupOk18 t
  · exact groupOk19 t
  · exact groupOk20 t
  · exact groupOk21 t
  · exact groupOk22 t
  · exact groupOk23 t
  · exact groupOk24 t
  · exact groupOk25 t

private def entry (i : Fin 468) : Entry :=
  group ⟨i.val / 18, by omega⟩ ⟨i.val % 18, Nat.mod_lt _ (by decide)⟩
private theorem entryOk (i : Fin 468) : valid (entry i) := groupOk _ _
private def nm (i : Fin 468) := (entry i).mask
private def pivot (i : Fin 468) := chooseFlag (entry i)
private def pos := pm
private def neg := nm
private theorem pos_ok (k : Fin 52) : pos k = pm k := rfl
private theorem neg_ok (i : Fin 468) : neg i = nm i := rfl
private theorem checked (i : Fin 468) (k : Fin 26) (h : (nm i).testBit k.val = false) :
    pm (pivot i k) &&& (nm i ||| 2^k.val) = pm (pivot i k) := (entryOk i).2.2.2 k h
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem neg_bounded : ∀ i, nm i < 2^26 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem ordered : ∀ k : Fin 467, nm k.castSucc < nm k.succ := by decide
private theorem distinct_rows : Function.Injective nm := (Fin.strictMono_iff_lt_succ.mpr ordered).injective
-- A missing vertex can be added to a negative row to expose an incident edge.
-- If the other negative already contains it, this positive row lies in their union.
private theorem added_mix (i j : Fin 468) (k : Fin 26) (hi : (nm i).testBit k.val = false)
    (hj : (nm j).testBit k.val = true) :
    mix (bits (pm (pivot i k))) (bits (nm i)) (bits (nm j)) := by
  intro t ht
  by_cases h : t < 26
  · let q : Fin 26 := ⟨t,h⟩
    change (bits (pm (pivot i k))).getD q.val false = true at ht
    change (bits (nm i)).getD q.val false = true ∨ (bits (nm j)).getD q.val false = true
    rw [bit_at] at ht
    rw [bit_at,bit_at]
    have e := congrArg (fun n : Nat => n.testBit q.val) (checked i k hi)
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_two_pow,ht,Bool.true_and] at e
    rcases Bool.or_eq_true_iff.mp e with hit | same
    · exact Or.inl hit
    · exact Or.inr ((of_decide_eq_true same : k.val = q.val) ▸ hj)
  · rw [List.getD_eq_default _ _ (by simp [bits]; omega)] at ht
    cases ht

private def observe {m : Nat} (C : Circuit) (pick : Fin m → Nat) (j : Fin 468) :=
  fun k => (C.wires (bits (nm j))).getD (pick k) false
private theorem agree_bit {m : Nat} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (pick : Fin m → Nat) (cover : covers pick C.gates)
    (positive : ∀ s, C.eval (bits (pos s)) = true)
    (negative : ∀ s, C.eval (bits (neg s)) = false)
    (i j : Fin 468) (same : observe C pick i = observe C pick j) (k : Fin 26)
    (hj : (nm j).testBit k.val = true) : (nm i).testBit k.val = true := by
  cases hi : (nm i).testBit k.val with
  | true => rfl
  | false =>
    have split := propagate pick C.gates _ _ _
      (by simp [bits]) (by simp [bits]) (added_mix i j k hi hj)
      hC cover (congrFun same)
    have hp := positive (pivot i k)
    rw [pos_ok] at hp
    have deny_i := negative i
    have deny_j := negative j
    rw [neg_ok] at deny_i deny_j
    have out : C.eval (bits (nm i)) = true ∨ C.eval (bits (nm j)) = true := split C.output hp
    rcases out with h | h
    · simp_all
    · simp_all
private theorem observe_inj {m : Nat} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (pick : Fin m → Nat) (cover : covers pick C.gates)
    (positive : ∀ s, C.eval (bits (pos s)) = true)
    (negative : ∀ s, C.eval (bits (neg s)) = false) : Function.Injective (observe C pick) := by
  intro i j same
  apply distinct_rows
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 26
  · let k : Fin 26 := ⟨t,ht⟩
    have h1 := agree_bit C hC pick cover positive negative i j same k
    have h2 := agree_bit C hC pick cover positive negative j i same.symm k
    change (nm i).testBit k.val = (nm j).testBit k.val
    cases e1 : (nm i).testBit k.val <;> cases e2 : (nm j).testBit k.val <;> simp_all
  · have hpow : (2:Nat)^26 ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (neg_bounded i) hpow),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (neg_bounded j) hpow)]
private theorem sample_cover :
    ∀ (C : Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ s, C.eval (bits (pos s)) = true) → (∀ s, C.eval (bits (neg s)) = false) →
    ∀ (m : Nat) (pick : Fin m → Nat), covers pick C.gates →
      Function.Injective (fun (j : Fin 468) (k : Fin m) => (C.wires (bits (neg j))).getD (pick k) false) ∧ 9 ≤ m := by
  intro C mono positive negative m pick cover
  have inj := observe_inj C mono pick cover positive negative
  refine ⟨?_, ?_⟩
  · simp only [neg_ok]
    exact inj
  have count := Fintype.card_le_of_injective (observe C pick) inj
  have lower : 468 ≤ 2^m := by simpa using count
  by_contra! small
  have upper : (2:Nat)^m ≤ 2^8 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private def point (i : Fin 52) : Fin 13 := ((if i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 3)) else (if i.val < 4 then 9 else (if i.val < 5 then 1 else 2))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 10 else 2)) else (if i.val < 11 then (if i.val < 10 then 3 else 5) else (if i.val < 12 then 11 else 3)))) else (if i.val < 19 then (if i.val < 16 then (if i.val < 14 then 4 else (if i.val < 15 then 6 else 12)) else (if i.val < 17 then 0 else (if i.val < 18 then 4 else 5))) else (if i.val < 22 then (if i.val < 20 then 7 else (if i.val < 21 then 1 else 5)) else (if i.val < 24 then (if i.val < 23 then 6 else 8) else (if i.val < 25 then 2 else 6))))) else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then (if i.val < 27 then 7 else (if i.val < 28 then 9 else 3)) else (if i.val < 30 then 7 else (if i.val < 31 then 8 else 10))) else (if i.val < 35 then (if i.val < 33 then 4 else (if i.val < 34 then 8 else 9)) else (if i.val < 37 then (if i.val < 36 then 11 else 5) else (if i.val < 38 then 9 else 10)))) else (if i.val < 45 then (if i.val < 42 then (if i.val < 40 then 12 else (if i.val < 41 then 0 else 6)) else (if i.val < 43 then 10 else (if i.val < 44 then 11 else 1))) else (if i.val < 48 then (if i.val < 46 then 7 else (if i.val < 47 then 11 else 12)) else (if i.val < 50 then (if i.val < 49 then 0 else 2) else (if i.val < 51 then 8 else 12)))))) : Fin 13)
private def line (i : Fin 52) : Fin 13 := ((if i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 0)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 2)) else (if i.val < 11 then (if i.val < 10 then 2 else 2) else (if i.val < 12 then 2 else 3)))) else (if i.val < 19 then (if i.val < 16 then (if i.val < 14 then 3 else (if i.val < 15 then 3 else 3)) else (if i.val < 17 then 4 else (if i.val < 18 then 4 else 4))) else (if i.val < 22 then (if i.val < 20 then 4 else (if i.val < 21 then 5 else 5)) else (if i.val < 24 then (if i.val < 23 then 5 else 5) else (if i.val < 25 then 6 else 6))))) else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then (if i.val < 27 then 6 else (if i.val < 28 then 6 else 7)) else (if i.val < 30 then 7 else (if i.val < 31 then 7 else 7))) else (if i.val < 35 then (if i.val < 33 then 8 else (if i.val < 34 then 8 else 8)) else (if i.val < 37 then (if i.val < 36 then 8 else 9) else (if i.val < 38 then 9 else 9)))) else (if i.val < 45 then (if i.val < 42 then (if i.val < 40 then 9 else (if i.val < 41 then 10 else 10)) else (if i.val < 43 then 10 else (if i.val < 44 then 10 else 11))) else (if i.val < 48 then (if i.val < 46 then 11 else (if i.val < 47 then 11 else 11)) else (if i.val < 50 then (if i.val < 49 then 12 else 12) else (if i.val < 51 then 12 else 12)))))) : Fin 13)

private def representative (i : Fin 468) := (entry i).rep
private def multiplier (i : Fin 468) := (entry i).a
private def offset (i : Fin 468) := (entry i).t
private def dual (i : Fin 468) := (entry i).dual
private def sample (i : Fin 468) := orbit (representative i) (multiplier i) (offset i) (dual i)
private theorem key_ok (i : Fin 468) : representative i ∈ reps ∧ multiplier i ∈ multipliers :=
  ⟨(entryOk i).1,(entryOk i).2.1⟩
private theorem sample_ok (i : Fin 468) : List.ofFn (sample i) = bits (nm i) := (entryOk i).2.2.1
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem flag_ok : ∀ s, (∃ d ∈ differences, point s = line s + d) ∧
    List.ofFn (flag (point s) (line s)) = bits (pm s) := by decide
-- The other eight coordinates distinguish all rows in a fiber of one coordinate.
theorem fiber_bound (f : Fin 468 → Fin 9 → Bool) (inj : Function.Injective f)
    (k : Fin 9) (b : Bool) :
    (Finset.univ.filter (fun j => f j k = b)).card ≤ 256 := by
  let S := Finset.univ.filter (fun j => f j k = b)
  let cut (j : ↥S) (t : Fin 8) := f j.val (k.succAbove t)
  have embed : Function.Injective cut := by
    intro i j h
    apply Subtype.ext
    apply inj
    funext t
    by_cases ht : t = k
    · subst t
      exact (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm
    · obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq ht
      exact congrFun h u
  have bound := Fintype.card_le_of_injective cut embed
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at bound
  exact bound
private def off (r : Fin 26) : Finset (Fin 468) :=
  Finset.univ.filter (fun j => (nm j).testBit r.val = false)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount0 : (off 0).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount1 : (off 1).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount2 : (off 2).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount3 : (off 3).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount4 : (off 4).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount5 : (off 5).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount6 : (off 6).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount7 : (off 7).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount8 : (off 8).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount9 : (off 9).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount10 : (off 10).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount11 : (off 11).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount12 : (off 12).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount13 : (off 13).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount14 : (off 14).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount15 : (off 15).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount16 : (off 16).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount17 : (off 17).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount18 : (off 18).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount19 : (off 19).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount20 : (off 20).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount21 : (off 21).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount22 : (off 22).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount23 : (off 23).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount24 : (off 24).card = 342 := by decide
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem zeroCount25 : (off 25).card = 342 := by decide
private theorem raw_count (r : Fin 26) : (off r).card = 342 := by
  fin_cases r
  · exact zeroCount0
  · exact zeroCount1
  · exact zeroCount2
  · exact zeroCount3
  · exact zeroCount4
  · exact zeroCount5
  · exact zeroCount6
  · exact zeroCount7
  · exact zeroCount8
  · exact zeroCount9
  · exact zeroCount10
  · exact zeroCount11
  · exact zeroCount12
  · exact zeroCount13
  · exact zeroCount14
  · exact zeroCount15
  · exact zeroCount16
  · exact zeroCount17
  · exact zeroCount18
  · exact zeroCount19
  · exact zeroCount20
  · exact zeroCount21
  · exact zeroCount22
  · exact zeroCount23
  · exact zeroCount24
  · exact zeroCount25
private theorem internal_only (C : Circuit) (pick : Fin 9 → Nat)
    (inj : Function.Injective (observe C pick)) (k : Fin 9) : 26 ≤ pick k := by
  by_contra! small
  let r : Fin 26 := ⟨pick k,small⟩
  have agrees (j : Fin 468) : observe C pick j k = (nm j).testBit r.val := by
    change (C.gates.foldl addGate (bits (nm j))).getD r.val false = _
    rw [old_wire _ _ _ (by simpa only [bits,List.length_ofFn] using r.isLt),bit_at]
  have cap := fiber_bound (observe C pick) inj k false
  have eq : Finset.univ.filter (fun j => observe C pick j k = false) = off r := by
    ext j
    simp only [off,Finset.mem_filter,Finset.mem_univ,true_and,agrees]
  rw [eq,raw_count] at cap
  omega
end PEqualNP.Research.PlaneAndInputCover

open PEqualNP.Research.PlaneAndInputCover PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Research.PlaneAndInputCover :
    ∀ C : Circuit, Monotone2 C →
    (∀ p w : Fin 13, (∃ d ∈ differences, p = w+d) → circuitFun 26 C (flag p w) = true) →
    (∀ z ∈ reps, ∀ a ∈ multipliers, ∀ t d, circuitFun 26 C (orbit z a t d) = false) →
    ∀ (m : Nat) (pick : Fin m → Nat), covers pick C.gates →
      9 ≤ m ∧ (m = 9 → ∀ k, 26 ≤ pick k) ∧ ∃ rows : Fin 468 → (Fin 26 → Bool),
        (∀ j, ∃ z ∈ reps, ∃ a ∈ multipliers, ∃ t d, rows j = orbit z a t d) ∧
        Function.Injective (fun (j : Fin 468) (k : Fin m) =>
          (C.wires (List.ofFn (rows j))).getD (pick k) false) := by
  intro C mono hp hn m pick cover
  have positive (i : Fin 52) : C.eval (bits (pos i)) = true := by
    rw [pos_ok,← (flag_ok i).2]
    exact hp _ _ (flag_ok i).1
  have negative (i : Fin 468) : C.eval (bits (neg i)) = false := by
    rw [neg_ok,← sample_ok]
    exact hn _ (key_ok i).1 _ (key_ok i).2 _ _
  have h := sample_cover C mono positive negative m pick cover
  refine ⟨h.2, ?_, sample, ?_, ?_⟩
  · rintro rfl
    exact internal_only C pick (observe_inj C mono pick cover positive negative)
  · intro j
    exact ⟨_,(key_ok j).1,_,(key_ok j).2,_,_,rfl⟩
  · intro i j e
    apply h.1
    simpa only [sample_ok,neg_ok] using e
