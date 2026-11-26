import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35SecondFamily
open PlaneFirstAndSeparation PlaneFirstAndBudget PlaneCase35FourthOrBudget
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def omittedFlags : Nat := 1030807945728
private def indices (i : Nat) : Nat :=
  (0x1b3d96c761afd76b759abd3e9b4ba4d1e6b298cc5e2b1187c36170983c1607017fbf5f6f97bbd5e6f177bb5d6e973b85bedd6db65aed164b1586c15faf576b95bad566b157ab53e9d4da652e9548a3d1a8b44a1d0a8340994aa532893c9a49239147a3b1c8dc6a33168ac52271288c421b0c85c2a130883c1a09017fbf9f8fb7cbe1eef67abd1e6ea72b85c0df6f375b8db6d359aad469b49a2d067b399ac96431d8cc56230d82c05faf97abc5dae56cb459ac960af572b558ab552a550a75327d248a3f9f8fa6f371b4d86b349a0ce6632990c6622d968b2582b14ca04e26930964a249208e4622904803f1f0f4783b1b8cc6230170b4582b150a45025118843e1e0e870361a0c8602e160a85026110803c1a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0xea8002a6a100a2aa040a8ea000aa6980032e910222e908212e900232e88003ae818282a8142a0e8102a2e808292a8042a86500852a440898e2a040a6290422e28042ae22044a621848222124a062104a2220a4c062084c222060e0a2040e822024e0619082221828306180832e130a02e128242a124a40e120a42a114a20e110a22e1082522106860a104a602102870a0c0c1860b0c02e0a0c0a2092c206090c222082c30a060e08a050e80a048690a044a882042c90e038602e030e02e028642a024a48e01868220168a0a014aa02012ca0200a4d020068e0991022419020349900234988412818821309880138984021c98303049824308982030c98143201812124981032498043281802134d44001d140215453100255304061130206453000655290421d284029d2804291222444922044c12124245210425d2040691202464d140215d114221d110225d10c241d108251d10426111020745098501509412110925205090521108a5105088511d0841291082530906060cd04861110325049030704102a54090287401022544d01c301d018701d0143211012524d00c341100a5508c4009c4c101864b810224b210064b100260b030244b01026caa100a8a85028ca8102a8a4108cca2100e0a120a44a100a60a070a08a050a80a030a44989012098303049810328941214c930206c929202c921206c910226c909212090303488a5108c8a110a088b1104889112088712088851280883130886120c88492900843094c838302c830306c8293028825308881c380c81838208161a088143a008121a4080f180880d380080b19008071a0c64008d4540815c4c08194450885c444889044289404069c04390023438900343850214381023032304443210464310027430d0414309043030706043050610303064429840342904234289403c285029826140c425048542494810243484022b44042294420223444421848302124a4020f0c0420d0c1020b4c002070e041c18114194821419082341890130187820418582101838308161a04c1492110143814c130a06c12924201278408125a400123844c114a21c10d241010786080e1c0840c941100c3c1000b2d0040b0d0200ab50040a950200a790080a590800a3d004098503009692040949210092d20008b51000879208070e048065a080063c04c058681c054a810052c84c04d281004b490c0387020032d04002f140802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x8000200800000840000024000001200000010000000800000020000001000000080000002000000100000008000000400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x77c0001fd01efa28fb0000fc01aba00000fc037e9000000000006d60000da925842d810002890802d8a069000280040f8800c5040150000600000004040200037f6bea2eb0d03a0000000000000001ed515f281c8001ad1c0a030300288002000000000000000000000b78dfb590740000000000007cf3af6127a40c80503404fffffffffffffffc0000000000000000000000000000000000000000000000000000000000000001ffffffffffffff80000000000000000000000000000000003fff000000000000fffe00000000003ffffffffffff0000000000000000000001e001ffe0000000000003ffe00000007fff0000000040fffffff80000000000000f02000fff8000038001e00fe000003e007fe00000107ff80003ffff0000000044407007003f000038000e000ff00010e0380fe000043c03c001fc007fff800000002400780c43c001c000c00005f0044401c609e000018011c0013e27f0383f088e09c12305919e409c2218c3c0c78901809000cf808820c41830108307939860248098084004a88000000019189b30000424615638020c516b84242462213ba90120030298010b221484412a4201500418008c06da14858401a981b80cca51bc000015500a28417481290a40949514102a8095205b0610a035b0a4a4d55c95b60000000000000000000000000000006fe7f6fff307807df3be7cfef7cf86c6790003000f7bffb574000000000000000000000000001f80000003bdbdb9ddec4500007fc8003fef4c00000be80bdfea800000000000000003bfe400007f335ae401df00007f407be8a3ec0003f006ae800003f00dfa400000000001b5800036a480000000000000000eff400003fcffe8000003f8fff810000000000003ffe01ff707d0ff00000f0fc00000000000000c02f8000187fe7800038fc000000001f03800108f873c0018600017198f000e180000000000000437c039e003d8000001e7f6d199f86e3801dfc3e7f3d9b98030bb3ec28700710164ea0116e014007400041716000c0984a013701c00114350030000f0ccb00132000000049600c0040200b085b020005121005b140d2000500081f10018a0802a0000c0000000808040000000000000000001c6b7b1ed100b226f1e46d015021a838434a002c40000522037f6bea2eb0d03a0000000000000001ed515f281c8001ad1c0a030300288002000000000000000000000b78dfb590740000000000007cf3af6127a40c80503404 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0xfffffffecfffffffccfffff3aeafff6a9fe0ffffff88cffffffffffdaffffc4ff3feafffffffe0ff1ffffff13ffedfffffffccfffff3aff8bffe9fffff1ffffffffffedffffdafccfc4ff3affffffe9fe0fffff06dcffffecfffffffcdfffff3afffff77fffffffffffffffffffffffdbfff284ff3aeafff77ffcdff1ffffffffffffffffff47ffffff3fffff27692bf73fff0fffffffecffffdbfcd2bfff3afffff77ffff73fffffffffffecfe073ffcdfffff3aff6ff6bfffffffffffffffffffffffff4fffffffffeaff2fe928d33fff0fff13fffffff77fffffff0f3aeaff2ffffff33ffffffffffffffe277ffff284ff3feafffffffcd331fffffffffffffff77f4cdfff0f3aeaffffe92bfff1ff0fff13ffedfe2ffffccfffff3afffffffffc6fffffffffffffeeafffd944e2c6073ffffff77fffffffff0fffffffeefe375a4cd2c60b3ffffffffffffff1ffffffffffffffffffffffffff38ff8b26994bfff1ff088cfffffffff7ffffffff0738fffff6bfffffffff0fffffffecabffff48cfffff38fffff6bffe0fffffffffffffffffffd9ffffffff38ff8b24ff4bfff1fff8bfffffffffffff4fffff07ffffffffce2a0ff1ff08bf07ffffffffdaffffc7ff38ffffffcefffff1fff88cffffffabffdafff2bf073fffffffcefffff1ffffff070fffffffff4cefffff38ffffffff2a0fffffffffffffffffffff4cefff0738ffffffff2a0fffff0fc213ffedfffffffcefffff38c7ffffffffffffffffff13ffeda7fffffcefff0b38c7fffffffffff1ffffc207ffedfffffffce287ff38fffffffffffffffff6fffffffffe3fffffffc4ff3fdffffffffcdff1ff0fff070feefffffffcdfffff3fdffff759ffffffffffdcffffeeaffffffcdfff073ffffff759ffffffff0ffffffffffffffffff2ffffffdfff2fce4bf731ff0ffffffffffffffffcefc4ff32dfffffff491ff1ffffff13fffffffffffff2ffff3fdffff77f4bf731fffffffffffffffffffce2c4ffffdfffffff491731ffffff130fffafffffffffff0f3fdffff74effffffffffffffffffafffdb4bffc4ff3fdffffffffcdff1ffffffffffeca7ffff47ffffff32fffff77f2bffffff00dcffffeefffffffcefffff3ffffff77ffc6fffffffffffffeeffffff48efff0f3ffffff77ffc673fffffff07ffeeffffd9fcefc6ff3fdffff77ffffff1ffffffff0feeae37ff44dfff0b3ffffff6bffffffffff6ccfffffffffffffff2ff07ffffff2fff491ff1fffffffffffffe3ffffcc2c7ff3fff6fffd9491ff1fff6ff07fffffe3fffffffc7ff3fffff26bffcdffffff6fffffffffe37ff4bffff073fffff2ffffcdfffff0fc207ffeefff7fffcdfffff3ffffff6bffffffffffffffffffffe37dbfcc2c7ffffffffffff491ff1ffffffffffeeae37db4ff2c70f3fffff2ffffff331ffffffff0fffaa27ff4cdfff0ff2ffffffff2bffffffffffff0feeae377f4ccfff0f3ffffffffffc6fffffffc2ffffeefe37dafcd2c7ff3ffffffffffffff1ffffffffffecfff7dbffffffff32ffff24ce4bfffffffffffffffffff7dbfff2ff0ffffffff4ff4bf331ffffffffffecfe27fffcefffff32ffffffff491ffffffffffffffffff71bfff2ffff3fc7ff24ff4bfff1ffffffffffffaa2fff4fffff0ff2ffffffff28dfffff00ccffffffafffdaffffffff3fc7ff2fcefffff1ffffffff0fffaff77fffffff0f3fc7fffffffff33ffff0fffffffffe3fdaffffc7ff3fffffffcefcdff1fff0ffff0ffffe0fff4fffffff32ffff2fff2bfff1ffffc2ffffeefe377ffcefffff3fc7ff2ffffc6fffffffffb28ffffe2fffffffc5feffeafdeffffcdffffff0dcfe8c7ffffffffcdffffefffffdeb69fffffffffffffe8c7ffffffffcdfff0effffffffe9fff73ffffffffe8cbffffffffccfff0affff6ffffffc6fd8ffffc2fe8cbffffffffcdfc6feffeaffffffffffd8fffffffe8cbffffffffcdfc60affff6fffffffffd8fffffffe8c7ffff71b44dfc60efffffffb69ffffffffffffb3fffffffffffff23ffefbaaffffff49133ffffffffe8cbffffffffccffffeffeafffb7f4bffc5fffffffffffffffffffcc205fefbaafffb7f491ffffffffffe8ffffff7bffff2bf0effeafffb7ffff305fff0fffffffffff798fffffffeffeafffb69fcdffffffffffffffffff7bf4bffc50effeafffb7ffff33ffffffffe8cbfffffdb48cfff0effffffffffffffc5ffffc2fffcbffff798fcdffffeffeafffb69fffffffffffffffc7fa3f71844d2060afffffffb7ffffffffffffffc0cbfa6179944e23ffefffffffb7ffffffffff8bfffffffffffd8fffffffeffdffe1b4efe0fffb3f89cfffc3ffffffffceffffefffffe1fffffffc5fffffffc0c7ffffffffcefc5feffdffe1ffffe0fffffffdcfffc7ffffffffcefc502ffdffffffffe0ffffff88cffffffffffffffffc702fffffe1fffffffd8b3fffffffc3ffffffffccffffeffc7fe1b59fe0fd8fffffffffc3ffffffffccfc7fefffffe1ffffe0fd8ffffc2fc0fffabfffffff23ffefbbffe1fff4bffffffffffb3ffffabfffffff23f0afbbf8bfb7f4a0ffffff8bffc0ffffff7d8fffffffefffffe1b4efffffffff88cfffffffff7d8ffffff02fffffffb7ffffffffffffffffc3ffff719fceffffeffff8a1b7fffffc5fffffffc0c7ffff7ff48efc7fefffffffffffe0ffffffffffffc7fa22ffffcd2060efbbffdeffffff73fffffffffffffa3ffdbfffffffefb9ffdefceffffc5ffffffffffffa22fffffffc5fefb9fffffcefcdffffffffffffc3ffffffffffffffefb9ffdefff286fc8ffffffffffffffffff47ffc6feffdffdeb7f2bf708b3fffffffc3ffe2ffffce2bffefffffdeffffff705fffffffc0c7fa60ffffceffffeffdffdeb7ffffffffff6ffffffffffffffffffff02fffffffb7f28dfd8b3f6ccffffffa21ffffffffffefb87ffffffffffd8fff6fffc0ffffe1fffffffc7fefbbfffffd9fcdfd8fff6fffffffffe1ffffff28702fbbffffffffcdfffb3fffffc0fffabffff47fffffefbbffffb592bfffffff6fffffffffff7ff44dfff02fbbffffb592bffd8fffffffffcbfa21ffffccffffefffffffb59fc6fd8fffffffc0cbfabfffffcd2bffeffffffffd9ffffd8ffffffffffffaa2ffffcc23f0ffbbfffffff491ffffffffffffffffff7db44dfc70ffffffffb7f2bffc8fff0ffffffffaa1ffffff23ffffbbfffffce491fffffffffffffffaa2ffffff23f0ffbbfffffff49133ffff0fffffffffe1fd9fffffffefffffffb7f491fc8fffffffffcbffffffffcefc70effffffffff491fc8ffffc2ffffffaa1ffffce23ffffbbfffffff491ffffffffffffcbffffffffffffffeffc7fffb4e2bf308b3ffffffffffffffdbffffc7fefffffffb4e28d308b3ffffffffffa3f79bfff2bffefb87ffffcefff33ffff0ffffffffaa17d84bfffffefffffffb4efcdffffffffffffcbfa7f7bffceffffeffc7fffb7f286fc8fffffffc0cbfffffd947fffffefffffffb7f2bffc8ffffffffffedfe075a4cd2060bfaeafffffffffffffffffffffcadfe17bf4ff20504ffeafffffffcdffffe889cffffffffffff48ffff07ffffffffe9fe0fd8fe889cfffffffffffffff23f07fafffff7694bfffffff8bfffffecffffd8fffffffcfaeafff77ffffffffe88bf07ffffffffd848fffffffffffff769fe0ffffff8bfffffffffffd848ffff07fffffff77ffe0ffffe8fffffffffffffffffffc4ffffea8a1fff4a0fd8fe8fff128fffffffffffffff0bffea8a16bffffffffffffffffcfffff73f4bffc40bffff8bfffffe0fd8fe8ffffe8cfffff75a4cffc50bffff8bfffffe0ffffffffffffffffff718fff23ffffaea8bf4e94bfffffe888c07ffedffffffffffc5fcfaeafe1ffffffffffff8bffffc6dfff77fffffff04faeafe1ffffe0ffffe8882ffffffffffdafcf2bffffffffe1fe9fe0fc5fffffffe8cffffffdaffffff0bffff8bffe9ffffc5fff882fffffffff75afcffc5ffffeaffffe9fe0ffffff6ffffffffffffff47ffff07fafffde77f2bfffffe8fdc07fffffffffffcf286fffafffdefe9ffffd8fff6fffffcfffe0ffffff2bf07fafffdefffffffd8fe8ffffffceffe2fdb44f23f0ffaffffffe9fff73ffffffffffffffffffffff23ffcfafffdefe94bf73ffe8fffffffffffffdbfcffc4ffffeafdefe9491fc8fffffffffffffe2ffffcf23f0ffaffffffff49173ffffffffffc6cfe2fff4bffc5fcffeafdeffffcdffffe8ffffffcffffffdb47ffff0ffffffff77f2bffc8fe80ffffffeffe0fd8fcfffffffafffff769ffffffffffff13fffffffffffffffffffaea6ff6a9491fd8fffffffffffffe1fffffffc4ffffea6fffff491fd8ffffff068ffffff7bf47ffffffffeafff6bf2bffd8fffffffffffffff7bf47ffff07ffeafff6bf2bffd8fe8fc2fffffffff7bf48fffffffaeafff6a9fc6fffffffffffffeffe1fff48ffff0bfaff6ffffffc6fffffffc2ffffeffff7bffcf286fffafffff6a9ffffffffffffffffeffe271bfcf205fffaffffffff491ffffffffffe8cfffff75b4cffc60fffffffffff2bffc8fff0c2ffffeffe075afcf206fffaffffffe9fffffffffffffffcbfffffffffffc4fcffeafff4ff4bffc8fe8fffffffecfff7bffff23ffcfafffff4ff4bf33ffffffffffffffff79bfcffc4ffffeafff4ff4bffc8ffffff13ffeffff79bfcfffffffaeafff4e94bffc5ffffff128fffffffff4ffffffcfaeaffffff28dffffffffffffcbfffffff4fffc4ffffeaffffff28dfc8fe80fffffcbfffffdafffffffcfaeaffffe9ffffc5ffffff128cadfff7bffff2bf0cffeafffffffff33ffff0ff07ffedfe1fffffffc5fcfaeafffffffcdffffff0fffe8fffffffff4fffffffffeaffffe9286fc8fffffffe8fffffffff4cffff0ffaeaffffff286fc8fff0fffe8fffffffda4fffc6fffaeaffffe92bffc8fff0fffffffffe1fdafcf2bffffaffffffe9fc6fc5ffffffffffffa3f75a4cc2050bffff8bfffffe0fffffffdcfffc6eae3fd844d2c603fffffffffffffffffffffffffc2eae373f44d2ff0bffff6ff6bffffffffffffffffc6eae3fda4ff2c500fffffffffffcdffffffffffffc2eae377f4cc2ff0bffc7fffffffc6fff13ffc2fffc6eae375a4cd2c6ffffffffffffffffffffffc2fffcbfae379a4ce2ffffffc7ffffffffffc5fff8bffffc3fffffffffffc4fcf8dffffffffe0fd8fff8bfffffffa3ffffffffc4ffffdfffffd92a0fd8fff89cfffffffffffffcffff03f8fffff759fe0fff13f89cffffffa3fffffcf28407fffffffffffe0fd8ffffff07ffffa7fffffff23ffff8dffff77f4a0fffffffffffffffa7fffffff23f07f8dffff77f4a0ffffff8bfffffeca3ffd8fffffffcf8dffff77ffffffffff8bffffffffffffffffffffff8dffe177f2bffc813f8bfffffffffffd9ffffc4ffffdfffffff2a0fc8fffffffc0fffffffd948fffffff8fffe177ffe0fc5fff8bfffffefffffd9fff2bf03fffffff77fffffc513ffff07ffefa7ffff48ffc5fffffffff77ffe0ffffff88cfffffffffffffffffffcf8fffe16bf2bffd8fff88cfffc2cfff7fffff2bf04fffffe16bffffffffff8bffffcffabf7fffcffff07f8fffe16992a0fd8ffffffffffefa3f73fffffff0bf8c78bf6bfffffff13fffffffcefabf7fffff23f0bf8fffff4ff4bfffffff88cfffc6dabf7dafff23f00f8fffffffffffffffffffffffcfffff7da4cffc703ffffffffff2a0fc8ffffc2fffcefabf7ff4cf207fff8fffe1ffffffffffff8bf07fffffff7d9fffffffffffffe14ff4bffc8fff8bffffcfffff7d9ffffff07fffffff4ff4bffc8ffffc2ffffefabf7fffff23ffff8fffff4ff4bfffffff8bffffc3fffffda4fffc7fcfffffe1fff2a0fc8fff8bffc0c6dabffdafffffffcf8ffffffcefffffffffffffc0fffa7ffff4ffffffff8c7fe1fff2a0ffffff8bffffffffff77f4cffff03f8c7ffffff2a0fc813fffffc0cffffffff4cffc7ffffffffffff2a0fc8ffffc2fffcffa7f77ffcf2bfffffc7fe1fffffffc5fff6dcfffcffae3ffffcf2c603fffffdefffffffd8fff6dcfffc3ffe3ffffffffffcffdffdefffffffd813f6fffffc3ffe3fffffffc4fcffdffffffffcdfd8fff6ffffffefa20fff47fffffff2dffff7592bfffffffffffc0fffafffff48ffffffffdffde759fc6ffffff6dcfffffffe3ffffcffff03fffffffffffc6fff13fffffc0cffaffffffcffc6ffffdfffffd9ffffd8fffffffffcffae3ffffcf2c50fffffffffff49173ffffffffffcefa22fdb47ffc6fffffffff77f2bffc8fffffffc0cefae3fd844ffc6ffffdffff77ffffffffffffffffc7faffffffff2fffcffdffff77f49173ffffffffffcffa62fffffffc4fff2dfffffff491ffffff0dcfffffffffffffff2ffffffdffdefff491fc5fffffffffcfffffffffff2ff0fffdffff77f491705fff0dcfffffffe3ffffff2c5ffffdffde77f491ffffffffffffc2eafffdbfffffffcffdffff74effffc5ffffffffffefa62ffffffffffff2dffde77f286fff13f0fffffcfffe3fd948fffffffffffde77ffc6ffffffffffffcffaffffffcf2c70bffffffffff491fd8ffffffffffefaa07ff44ffff03f2fffff6bf2bfffffffffffc0cefaff7ff44f2c7ffffffffffd9ffffd8ffffcc07fcbffffffffff2fffcfffffff6bf4bffd8ffffccfffcbffffffffff2ff04fffffff6bf4bffd8fff6ff07ffffaa1ffffcfffffff2ffffffd9491ffffff6ffffffffaa1ffffcffff07f2ffffffff491fffffffc2fffffffffffffcf2ffffffc7ffffd9491fd8fffffffffcffaffffffff2ff0bffc76ff6bf491fd8ffffc2fffcfffffffffcf2c7ffffffffffff491fd8fff6ffffffecfe1ffffffffffcf2fffff6bf2bfffffff6fffc0cbfaffffffffffffcffc7fff6bfffffd8fff6fffffcaefff7bfffffff00ffc7fff6bffcdfd8fff6ff07fcaefe3fff4bffc7fcfffffffffffcdfd8fffffffc0fefabf7ff47fffffff2fffff6bf2bfffffffffffc0fffaff7bf48ffffffffc7fff699fc6ffffffffffffc6eaff7dbfff2ff0cfffffff4ff4bf33ffffffffffcffaff71bfff2ff0ffffffff4ff4bffc5ffffc2ffffeffe37d8fcf2c7ffffffffffff491ffffffffffffc2daa2fdb4fffc7ffffffffffff28dfc8fffffffffc2eaff75bfff2ff0cffc7fffffffff305fff0fffc0c6eae3fda4fffc7fcfffffffffffcdfffffffffffffefa2277f4cffff0ff2ffffffff286ffffffffffc0cefaa0fda4fffc7ffffffffffff2bffc8fffffffffcacabffdbfffffffcfffffff4ff4bffc8fff0ffffffeeffffd8fff2fffcfffffff4ce491ffffff0fffffffffff799fffffffff2c7fff4ff4bffc8ffffffffffefa7f7bfffffff0ff2c7fff4ff4bfffffff0ffffffeffe1fd9ffffc7fff2fffff4ff4bffc8ffffc2fffffffff799fff2ffffffc7fff4ff4bffc5ffffffffffeda3ffff4ffffffcf2c7ffffff28dfc8fff0fffc0cbfafffdafffffffcffc7ffffceffffc5fffffffc0fffa61fff4ffffffff2c7ffffff286ffffff >>> (168*i)) &&& 0xffffffffffffffffffffffffffffffffffffffffff

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
private theorem boardOK (w : Fin 28) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
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
  | ⟨a+28,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 28) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 28) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 28) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 28) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 28) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 28) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 28) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 28) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 28) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 28) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 28) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 28) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 28) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 28) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 28) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 28) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 28) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 28) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 28) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 28) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 28) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 28) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 28) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 28) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 28) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 28) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 28) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 28) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 28) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 28) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 28) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 28) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 28) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 28) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 28) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
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
  obtain ⟨w,hw,on⟩ := member (List.range 28) full
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
end PEqualNP.Research.PlaneCase35SecondFamily
open PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35SecondFamily in
theorem PEqualNP.Research.PlaneCase35SecondFamily : ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
    pos p.val &&& (neg (f i).val ||| neg (f j).val) = pos p.val := by
  exact ⟨idx,fun i j h => retained i j h⟩
