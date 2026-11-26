import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35FifthGuard
open PlaneFirstAndSeparation PlaneFirstAndBudget PlaneCase35FourthOrBudget
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def omittedFlags : Nat := 66559
private def indices (i : Nat) : Nat :=
  (0x1cfe773795c9e371787c2e06f777b9dc6df6db4d9ecb61afd76b759abd469f4ba4d1e8b3f9ecee733599cc65f2992c8637198bc56230f85c1e02ff7dbe5eef377bb5cee570b7dbad96bb55a2cf64b1582bf5eaed72b758abd5aab54a9d46a14fa6d2a9348a3d1685409fcfa773a9bcda673297caa532692c9245208fc7637198c45a29128843a1b0a8441a090280be5eef579bc9e2f077bb9d8ea74ba1cae270b81bedd6e369b2d66ab4da0cf66b3192c86331588c3602f976b95a2c95ead5529d4ca4512853e9e4e26530974b255289247a391a8c452190883411fcfa7b3c1d8e670379b8da6b33994c45e2d968b2582b14c9c4b251248c45221047e3e1d8dc6a33188c0562a148a04a231087838190c05428130883c1a0b048200e04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0xb800238b280428b220448b200468b108250b100270b0c0418b080438b060608b040618b020648b0086503002470ee0008aec8001aac40098ec0009aea8002a6a100a2ea000aa6980032e910222e908212e900232e88003aa840298e818282e8102a2e808292a8042a8e62004ae6000ca6580812652084265080526500852a4c0818e4a080ae48081aa440898e42084a64080d224028d0e2a040a6290422e28042ae22044a621848262104a262084c222024e061908226180832e130a02e128242e120a42e110a22e1082522102870a0e0c08a0c0c1860b0c02e0a0c0a6090c222082c30a070e00a060e08a058680a050e80a0486902042c90e038602e030e02e028642a024a48e0186822012ca0200a4d020068e09c801189c4001c9c2010c9c0011c9940214991022499002349880138986020c984021c9830304982030c981032418021345700045d64000dd60004d55400155500055d4c0019d480119d44001d942014c140215453100255300065d2c04095290421d2804295250405d24040d922044c52104251202464d150205d140215d110225d1082511102074d0c04195098501509052150885111082530906060cd050605d0486111022544d0187011012524100a5508e4008cce2000e4e10086ce0008ecca010acc8011a8c4009c4c30106cc2010e4c101860c021944b810224b210064b100264b01026caa100aca8102a8a6100c8a4108cca2100e4a100a60a030a44989012498103289612048941214c930206c921206c910226c9092120903034c8a110a48891120883130886120c0843094c8303068825308c81838208121a4080b19008071a0471000747000474650085c64008dc62004e4610087c6040c945c0811459080345880134580813455080545408154520846451080745080530502854c4c0819449810344909034488113c484909445088504428944430906042294444181830412984040a1d004069c0439002343890034381023431002743090430303064c2c1409429840342904234289403c285029826140c425048502434840223444421848302124a4020b4c002070e041c901141c18114190823418901301838308161a04c150a05c1492110143814c130a060123844c114a21c10d241010786080e1c0840c941100c3c1040b0d0240a950200a3d0040985030092d20008b51000879208070e040063c04c0586810052c84004b490c0387020032d04002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x8000200800000840000024000001200000010000000800000040000002000000100000008000000400000020000001000000080000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x8cf0077c000007c07df01df00000781d0000003f0b800000000000003ac0052279f3e86387cb000d1010f1d19e2b01081bd03e002480d00220004600000800000001bfeefdb7f7f1c07400000000000007ddf9b3d8a3339ce28f9c106080d008000000000000000000000000ff3faf79a00000000001eff6fc47df48f31908204fffffffffffffffffffe000000000000000000000000000000000000000000007ffc0000000000000000ffffffffffffe00000000000000000000000000000002001ffff0000000000007ffe000000000ffffffffffc000000000000000000000000f0007ffc000000003c00ffc0000007ff00000001fffffff8000000000000070047003001fe0000000000701ff80003c07ff00000fe000003ffff8000000000600078078000ff000000e0260c03e000003c07fc0060ffc001f8003fff0000010c0922023870607e00040800c1c00f800c118301c000781f00e3e01f007fe0000582008012000030fc0123055098c438410030601806230860010e0c78380f8020a000024492071661e04160040200121262542c4b0080400c0004802313863c000012180004ca42accc04280094a8c4c42881050165249195923130894132d98204008a0810509005550000000002515000002048280104a0a494152212545aa00000000000000000000000000000000000dfbebfa60000000373b3ddafb349900000000dfa01dbfeaaa0000000000000000000000001bed7d40000377b6ae9539fc0000000ff00fffee0000003fc1ffe00000000000000000007bf8000ffbfc233c01df000001f01f7c077c00001e074000000fc2e00000000000000eb00148800000000000000000002c4f02c0003c786f00000e7e000079f8000000007f07f0005b07d0161e0001e1e0000000000002c980b0004f3600033c00378000001c39e1c0001b87131b000330002a3414601200000000002502c0261804c00b0000675421f6500032e2860028386006c6528200168d0a4140000000b4a0a50280a0051eb7179176c010d10c0b6d11f4005cc8831001a368402d392100000d98182080f3e7d0c70f96001a2021e3a33c56021037a07c004901a00440008c0000100000000000000000000000007effe7c7fa0d5e7dcf9f4727e0f41e8283d01b8003480001bfeefdb7f7f1c07400000000000007ddf9b3d8a3339ce28f9c106080d008000000000000000000000000ff3faf79a00000000001eff6fc47df48f31908204 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0xfffb3ffffffffdc6ffffffffbaaff2b7ffffff1ffffffb30ffffffffffffffffffbbf8bfb59fe0ff1ffffffb3fffffffffffd6fffffffff8b2b7f4a0ff1ffffffb30fffffffff67f4bffffbbffffb7ffe0ff1ffffffb30fffffffffffffffff3b9ffffb7f2bf731ffffffb3ffffffffffffffff2b3b9ffffffffff731ffffffb30fffabffffffffffff3bbf6fffd957fff1ffffffb3fffffff83ffd5ffffffbbf6f2fd9fffff1ffffffb30ffffffffffffffffffbbfff2b56551ff1ffffffb30fffffffff6ff47ffffffffffb5657fff1ffffffb3fffffff8bffd6fffff3bbfff2fff491ff1ffffffb3ffffffffdf6d647fffffffff2b7f2bfff1ffffffb3ffffabf81f6564bf2bfffffffb7ffffff1ffffffffffffffffff6bffccffffff97ffe9920ff1ffffffffffffffffdcfff47ffffaeaff26bf93fff1ff0fff530ffffffffffffffffffaea972fff93fff1fffffffffffffff83f694fcdffffff972fe993fff1fffffffffffffffffffff48cff3aeafff6bffe0ff1fff88cffffffffffff6bffffffffeaff2fe9fe0ff1fffffffffffffe4fff6bffccffffff8b2fe9fe0ff1fff6dcfffffffe483fffffffff3aeafffffffffff1ffffffffffffffffff6ffffffffaeafff769fcd731ffffffffffffffffff6fffffff3aeafff7692bfff1ffffffffffffffffff6fffcd2b3feafff769fff731fffffffffffffe481cffffffff3fea6f26bffffff1ffffff530ffffe5ffffffffffffaeaff2fe957fff1ffffffffffffffffff6ffffffffaeaff2fe928d331fffffffffffffff89d6fffff2bffeaff2fe9fcd331fffffffffffffe5fdd6d4fcdff3fffffffe92bfff1ffffffffffedfe589d6d5fcc2b3fffffffe9fffff1ffffffffffffffffdc67fffffff8e697f4fffffff1ffffffffffffa7ffff6bf4ffffffe6972fff920ff1ff0fdcffffffafffffffffcdffffe6ffffd993fff1ff095cfffffffff8ff67ffffff3ffffff77ffd1ff1fff97fffffffffffff67f47ffff2ffff277f93fff1ff097fffffffffffff67f47f2ffffffff77f93fff1ffffff530fffffffffffffffffffe6ff269993fff1fffffffffffffff8ffffffccffffe6ff2fd9911ff1ffffffffffffafffdcfd447fffffe6ffffd993fff1ff0fff530fffafffff6bffffffffe6ffffd693fff1fffffffffffffff8dc67ffffffffe69724fffffff1fff97fffffffa7f81d6bfffffff2e6ff2ffffffff1fff97fffffffaff8dd6964ff2fffffff2fff93fff1fffffffffffffe6ffffd4fccff38ffffffd94a0ff1ffffccffffffffffdfffffff2bf8fffff6bffe0ff1ff0fffffffecabfffffff48cff3fffffffd9fe0ff1ff0fffffffecfe6fdf67ffffffffff8b24fffffff1fff8bfffffffabffff6bfffffff8ffffffce2a0ff1ff08bfffffffabffff6bffff2bf8ffffffcefffff1fff8bffffffffe6fff6bf4ceff3fffffffff2a0ff1fff8bfffffedaa6fff6bf4ce2b38fffffffffffff1fff6ffffffffaffffffff4bfff3fdffff77ffcdff1ff0fffffffffae4fffffffcdff3fdfffffd9fffff1ff0fffffffffafffff6fffffffffdffff74e4bfff1ff0fffffffffffffff6fffffff32dffff77f491731fffffffffffffe5fff6fffce2fffffff277f4bf731ffffffffffffafffff6ff4bfffffdffff74efffff1ff0fffffffeca65fff6ff47ffffffffff77f2bfff1ff0fffffffeeae4fff67f48e2f3ffffff77ffffff1ffffff530fffffffffffffffff3fff6fffd9551ff1ffffff53ffeefe6ffffff47fff3ffffff6bf57fff1fff6ccfffffffff8dfffffffffffffff2fff491ff1fffffffffffffe68fffd4fccffffffff2fd9491ff1fffffffffffffff8dffff4bfffffffff26bffcdff1ff06ffffffeeae68dffd548d2fffffff2fd9fffff1ffffff53ffffffffffffffffffffffff24d6551331ffffff53ffeeffffff6fffccffffffff2fd6551ff1ffffff530ffffffffffffffffff2ffff2fd654d331ffffff53fffffffffffff4ff2fffffff2fff54d331ffffff53ffedabffff6fffcdff32ffffffd6fffff1ffffff53ffeeae6fff6bf4cd2fffffffffd657fff1ffffffffffffffffdf6ffffffff2ffff24cefff331ff0fffffffffffffdf6d4fff2ffffffff4cefff331ffffffffffecfff89f6fffcefff2ffff24fffffff1ffffffffffeefe58dc6d6fce2fffffff24fffffff1ffffffffffffabf8bf6d44fffff2ffffffcefffff1ff0fffffffffaff8df6954ff2fffffff2fcefffff1ffffffffffedaa681f6964ceffffffff2fff2bfff1ffffffffffeeae48dd6964ce2f3ffffffffffffff1ffffffb28ffffffffffffffffffbaa97fb7f93ffd8ffffffb28fffffffdcfffffffefbaa957b7fffffffffffffb3fffffffffffd7fccfffbbf97ffe9911fffffffffb3ffffffffff61747fffffff97fb6993ffffffffffb28ffffe5ffffffffffeffeafdefe957f73fffffffb28ffffffffffd5fffffffeafdeb69fcdfffffffffb3fffffffffffd5fcdfeffeafdefe9fff73fffffffb28ffffe4ffffffffffefbaa6ffb7fffffd8ffffffb28ffffffffffffffffeffeafd7b69551fffffffffb3fffffe5fdcfff47fffffeafd7b7f57ffffffffffb3fffffffffffd7fffffffeafffb694bf33fffffffb3fffffe5ffffd7fccfefbbfffffe9491fffffffffb3ffffffffde6d74bfffffeafffb69fcd33fffffffb3fcbffe4fde61748dfffffffffb69ffffffffffdcfffffffffffffd6ffffefffffe1fff920fffb3fffffffffffffffffffffffefba6961b56920fffb3ffffffffffffffdcfd6fffffffe6961b7f920fffb3f95cffffffa3ffffffffcdfefba6ffffd6ffffffb3f97ffffffffff83ffd6ffffffba6fdefff93ffffb3fffffffffffffffffffffffefba6957b7fffffd8b3ffffffffffa3fffffd7ffffffba697fb7f93ffd8b3ffffffffffa3f81c63ffffffffe6fd7b56ffffffb3ffffb3ffffa7f87ffd7ffffffba697fb7f911fffffffffb3ffffa7f85e65747fffffe6fffb7f93fffffff8bfffffffa3fffffd5ffffefb9ffe1fceffffffb3f8bffffffffe4ffffd6fcefeffdffe1b7ffe0fffb3fffffffffffffffffffffffefbbf8a1fd9560fd8b3ffccffffffffffffffffff2bfbbffe1b7ffe0fd8b3fffffffc3ffffffffd5fccfefbbf8a1fd9fe0fd8b3f88cfffffffffffffffffffffbbffe1b56560fffb3fffffffffffe6fff63ffccfeffff8bffd6fe0fffb3ffffb3fc7ffe6ffffd6ffffefffffe1fff4a0fffffffffffffffffffdf615ffffffffffe1b4efe0fffb3ffffb3fc7ffe6fdf65648efffffffe1b7fffffffffffffffffffa3fffffffffffffb9ffffb5654d73fb3ffffffffffa25fffffffcdfeffdfffffd657ffffb3ffffffffffa3f8bffd5ffffffb9ffdefceffffffb3fffffffc3ffe5ffffd6ffffefb9ffdefff2bffffb3ffffb3fc7fa6483ffd6fce2bfbbffdeffffffffffffffffffc3ffe683ffffffffeffff6d7fffffffd8b3f6ccfffffffffffffffffffefffffffb7f28dfd8b3f6fffffffffff87fffffff2afbbffffffffcdfd8b3fffffffcbffe6ffffd7fcdfeffffffffd92bffd8b3ffffb3fcbfaa687ffd7fcd2affffffffffffffd8ffffffb3fc7fabf8bfffffccfffbbffd7fd6fd1ffffffffffffffffff89ffffffffffbbffd7b7ffcd33fb3fffffffc3faa689f6ff44dfffbbffd7b7fffffffb3ffffb3fcbfaa687ffd7fcefeffffffffff491fffffffffffffffabffff6d7ffffffbbffffb4e2bffffb3ffffb3ffffabf85f617fff2bfbbffffb4effffffffffffb3fcbffe6fdf65744efffffffffb7f2bffffffffff528fedffffffffffccfe7affffffff920ffffffffffffc6cffffffffffccfe7ffffe14e9fe0fffffffccfffc7fffffddffffffffffeafe1fff920ffffe8ffffffc7ffffffffd44ccffffffffffe9920ffffe8ffffffcbfffffffffffccfe7fffffffe9fd1fd8fe8ffffffcacfffffffff47ffe7feafff6bfffffd8fe8fff53fc6dfff83ffffffffe7aeafd7ffffffffffff94cfffffffff87ffffffffffaeafff4fffd1ffffe8fffffffecfff87f63ffccfe7aff97fffffd1ffffff97ffffffffff87ffff4fffffaffffffe990dffffe8ffffffcadfff85e6974cdfe7aeaffffe9ffffffffffdcfffcfffffffffffffffffffffe1fe9fe0fd8fe889cffffffffffff614fcfffffffffffe94a0ffffff8bffffffffe4fff63fffffcffeafff77ffe0ffffe8fdcffffffffffff63f48ffffffffff769fe0ffffffffffffcffffffffffffffffffeafe1fff4a0fd8fe8ffffffcffffffdcfff4bffffffffe1fe9fe0fd8fe8fff53ffeffffffffffffffffaea8bf4e9560fffffffff53ffeffe7ffffff4fffffaea8bffe9560ffffffffffffffffe7fdc614fcffffffffe14e9fe0fffffffccfffc7ffe4fddfffffffcffeafe1ffffe0ffffffffffffcfffe7fdd6954cffffffffe1fe9fe0ffffff6fffffcfffffffffff47fffffeafdefff2bffd8fe8ffffffcfffff83fffffff2bfafffdefffffffd8fe8fff53ffeffffffffffffffffafffff769fd173fffffff528fefffffff6ff47ffffafffff77f57fffffffffffffc7ffff8bffd4ffffcfafffdefff491ffffffffffffffffff8bffd4fcffffffffdefe9fd173ffffffffffc6cfff8bffff4bffffafffde77ffcdffffe8ffffffcfffe7fff6d447fffffeafff77f2bfffffe8ffffffceffe783f61548f2bffeafff769fffffffffffffffcfffe787ffffffffffaea6ff6bffd1fd8fe8ffffffcfffe7fdefff47fffffeafff6bf2bffd8fe8ffffe8ceffe785efff4bf2bfafffff6bfffffd8ffffff53ffeffff89cfffffffffafffd74e9fd1fffffffff53fceffe781dfff4fffffaeafd7fffffffffffffffffffecfe589efffffffffaeafff4fffd133fffffffffffeffe789e6d7fcffffaffffffe9491ffffffffffffcbffe58bffff4ffffffeaffffe928dffffe8ffffffcadfe485efff4ff28fafffffffffcdffffffffffffcfffe7fde6974cfffffeaffffe92bfffffffffffffceffe785e6974cf2bffeaffffe9ffffffffffffffffffa3ffff614ffffff8e6fff74e920fffffffdcfffc6cffffffffffcefe78fffffffffe0fffffffccffffedfffffffffffffe78e6fe1ffffe0fff53ffffffffeda3ffffffffccfe78ffffffd6920fff53fffffffc6ca7ffdcffffcefe7ffffe14fffe0fffffffffffffffa3ffdd694fffffffe6fe1fcefe0ffffffffffffc2da7ffddfd64cefe7ffffe1fff920fffffffdcffffffffffffffffcdfe7fe6ffffd9ffffd853fffffffc3ffff8fffffffffe7ffffde77f90dfd8fffffffffc3ffffffffd4ffffe72e6fdefd993ffd8fffffffffc3ffffffffd4fcd2e7fe6fdefd9ffffd8fff97fffffeefffffffffffffe7fe6fde77ffcdfff53ffffffffeeffffff63ffcdfe7fe6fff756ffffff53ffdcfffc7ffff8ffffffcefe7ffffdeffffd1ffffff97ffffc7ffff8ff614ffffffffffdefcefcdffffffffffffc2ca7f83f67fffffe72e6fdeffffffffffffffffffc6eaff8ff65644e2e7fe6fff77ffffffffffffffffc2effffdcffffffffffe6fd7fd993ffd853fffffffcbfa3fffffffffffe72e6fff6bf90dfd8ffffccfffcbfffffdeffffff2e7fe6fff6bffcdfd8fffffffffcaca3ffdeffffcdfe72ffffffd9ffffd8fffffffffcaeafffdefd7fcc2e7fffffffd9ffffd8fff97ffffc6efff8ddfffffffe7fe6fd7ffffcdfff53ffff53fc6eaff8dd6bffcdfe7fffffffd6fffffffff97fffffffaff8de63ffffffffe6fff4cefd1ffffffffffffcaeaff8de67ffcefe7ffffff4fffd1ffffff97fffffffa3f87f6bf4fffff2ffffffce90dfffffffffffffffaff8de6974ff2fffffffffce90dffffffffffffcada7f85e6bffcefe72e6fffffffffffffffffffffcaeaff8de6974ce2fffe6fffffffffffffffffffffc3ffffffffffffffcf8dffe1fd9fe0fd8fffffffffcffa3fffffffffffff8dffe1fd92a0fd8ffffdcfffcffa3ffffffffcf2bffdffe1fd9fe0fd8ffffffffffeca24fff63fffffff8dffff74efe0ffffff89cffffffa67fff67ffcffff8dffff77f2a0fffffffdcffffefa67fff67f48f2bf8fffff77ffe0fffffffffffffeffffffffffffffff8ff8bffd9560fd853fffffffc3ffffffffd4ffffcf8fffe16bf2a0fd8fffffffffc2cffffdfffffff28fffffe16bffe0fd8fffffffffcffabffdffd4fcffffffffe16bf2bffd8fffffffffcefa3ffdcfd5fcf2bfffffe16bfffffd8ffffff53ffefabffff63fffffff8fffff4d6fe0ffffff8bffffc6dfe6ffffffffffcf8ffffffff57ffff53ffff53ffefaa7fff6bf4cffff8ffffffd6fe0ffffffffffffcefaa7fdf656fcffff8fffe14fffe0ffffffffffffc3ffe6fff6944fffcfffffe1fff2a0ffffffffffffc6daa6fdf6954ff2bfffffe1fcefe0ffffffffffffcfffe7fdf6964cffffffffe1fff2a0ffffffffffffcefa67fdd6964cf2bfffffe1ffffe0ffffff6dcfffffffffffffffffffff2dffdefd9ffffd853ffdcfffffffe7fffffffff2fffdfffffd957ffd853f6fffffc3ffe48fffffffffcfffffdeffffcdfd8fffffffffcffa2783ffd4ffffff2fffdefd9ffffd8fffffffffcffae78fffd5fcf2ffffffdefd9ffffd8ffffff53ffefafffff6fffcfffffdffff756fd1fffffffffffffeefe5ffffffffffcffdffff75654dfff53ffffffffefa3ffff6ff47ffff2fffff75657ffff53ffff53ffefae7fff63f44f2ffffffff77f57fffffffffffffc7fae58fffd4ffffffffffdefce491fffffffdcfffcffae78fffd6fcf2ffffffdefff491ffffffffffffc2eae58ff6d54bffffffffff74efcdffffffffffffcefa678bf6d6ffffff2dffff77f2bfffffffffffffcefae78ff65648f2fffdffff77fffffffffffff53fcfffff8ffffffffffffff6d7fd9551fd8fffffffffceffff81ffffffffff2fffd76bfffffd853ffff53fceffe78dffff47f2ffffffd7fff57ffd8fffffffffcbffe6ffffd7fff2cffffffffff4bffd8fffffffffcffabf87fffffcffff2ffffffd9fd1fd8fffffffffcffae7ffffd7fcf2fffffffffd94bffd8fff6fffffcacfe687ffffffffcf2fffff6bf2bffd8fffffffffcaefe68dffff4bf2cfffffff6bfffffd8fffffffffcefaa785ffd744fffffffffffd92bffd8fffffffffcefae78defd748f2fffffffffd9ffffd8ffffff53fc6effffdffffffffcfffffd74fffd1fffffffff53fcefaff8df63ffcffffffffff4d6fffffffffffffffc2dfe68bffffffffcf2fffd7fff57ffff53ffff53fc6efe68dffff4ff2cffffffffff57ffffffffff53fcefabf81f6bffcffff2ffffffd6fffffffffffffffcacabf8bf6ffffffff2fffff4cefd1ffffffffffffcaeae68df617fff2ffffffff4cefd1ffffffffffffcefabf85f67ffcffff2fffff4fffd1ffffffffffffcefae78de657fcf2ffffffffffffd1ffffffffffffcada258bf6d74ffffffffffffce28dffffffffffffcaeae48de6974ff2ffffffffffffcdffffffffffffcefa6785e6974cffffffffffffffffffffff >>> (168*i)) &&& 0xffffffffffffffffffffffffffffffffffffffffff

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
end PEqualNP.Research.PlaneCase35FifthGuard
open PEqualNP.Research.PlaneCase35FifthGuard PEqualNP.Research.PlaneCase35FourthOrBudget in
theorem PEqualNP.Research.PlaneCase35FifthGuard : ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
    pos p.val &&& (neg (f i).val ||| neg (f j).val) = pos p.val := by
  exact ⟨fun i => ⟨ix i,neg_match i⟩, fun i j h => pairGuard i j h⟩
