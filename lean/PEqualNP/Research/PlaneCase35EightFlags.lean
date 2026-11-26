import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35EightFlags
open PlaneFirstAndSeparation PlaneFirstAndBudget PlaneCase35FourthOrBudget
set_option maxRecDepth 8192
set_option maxHeartbeats 0
-- Each bit marks one of the first eight positive flags, grouped on lines 0 and 1.
private def omittedFlags : Nat := 255
private def indices (i : Nat) : Nat :=
  (0x190c6e33178ac4e230f85c1e02ff7dbe5eef377bb5cee570b7dbad96bb55a2cf64b1582bf5eaed72b758abd5aab54a9d46a14fa6d2a9348a3d1685409fcfa7b3b9d4e66f369acce652f964aa532692c9245219047e3b1b8cc622f168a44a210f8743615088341609038140600fe7dbe5eef579bc9e2f077bb9daec753a5d0e772b8dc4e17037dbadc6d365acd569b419ecd6632d92c863b198ac461b0980be5dae56cb459ac960af56aa94ea652a9146a250a7d3c9d4e26932984ba592a94492451e8e46a31148943a190883411fcfa7b3c1d8e670379b8da6b351a0ce6531184c05e2e970b65a2c960ac55299409c4c25928924622910823f1f0ec74371a8cc6230170ac54291409446211007838190c05428130883c1a0b048200e04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0x64080d224028d0e2a040a6290422e28042a6228442e22044a621848262104a262084c222024e061908226180832e130a02e128242e120a42e110a22e1082522102870a0e0c08a0c0c1860b0c02e0a0c0a6090c222082c30a070e00a060e08a058680a050e80a0486902042c90e038602e030e02e028642a024a48e0186822012ca0200a4d020068e09c801189c4001c9c2010c9c0011c9940214991022499002349880138986020c984021c9830304982030c981032418021345700045d64000d962004cd60004d554001555080515500055d4c00195488111d480119d44001d942014c5408151140215453100255300065d2c04095290421d280429926040c5250405d24040d922044c52104251202464d150205d148211d140215d110225d108251110207450c8411d0c041950985015090521508851110825309070604906060cd058601d050605d0486119038700903070490287401022544d0187011012524100a5508e4008cce2000e4e10086ce0008ecca010a4c88112cc8011a8c4009c4c30106cc2010e4c181824c101864c081920c021944b810224b210064b100264b01026caa100aca8102a8a6100c8a4108cca2100e4a100a60a030a449890124981032896120489492108941214c930206c929202c921206c910226c909212090303448a9102c8a110a48891120883130886120c88492900843094c838302c830306c8293028825308c81838208121a4080b19008071a047200464710007470804347000474650085c64008dc62004e4618083461008746080c3c6040c945c08114590803458801345808134550805454081545308064520846451080745080530502854c4c081944b0902c4a090a449810344909034488113c484909445088504428944430906042294444181830412984040a1d004069c04390023438900343810234329042432104643100274309043030306482e140842c9401c2c140942a9402c2a140a429840342904234289403c285029826140c425848142504854249481024348442294420223444421848302124a4020b4c002070e041c901141c18114190823418901301838308170a048161a04c150a05c1492110143814c130a06c1292420123844c114a21c10d241010786080e1c0840c941100c3c1040b850240b0d0240a950200a3d0040985030092d20008b51000879208070e040063c04c0586810052c84004b490c0387020032d04002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x8000200800000840000024000001200000010000000800000040000002000000100000008000000400000020000001000000080000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x7c07df01df0000003e03fd00000007f837c000000000000000001ed80052215000d1010f1d1c5c2d8020801b6807c000904018800a20001518000001000002ff7f1c07400000000000000007efbf363ee1d1e79cf3e28fe1f02830301d00800000000000000dfebed7df1c200000000000007dff9a7c47333dc478c3208204fffffffffe0000000000000000000000000000000000000000000000000000000000000000fffffffffffffffe0000000000000000000000000000000000000000000000007ffe000000000000ffffffffffffe000000000000000000000000018000000003c00fffc000000007ffe000000000fffffffff800000000000000003fe00000000007801ffc000003c00ffe0000007ff0000003ffffffc000000000000ff000000e02380c01f80000000780ffe0003c07ff0001fe00001fffe000000e0607e00040800381c003f0000e0230600f000003c07f00e0ff800f800ffe000000030fc0123049209c7187c04080060e007000c118206000703e063e0700f8026071661e041610080900031e12304a84e3278410030c0c062610c018e27863c08ca42accc04280009252196cc4161020480331262545959080c6184a48332d9a15090055500000910004aa2d5042800492a554428810a0a52552aa90925545aa00000000000000000000000000001bf7edff330000000003dfce79ed6df33499401dbfeaaa0000000000000000000000000000000dfbd7d40000001bdb6aae951ff00fffee00000003fe07fffe000000000000000000000001feffc0001ffbfc0001f01f7c077c000000f80ff40000001fe0df0000000000000000007b60014880000000002c4f00dc0000783f877e0000078ff000001f9f800000000000ff07fc1e0001e1e0000000000000002c4f01600018786f000033c0000f3c0000001c3e331b000330002d8740a1800320000000000002c980b00263600066003600006462e28600283860006c31450020002d1a05100a000000000a502805280500a0058010d10c0b6d10fec003798408386003619b0200168e12100000006c603020802a001a2021e3a38b85b00410036d00f8001208031001440002a300000020000000000000007effe8dc7f681a55e3ab9f2da15137a07d01e81a00aa80ed0003482ff7f1c07400000000000000007efbf363ee1d1e79cf3e28fe1f02830301d00800000000000000dfebed7df1c200000000000007dff9a7c47333dc478c3208204 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0x97ffffffffff83f6bfffffff2e6ff2ffffffff1ff0ffffffffffff8ff6bf4ff2fffe6ff2fff93fff1ffffffffffffabffffffffff2738ffffffd94bfff1ff0fccffffffffffffffffff2b38fffff6bffe0ff1ff0ffffffffffffffffff48c2b38ffff2fd9fffff1ff0889ffffffffffdf67ffffff3fffff24fffffff1ffffffffffffffffff67ffff27f8ffff24fffffff1fff8bfffffffffffff6bffffffffffff2fce2a0ff1ff0fffffffffffffff6bffff2bf8ffff2fcefffff1fff8bffffffffe6fff6bf4ceff3fffffffff2a0ff1fffffffffffffe6fff6bf4ce2b38fffffffffffff1fff6ffffffffffffffffffff2f3fdfff2fd9fcdff1ff0fffffffffffffffffffcd2f3fdfff2fd9fffff1ff0fffffffffffffff6fffff2fffdfffffce4bf731ffffffffffffffffff6fffffff32dfff277ffd1ff1ff0fffffffffffffff6fffce2fffffff277f4bf731ffffffffffffffffff6ff4bf2fffdfff2fcefffff1ff0fffffffffffffff6ff47fff3fffff277f2bfff1ff0fffffffffffffff67f48e2f3ffffff77ffffff1ffffff53fffffe68ffffffff2f3fff6fffff551ff1ffffffff0ffffe6ffffff47f2f3ffffff6bf57fff1fff6ccfffffffe6ffffd4fff2fffffff2fff4bfff1fffffffffffffff8fffd4fcc2fffffff2fd94bfff1ff0fccfffffffff8dffff4bf2fffffff26bffcdff1ffffffffffeefe68dffd548d2f3fffffffd9fffff1ffffff53ffffffffff6fffff2ffffffff4d657f331ffffffffffffffffff6fffcc2fffffff24d6fffff1ffffff530fffffffff6ffffffff2ffff2fd6fcdff1ffffffffffffffffff6ff4ff2fffffffffd654dff1ffffffffffedffffff6fffcdff32ffff2fd6fffff1ffffffffffffffffff6bf4cd2fffffff2fd6fffff1ffffffffffffffffdf6d4ffffff2ffff24cefffff1ffffffffffffffffdf6d4fff2fffffffffce4bf331fffffffffffffff89f6fffcefff2ffff24fffffff1ff0ffffffffffff8dc6d6fce2fffffff24fffffff1fffffffffffffff8bf6d44ffff32ffff2fcefffff1fffffffffffffff8df6954ff2fffffff2fcefffff1fffffffffffffe681f6964ceff3fffff2fff2bfff1fffffffffffffe48dd6964ce2f3ffffffffffffff1ffffffb28ffffff87ffff47f27fbbfffffff93ffd8ffffffb28fffffffdcfff47fffffea957b7fffffffffffffb3fffffffffffd7fccfffbbf97ffe9911fffffffffb3ffffffffff61747fffffeafffb6993ffffffffffb28ffffe5ffffff47ffeffeaffffff57f73fffffffb28ffffff8bffd5ffffffbbffdefe9fcdfffffffffb3fffffffffffd5fcdfeffeafdefe9fffffffffffffffffffe487fffffff2afbaaffffffffffd8ffffffb28fffffffffffffccfeffeafd7b69fd1fffffffffb3fffffe5fdcfff47ffeffeafd7fe9ffffffffffffb3fffffffffffd7fffffffeafffb6949133fffffffb3fffffe5ffffd7fccfefbbfffffe9491fffffffffb3ffffffffde6d74bfffffeafffb69fcdfffffffffb3fffffe4fde61748dfeffffffffe9ffffffffffdcfffffffffffffd643ffefffffe1b7f920fffb3ffffffffffa3ffffffffccfffba6fffb56920fffb3ffffb10fffffffdcfd6fffffffe6961b7f93ffffffffffffffffffffdcfd643ffffffffe1b7f93ffffb3f95cffffffa3ffffffffcd23fba6ffffd6ffffffb3f97fffffffffffff67fffffffffffdeb7f93ffc8b3fffffffffffff83ffd6fff23fbbffdefff93ffffb3fffffffffffff83fffffff27fba6fd7fffffffd8b3f949fffffffffffffffffffefba6ffffd9ffffd8b3ffffffffffa3f87ffd7fff27fba6ffffffffffd8ffffffffffffa3f81c63f47fffffe6fd7b7fffffffb3ffffb3ffffa7f87ffd7fff27fba6ffffff911ffffff97fffffffffffde67fffffffba6fffb7fffffc8b3ffffb3ffffa7f85e65747f23fffffffb7f93fffffff8bffffffffffffffd5ffffeffdffe1fceffffffb3fffffffffffe4ffffd6fcefefb9ffe1ffffe0fffb3fffffffffffffffffff43f26fbbfffffd9560fd8ffffccffffffffffffffffff2bfbbffe1fd9ffffd8b3fffffffffffffffffd5fcc2afbbffe1fd9ffffd8b3ffffb10ffffe6fffffffccfefbbf8bffd6fe0ffffff88cffffffffffdffff43f23fffffffb7f560fffb3fffffffffffe6fff63f40cfeffffffffd6fe0fffb3ffffb3fffffe6ffffd6ffffeffff8a1fff4a0fffffffffffffffffffdf615ffffffffffe1b4effffffb3ffffb3fffffe6fdf65648efffffffe1b7ffffffffffffffffffffffffffff43ffffb9ffffb5654d73fb3ffffffffffffffff6fffcdfeffdfffffd6ffffc8b3ffffffffffa25fffffffcd22ffdfffffff57f73fb3ffffffffffa3f8bffd5ffffffbbffdefcefcdfffb3fffffffffffe5fff6d647ffefffffdeb7f2bffc8b3ffffb3ffffa6483ffd6fce2bfbbffdeffffffffffff6c9fffffffffffffffffffefbbffd7b5957ffd8b3fffffffffffe683fffffff27fbbffd7fffffffd8b3f6fffffffffff87ffffffffefbbfffffff28dfd8b3ffffffffffabf87fffffff2bfbbffffffffcdfd8fffffffffffffe6ffffd7fcdfeffffffffd92bffd8b3ffffffffffaa687ffd7fcd2bfbbfffffffffffd8ffffffb10fffabf8bffffffffffbbffd7b7ffd133fffffffb3ffffabf8bfffffccfefbbffd7fd6fd1fffffffffffffffffffdf6ff43ffffffffd7b56fcdfc8fffffffffffffff89ffff43f23fbbffd7ffffcdfffb3ffffffffffffffdf6fffcdfefffffffb56fff248ffffffb10fffffffff6d7ffffffffffffb4efff308ffffffb3ffffabfffffd7fff23fbbfffffce49133fffffffb10fffffffdf6fffcefefbbffffb7ffd1fc8ffffffb3ffffaa687ffd7fce23fbbfffffff4bffffffffffffffffffffdf6d743ffffffffffb4effffc8ffffffb3ffffabf85f6174bf2bfffffffb4efffffffffffffffffffe6fdf65744efffffffffb7fffffc8ffffff528ffffffffffff4fffe7feafe1fff920fffffffffffffffffffdcfd4ffffe7feafe14e9ffffffffffccffffffffffddffffffffffeafe1fff920ffffe8fffffffffffffddfd44ccfe7feafe1fe9fffffffffffffffffffff87fffffff267afffffffffd1fd8fe8fc9ffffffffffdeffffcdfe7feafff6bfffffd8fe8fffffffecfff87ffff47f267affffffffffffd8ffffff53ffedfff81dfffffffe7aeafd7ffffffffffff94cffffecffffde63fffffffaeafff4ffffffffffffffffffecfff85e63ffccfffaea97f4fffffffffff97fffffffffffff6bffffffffeaffffe990dfc8fe8fccfffffffff85efff4ff23faeaffffff90dffffff97fffffffffffff6bffcdfe7feaffffe9ffffc8fffffffe8fedfff85e6974cd23ffeaffffe993ffffffffdcffffffffffffffffff2bfaeafff77ffe0fd8fe889cfffffffe7ffffd4fff23ffeaffffe94bfffffff8bfffffecfe4ffffffffffcfaeafff77ffffffffe88bffffffffe7fff63f48fffffeafff769fe0fffffffffffffffffffffffffff27faeafe1fff4bffd8fe8fffffffffffffdcfff4bf2bfaeafe1fe9ffffd8fe8fff528fffffffffffffffffffea8a14e9fe0fffffffff528ffffe7ffffff4ffffffeafe1fff560ffffffffffffffffe7fdc614fffffffea8a14ffffffffffffccfffffffe4fddfffffffcffeafe1fe9fffffffffffffffffffe7fdd6954cfffffeafe1fe9fffffffff6fffffffffffffffff47fffffeafdefe92bffd8fe8ffffffffffff83fffffff2bfafffdefffffffd8fe8fff528ffffffffffffffffffaeafdefff55173fffffff528fffffffff6ff44ffffffffff769ffffc8ffffff53ffeffe7ffffff47f23faeafff77f57ffffffffffffffecfe5fffffffff20faeafdefff4bffffffffffffffffffffff6fffcfffffeafdefe9fd1fc8fffffffffffffe78bffd4fcf23faeaffffff4bf73fffffffffffecfe58bffff4bffcfaeafdefe9ffffffffffffffffffffffff6d444ffffffffdefe9ffffc8fffffffe8feffe783f61548f2bffeafff769fffffffff6c9fffffffe7fdeffffffffffeaffffe9491fd8fffffffffffffe787fffffff27faff6fffff491fd8fffffffffffffe7fdefff47fffffeafff6bf2bffd8ffffffffffeffe785efff4bf2bfafffff6bfffffd8ffffff528feffff89cffffffffffeafd7fe9fd1fffffffffffffffffffdd6fffcfffffeafd7fe9ffffc8ffffff53ffeffe781dfff4ff23ffeafd7fff57ffffffffffffffffffffde6ffffffcffeafff4e9ffffc8ffffffffffecfe5fdeffffff20ffeaffffff4bf33fffffffffffffffffde6fffcffffffffff4e9fd1248ffffffffffeffe789e6d7fcf27ffeaffffe94bfffffffffffffffffe5fff6ff4fffcfaeaffffe9ffffc8fe8fffffffedfe485efff4ff28faeafffffffffffffffffffffffffe7fde6974cfffffffffffe92bffc8ffffffffffeffe785e6974cf2bfaeaffffffffffffffffdcffffeca7ffffffffff2278e6fffffffffffffd0fffffffffa3fffffd4fff23f8e6fff74e920ffffff97fffffffffffff67fffffe7fe6fff77ffe0fc8ffffffffffeca7fffffff40e23f8e6fff77f93ffffffffccffffeda3fffffffffffff8e6fe1fd6fe0fff53ffffffffeda3ffffffffccfff8e6ffffd6920fff53ffffffffeca7ffdcfd6ffffe78e6fe14fffffffffff97fffffffffffff6bffffffffe6fe1fceffffc8ffffccffffffa3ffddfd4fff23ffe6fe1fff920ffffff949fffc3fffffdd6bffceffffe6fe1fff93ffc8fffffffffc2da7ffddfd64ce27ffe6fe1fff93ffffffffdcffffffffffffffffff2e7fe6ffffd993ffd853ffdcfffffffffffffff43f2ffffffde77f90dfd8fffffffffffffffffffd4fcdfe72e6fdefd9ffffd8ffffdcfffffffffffffd4fcd2ffffffdefd993ffd8fff95cffffffafffffffffffffffe6fff75690dfff53ffffffffeeffffff63ffcdfe7fe6fff756ffffff53f97fffffffaffffffd4fffffffe6fdefce93fffffd0ffffffc7faff8ffffffcefe7fe6fdeffffd1ffffd0fffffffffaff8ff61443fffffe6fff74e93fffffff97fffffecfff83f67fffffe7fe6fff77f93ffc8ffffffffffeeaff8ff65644e2fffe6fde77f93ffffffffffffffeeffffdcfff47f2fffe6fd7fd993ffd8ffffccffffffffffdeffffff2fffe6ffffd993ffd8fd0fffffffffafffffffffcc2fffe6ffffd993ffd8fd0fffffffffa3ffdefffffffff2e6fff6bf90dfd8ffffccffffffffffdefff43f2ffffffff6bf90dfd8ffffffffffeca3ffdeffffcdfff2e6fff6bf93ffd8ffffffffffeeafffdefd740c2fffffffffd993ffd8ffffffffffffaff8ddffffffffffe6fd7fd6fcdfff53ffff53ffeeaff8dd6bffcdffffe6fd7fd6ffffffffffffffffffafffde63ffffffffe6fff4cefffffffd0ffffd0caeaff8de67ffcefe7fe6fff4fffffffffff97fffffffa3f87f6bffffffffe6ffffce93ffc8ffffffffffffaff8de6974ff2fffe6ffffce93fffffff97ffffcada7f85e6bffcefe72ffffffffffffc8fffffffffcaeaff8de6974ce2e7fe6ffffffffffffffffdcffffffffffffffffff28f8dfffffffffffd8fffffffffffffffffffff40fffffdffe1fd92a0fd8ffffdcffffffa3ffffffffcf2bf8dfffffd9ffffd8fff8bfffffffffffff67fffffff8dffff77fffffc8fd0fffffffffa67fffffffff23f8dfffffff4bfffffd08bfffffeca24fff63fffffcf8dffffffffffffffff8bffffffffe7fff67f43ffffffffff77f2a0fc8ffffffffffefa67fff67f48f2bf8dffff77fffffffffffff510fffffffffffffff27f8fffe1fff57ffd8ffffc9ffffffffffffffffcffffffffe1699fe0fd853ffffffffeffffffffff43f27f8ffffffd9560fd8ffffc9fffcffffffdffd4ffffffffffe1fd9ffffd8fd0ffffffcffabfffffd4fff27f8ffffffff4bffd8fd0fffffffffffffdffd443ffcfffffe16bf2a0fd8ffffccfffc2cffffdfffffff28f8ffffffffffffd8ffffffffffffffffdffd440ffffffffe1fd92a0fd8fffffffffcefa3ffdcfd548f2bf8ffffffd9ffffd8ffffff53ffefabffff63fffffff8fffff4d6fe0ffffff8bfffffffffffff6bfffffcf8ffffffd6ffffc853ffffffffedfe6fffffffff20f8ffffffff57ffff53f8bfffffffffffff6bffcfffffffffffd6560fc8ffffff53ffefaa7fff6bf4cf23f8ffffffff57fffffff8bffffcffffffdf67fffffffffffe14ffffffc8fffffffffcefaa7fdf656fcf23f8fffff4fffe0ffffff8bffffc3ffe6fff694ffffffffffe1fceffffc8fffffffffc6daa6fdf6954ff2bfffffe1fcefe0ffffff8bffffcfffe7fdf6964cffffffffe1fff2bffc8fffffffffcefa67fdd6964cf2bfffffffffffe0ffffff6dcfffffffffffffffffffff2dffdefd9ffffd853ffdcfffffffe7fffffffff2fffdfffffd957ffd853f6fffffc3ffe48ffffffff2fffdffdefd9fcdfd8ffffffffffffa2783ffd4ffffff2dffdefd92bffd8fffffffffcffae78fffd5fcf2fffdffdefd9ffffd8ffffff510ffffffffffffffffcffdffdefff55173fffffff510fffafffffffffcfffffdffdefd6fd1fffffffffffffeeae5ffffff43fffffdffff75654dfff53ffffffffefa3ffff6fffcfffffdfffffd6ffffc8ffffff53ffefae7fff63f44f2fffdfffffff57fffffffffffffc7fae5ffffd4ffffcffdfffffff4bfffffd0ffffffcffa7f8bf6ffffffff2dffff77fffffc8fd0ffffd0cffae78fffd6fcf2fffdffdefff4bfffffffffffffc2eae58ff6d54bffcffdffff77ffffffffffffffffcefa678bf6d643ffffffffff77f2bffc8fffffffffcefae78ff65648f2fffdfffffffffffffffffff53fcfffff8ffffffff2ffffffd7fff551fd8fff6ffffffeffff81ffffffffff2fffd76bfffffd853fffffffceffe78dffff47f2fffffffffff57ffd8fff6fffffcacfe6ffffffffffcf2ffffffffffffd8fd0fccfffcbffe6fffffffff2cffffffffff4bffd8fffffffffcffabf87fffffcffff2ffffffd9fd1fd8fd0ffffffcffae78fffd7fcf2fffffffffd94bffd8ffffffffffecfe687ffff43ffff2fffff699fcdfd8ffffccfffcaefe68dffff4bf2cfffffff6bfffffd8ffffc9ffffefaa785ffd744fffffffffffd92bffd8fffffffffcefae78defd748f2fffffffffd9ffffd8ffffff53fc6effffdf6ffffffcfffffd74ffffffffffffff53fcefaff8df63ffcffffffffff4d6fffffffffffffffc2dfff8bf6ffffffff2fffd7fd6fcdfc853ffff53fc6efe68dffff4ff2cffffffffff57fffffffffffffcefabf81f6bffcfffffffffffd6ffffc8fffffffffcacabffdf6d7ffffffffffff4ceffffc8fffffffd0caeae6fdf617fff2fffffffffce4bfffffffffffffcefabf85f67ffcffff2fffff4ffffffc8fffffffffcefae78de657fcf2ffffffffffffd1ffffffffffffcada258bf6d74ffffffffffffce2bffc8fffffffffcaeae48de6974ff2ffffffffffffcdffffffffffffcefa6785e6974cfffffffffffff2bffc8fff >>> (168*i)) &&& 0xffffffffffffffffffffffffffffffffffffffffff

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
private theorem beyond : ∀ p : Fin 52, omittedFlags.testBit p.val = false → 8 ≤ p.val := by decide +kernel
/-- The selected negative rows share a positive witness outside lines 0 and 1 for every pair. -/
theorem pairCertificate (i j : Fin 257) (lt : i < j) :
    ∃ p : Fin 52, 8 ≤ p.val ∧ pos p.val &&& (neg (ix i) ||| neg (ix j)) = pos p.val := by
  obtain ⟨p,off,h⟩ := retained i j lt
  exact ⟨p,beyond p off,h⟩

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
end PEqualNP.Research.PlaneCase35EightFlags

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35EightFlags in
theorem PEqualNP.Research.PlaneCase35EightFlags : ∀ (extra : List Column) (gs : List Gate) (o : Nat),
    (∀ w ∈ extra, ∀ p : Fin 52, 8 ≤ p.val → w p.val = true →
      ∃ v ∈ initial, v p.val = true ∧ ∀ n : Fin 468, v (52+n.val) = true → w (52+n.val) = true) →
    (∀ p : Fin 52, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro extra gs o h hp hn
  apply separated_bound _ gs o _ hp hn
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j lt
  obtain ⟨p,low,hp'⟩ := pairCertificate i j lt
  refine ⟨p,?_⟩
  have good0 := initial_good p ⟨ix i,neg_match i⟩ ⟨ix j,neg_match j⟩ hp'
  intro w mem
  rcases List.mem_append.mp mem with prev | const
  · rcases List.mem_append.mp prev with raw | ext
    · exact good0 w raw
    · intro on
      obtain ⟨v,hv,hit,down⟩ := h w ext p low on
      rcases good0 v hv hit with x | y
      · exact Or.inl (down ⟨ix i,neg_match i⟩ x)
      · exact Or.inr (down ⟨ix j,neg_match j⟩ y)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at const
    rcases const with rfl | rfl <;> simp [good]
