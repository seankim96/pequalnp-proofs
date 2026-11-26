import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975Family3Mask
open PlaneFirstAndSeparation PlaneFirstAndBudget

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


def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 &&& b 13) <<< 26) ||| ((b 0 ||| b 14) <<< 27) |||
    ((b 1 &&& b 13) <<< 28) ||| ((b 1 &&& b 18) <<< 29) ||| ((b 2 &&& b 15) <<< 30)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def base : List Column := List.ofFn (fun j : Fin 31 => input j.val) ++ [fun _ => false, fun _ => true]
def omittedFlags : Nat := 0x40f000f00000

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x1d3e97439fcee6f3397cae4f1f8dc3e06ff7bbcddeeb73b3d96c761afd76b759abd469f4da5d268f3f9acbe53258cc5e2b1388c3e170782c0e02ff7dbe5eef579bc5deed75ba5bedd6cb5d92c561b057ebd5dae56eb559ac55ead4fa7536994ba55228f46a2d128742a0d02652b94ca24d2491c8a3f1e8ec6e35198a44e251188436150883c1a0901803f5f6fa7cbe1eef67abd1e6ec75385c0df6eb71b6da6b355a6d268b419ecd643198ac461b0982c05f2f578bb5cad96ab258ac15eae56ab156aa54aa14ea64fa3914843f1f4de6e369b0d66833998ca6331178ba5c2d968b2582b13c964a2491c8c45200fc7c3c1d8dc6632188c05e2e168b0562a148a04a22108803c1c0d86832180b05026110803c1a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x39002303880038b804228380023832804283220448b204068320246032004683108250310207031002703080438304061830286403020648300a4503008650b00426830024702a8002a2a100a2aa040a82a000aa2980032291022229082122900232288003a28402982818282a8142a028102a22808292a8042a826000ca2500852248081a2440898242084a22a040a2290422228042a2228442222044a221848222104a222084c2a2060e0a2040e822024e0219082221808322130a022128242a124a402120a42a114a202110a222108252a106860a104a6020b0c0220a0c0a2090c222082c302050e802048690a044a882042c9020386022030e022028642a024a482018682a0168a0a014aa02012ca0200a4d0a0068e0191022419020341900234988412818821301880138184021c18303049824308182030c98143201812124181032498043281802134944001d9404149931002593040619300065929042192840299280429924040d1222444122044c9210425920406912024649110225910c24191082519104261110207490985019090521908851190841291082530106060c90486111038700902c340102874090243481022544901c301901870190143211012524900c341100a5500c8011a0c4009c0b810220b210060b100260b010260aa100a8a850280a8102a0a4108c0a2100e0a100a68a070a08a050a80a030a4098901209810320930206092120609102260909212090303408a910288a510808a110a0889112888712088851280883130086120c084929088452880830306882d30008293028825308881c380081838288161a088143a008121a4880f180880d380080b19088071a0864008d851080784c081984909038444889044289484069c0839002383890038385021838102303210468310027830d04183090438305061030306482c140902a940202a140a8298403829042382894038285029026140c82450890223444821848302124a4820d0c1020b4c082070e0819482181908238189013818582101838300161a0481492118145a0101438140130a06812d240012924281278408125a4001238448114a21810d241810786000e1c0880c580900c3c1000b850200b0d0200a950280a790080a590800a3d0080985038094921008b51080879200070e048065a080063c0480586818054a810052c84804d281004b49000387020032d04802f140802d340002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3fffffffffffffffffffc00000000000000000000000000000000000000000001ffffe000000000000001ffffffffffffe0000000000000000000000000000000f0000fffe00000000000fffe000000000fffffffffff80000000000000000000000000000f80000000000000c00000000600000000003f80000000000000000003e003c0043ff800000000001ffe000000fff8000000103fffffe00000000000100e001e010003ff80001c000e00f800007803f80000041ff8000ffffc00000004808088804e01803c0001c000e003e000a38183f800018f03f807c001fff000000020002010000001e000100808000c00202000038002b00103001e00e007f800100c000006601e0c0f000700030005f0048818e13c000020614008fc4fc383f000000887008c28c5467902709048608781020a0011f051080c18c041061939860042c0224015021012a20000000328f3300010a426c70043150b1118428a13ba91001100900060a6042c885252094215500860098adb42914051644b7432a51bc0482400000028021105d2048022108114002810a00b60c0100561114914c95b60000000000000000000000000000000006fdf5ffee0f00f7f3e73fbef9e6c679000000000f001defed5d0000000000000000000000003f0000006ee7bd75ec4506c7e800007f9001fbd3000005f41deaa8000000000000001fae80000bcd5ae42c15d81df80001fd0efa28fb0001e07ee80001e01ff48000000000eeb00036a48000000000000000000003bfd00007cfff000007f1fff12000000000007fe01ff00000707f207e0003c3f0000000000000405e00030ffc700002f800000001f0383f9f8000c8cf1ce00618000586de01e1800000000000085e009c00fb000001e7eee0ff66818be1b30077f0f9f8f358030b67a50e00e202d30a13b00280140005a0f9a1789c001020a804dc0600029500380031894002240000002a80080402007e8d2b0c37a84001084016c5875005080c3e40195100540028e00000182040000000000000000000000071ada8f6208222e393a024043106202a0130800052200000037eb77fc7ace0e800000000000002fac7eb02900a3747c20c0a00e200200000000000000000000000003fe6f7907400000000000f9ef4f54f30190183404 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010000000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xfffffffffffffcdfff0effdfffffe9fff731b3fffffff83ffffffffff0bffea6f26bfffffffb28ffffff8bfffffccffffeffc7ff2b69fc6fffffffffffffdc6fffccfc6feffeafffb69fffff1ffffffffffffffffccfc7feffff6fffd9fe0fffb30fffffffffffffff27ffef8ff8bffff4bfff1b10fffffffff67fffffff0bffc78bfb7fffffff130fffffffff67fffffc7ffffff0e1b7ffe00b1b3ffffffffff67f4bffc70bffff8bfb7fffffffb30ffffffffffff47ffffffffdffff77f2bfff1b30ffffff83f67fffffc6ffffdf0ff77ffffff1b3ffffa7ffffffffcd2860efffffffffffff731b3ffffabf83ffffffffff0affff6ff6bfffffffb30fffabf81c6ff44c2460afffffffb7ffffff1b3ffffffffffffffffffffef2ffff2fff291271b10ffffff8bfffffff247fefffffff4ff491ff1b3fffffffffffff47fffffeffff0f2b7f2bffffb30fffffffdffff47ffff0ffffffffb7f2bf27fb30fffa7f89cfff48cffffefffffffb7ffc6fffff0ffffff81f67ffff286ffffff0ffb7ffffff1b3ffecffffdcfffffffffff38ea6ff6bffe0fffffffffffffff6bfffffc4ffffea8bffcefcd331ffffffffffff6bfffffff0b3fff8bffe9fc6fc5128fffffffff6bffccfc40bffff8bffe9fe0ff1ffffecfff83ffffffffffff3aff6defd9fff73fffffecffffff6fffffffffcfadffff74efcdff1fffffffffffffff47ffffff3ffffff7692bf27ffe8fecffffff6fffcd2bfff3ffffff769fff73fffffecfff81cfffffffff0bfaff6f2fffffffd8ffffedfff81c6bffcc246ff3affffffe9fffff1fffffffffffffff4fffc4ffffeaff2fff28d27ffe8fedffffffffffff2bf0cfaffff2ffffff33f13ffecfff89dffffff284fcfafffffffffcdff1ffffffffffddfff44dfffff3feaffffe92bf271fe8fedfff8bfffffccfffff3afffffffffc6fff13ffeca7ffff67f4cc2440bffff8bfffffe0fffff0feca7ffff67f44d2c4ff3ffffff77ffff73fffffecaff81cfff44cfff0bffff6f26bfffffffff0fedaff81c6bf44c2460b3fffffffffffffffff0fecfff8dc67ffcc244ffffffffffff491ff1ffffffffffffffffff27fff38fffe1fd9491fd8ffffecffffdfffffff2bffcf8ff6ff6bffff33fff0fecabfffffff48cfffff3fff6ff699fe0fffffffffffffffffffcefffff3fff8bf4ff291271ffffecffffff67ffff27fff38fffff4ff491ff1fffffffffffffff4fffffffffff8a1fce28dff1ff0fffabffff6bffff284fff8ff8bffcefcdff1fffffffffffffff4cefffff32ff8bffff2a027fff0fffffffdd67ffcefffff38c70ffffffff085ffffeda7ffff67fffffff0bffff8bfffffc6fc5130fedffffff67ffce287ffffff0ffffffe00b1fffffffff8fffffffffc4ffffdf6defcefcdfffff0fffaff83fffffcdfffff3fdf6defd9fff718ffffffffffffffffff2c4ffffdfffffce4bf331fd0fffffffffffffcefc4ff32dfffffff29127fffffffffffffffffff2ffff3ffffff4ff4bf70513ffffffffffffffce2c4ffffdfffffff491731ffffffafffffffffffffffcffc7fff74effffff130fecafffff6ff4bffc4fcfffffff74effffffff0feca7fffffff47fffffff2dffff77f2bffffff0ffffff8ff67fffffffff3fff0ff77ffc6085fffffffffffffff48efff0f3fc7fffffffc673fff0fffffffffffffff2ffffffff6f2fce48d318fffffffff8ffffffcc244ff3fffffffd9491fd8fffffffff8dffff4bffc4ffffff6f26bffcdffffffffffff81fffffcdfffff3fff0f2699fff0bfffffedabf89d6bf4ff2c70cffffffffcefff33fff0fedabf81dfff44dfff0fffffffffff2bf27fff0fedaff89cfff4ccfff0b3ffffffffffc6fff130fedfff81d6bffcd2c6ffffff0f2ffffff0b1ffffffffffdfffffffffffcf2ffff24ce2bf27ffd0fffffffdf6fffff2c4fffffffff4ff4bf331ffffecfff89fffffcefffff32ffffffff29127fffffffffffdcffffff27fff3fc7ff24ff4bffc5110fffabf8bffff4fffc4fff2ffffffff28dfffff0ffffff8ff6bfffffffffffc70f2fcefc6fc5ff0fedafffddfffffffff0cffc7fffffffff33f130ffffff8ff6bfffffc7ffffff0fffcefcdff1ffffedfff83ffff47ffffff32ff0fffff2bf0bfff0ffffff8dd67ffcefffffffc70f2ffffc60bffffc7fffffffffffffffffcffdffdeffffcdfffb28ffffff83f63ffffffffefaff0defe9fff0bffffc7fffffffffffcdfff0effffffffe9fff73ffe8ffffff87ffffffffff0affff6ffffffc6fff128ffffff81effffffffffefaea0ff6bffff098fffcbffff83ffffffffc60affff6fffffffffd8b28c7fffffdc63f44cfc50afffffffb7ffffffffe8ffffffffffffffffc5fcffeaffffff48d33fb3fcbfffffffffffff27ffefaffffffe94bffc513fffffff87fffffcc245fefaeaffffe9491ffffffcbfffffffffffff2bf0cfffffffb7ffff305128ffffff87f63fffffc5fffaea0ffb7ffcdffffffc7fffffdefff4bffc50cfffffffffffff33fb28cbfffffff6ff48cffffeffffffffe9fc6fc5fe8ffffff81e63ffcdffffffaff0ffb69fffffffe8c3fa3f83f63f40c2450afffffffffffffffffffc3fa3f85c67f40c27ffefffffffb7fffffc5ffffffa3ffff63fffffffffffdf8bf74efcdfffb3fc3fffffff67ffffffffeffff8bf77ffc6705ffffffffffff63ffcefc5feffdf8bf77ffe0fffb3fc3ffffffffffffffc7fcffff6e1ffffff318b3fc3fffffffffffffffffef8c76e1fd9ffffc513fc3fffffffffffccfc7feffff6e1ffffe0fd8fffc3fffffdc63f40cfc50bffff8bfb7ffe0fffb3ffffffffffffffffffffeffff0e14ff4910bfb3fc7fa7ffffffffff27f0af8ff8a1fff4bfffffd0fffffffdf63ffffffffff8ff8a1b4efff33ffffc3fffffdc67fffffff0bffff8a1b7fffffc513fc7fffffdf63f48efffffffff0ffb7ffe00bffffc3fa3f8bffffffffc5fcffdffdeffffcdfffb3fffffffffffff43fffffefffffde77f286fc513fc3fffffff67f43ffc6feffdffff77f2bf27fb3fc3ffff8bfffffce2bffefffffdeffffc673ffffc7fa7f83f63ffffffffeffff0de77ffff0bfb3fffffffffffff43fffffcffff6ff6bf28d27fb3fffffff87ffff43f287ffffff6ff6bffcdfd8b3ffffffffdefff40dffffeffff6ff6992bf27fffffffa3f87fffffccfff0affff6ff699fc6fff13fcbfabf83fffffcd2bffeffff0fffd9fff098fffc7fabf8bfffffcc2450affffffffff4bfffffd0c3fffffdf6ff40dfc60ffffffffb7f2bf27ffffcbfabffffffffffffffcf2ffffffce2bf27fb10fffffffdeffffffffffeffc7fff4ff2bf245110cbfffffffffffcefc70effffffffff2bf27ffd0cbfa7ffffffffff27ffefffffff4ff4bffc5110ffffff87fffffceffffeffff0ff4ff4910bfb3fffffffffffff43fffffcffc7fffb4e286fff13ffffffffff6ff43ffc7fcfffffffb7f28d27fb3fc3fa3ffde6fffff2bffcfffffffb7ffff305ffffffabf87f63f4bffffffffff0ffb4efcdfffb3ffffffffdefff40effffefffffffb7f28627ffffcbfffffde67f47ffffffffff0ffb7f2bf0bffffcacfff81cfff47f2440bfaff6fffffffffd8fffc6dfff81c63f44c2450bffeafffffffffffffe8fffffffffffffcffc4ffffdf6deffffe0718fe8fffffffff63fffffffffffdf8bf4e949173ffd0fecffffff63ffffffffcffff89e74efffffffe8fffffffff63f48ffffffffff8bf769fe0ffffe8fffffffffffffff27ffff8eafe14ff4bffd8ffffefffffdcfffffffffffffc76e16bfffffff128cffffffdcfff4bffc4ffffea6e16bffe0ffffffc7fffffdc63f4ccfc50bffff8bffe9fe0ffffe8fffffffdc63ffff27ffff8ea8a14ff4bfffffd0c7fffffdd63ffffffffcf8ea8a1fcefff33ffffcffffffff6bfffffffffffff0e1fe9fc6085fe8cffffffff6bfffffff0bffff8bffffffffc5128fffffffdd63f48ffc5ffffff0fffe9fe00bffffcfffffffffff47ffffffffdf6de6bf2bffd8fe8cecfff83fffffff2bffffaff6defffffffd8ffffffffffffffffffffffcfadffde4ce48d33ffffffffff8bfffffcffc4fffadffdefe949173ffffc6cfff8bffff4bfffffcfffffde77ffffffffe8cffffffff6ff47ffff0ffffffff77f2bf27ffe8feffff83f63ffffffffffaff0de77fffffffffffffffffdefffffffc4ffffea6fffff29127ffd0ffffff87fffffff27ffffaff6fffff4bffc5110ffffff87fffffff244fffaff6fffff491fd8fffcbfffffdefff47ffffffffeafff6bf2bf27ffe8feffff87fffffff2bffffaff0ff6bffc60bfffffeffff87ffff4bffff0bffff6ffffffc6fff128feffff81effffff286fffaff0ff6bffff0bfffffeffff89c63ffcc245fffaffffffff491ffffffcffffffdd6bf44dfc60fffffffffff2bf27ffe8cedfff8bf6bf4cc27f0bfaffffffffffffc513ffecffffdeffffffffffcffeafff4ff4bf33ffd0fffffffffffffffffffff2c7fff4e92bf245110fffffffde6fffcffc4ffffeafff4ff2bf27fffffeffff87f6fffff27ffffafffff4ff4bffc5fffcbffffffffff4ffffffcf2ffffffff286fff128cbffffffffff4fffc4ffffeaffffff28d27ffe8ffffff87f6bffffffffcfaff0fffcefc6fc5fffcadffffffffffff2bf0cfaffffffffffffc513ffedfff87f63fffffc5fffaea0ffffffcdffffffffffffffffff4fffffffffff0fffe9286fc5128ffffffffffff4cffff0fffffffffe928627ffe8cbfffffff6bf47ffc6fff2ea0fffff2bf0bffe8ffffff87f6bffcf2bffffaff0fffe9fc6ffffffc2da3ffdc63f43f2450bffff8bfffffffffffffc2ca3f8ff63f43ffc4fcfffffff77ffffffffffc3fa3f83ffff40c2460bffff6fffffffffd8fffc2cfff85efff43f2c4ffffff6ffffffcdfd8fffc2da3f8dc6bf40c27f0bffc7ffffffffffff13fc6dfff81d63f44d2c5ffffff0ffffffff0bffffcbfa7f85d67f4ce2ffffffff0ffffffc60bfffffffa3ffffffffffffffcf8df6fffcefff318fffffffffffffff43ffc4fff2dffff6992a0fffffffffa3ffffffffffffffff8c76fffd9fff70513ffffa3ffffffffcf284fff8df6fffd9ffffd8ffffffa7ffffffffffffffff8df89efff4bf73ffd0feca3ffff63ffffffffff8df8bf74efcdfffffffffffffff67f43ffffffffff8bf77f28627f13ffffffffff67f43ffc4fff2dffff77f2a0ffffffc2fffffff67ffff2bffff8ff89e77fffffc5ffffefa7ffff63f48e285fff8ff0ff77ffffffffffc2fa3ffdcfff40c2470bffff6e1ffffe0fd8ffffffffffffffffffffffff2ff6e14d9291258fd0cffabffffffffff27ffff8ffffffd94bffd8fd0ffffffffffff43fffffcfffffe168e28dfd8fffc2cffffdfffffff2bffcf8ff6e1fffffffd8ffffffffffdffff40ffc4fffffffff6bf2a027fffffefa3ffdcffffffffffff8c76ff699fffffffffc6fabffdc63ffff27f0bf8ffffffff4bfffffd0c2da3ffdc6bffff27f0bf8ff8bffffffffc513fc6fffffdf63ffffffffff8ff0e14ff4bf0bffffc3fffffff6bf43ffc4fff2ff8bffce28d27ffffc6dabffdd63ffff2bffff8ff0fffcefff0bfffffffffffddfff43ffffffffc78a1fff28627f13fcffffffdd67f4cefc7ffffffffffff2a00bffffcffa7ffdd67ffff2bfffffff0e1ffffff085fffc3ffff8ffffffffffffcffff6de6bffc6fff13fc3ffff8fffffffffc4ffffdf6deffffcdfd8ffffeca3f83ffff43fffffff2ff6de6bf2bfffffffffffff8ffffffcffffffffff6defd9fc6705fffcffaff83fffffcd286ffffdf0deffffff098fffc7faff8bfffffcf2c50fffffffffff4bf73ffffc2fa3f83f6ff43ffc6fff2fffff77f2bfffffffc2ffff8bf6ff40f2ff0ffffffff77fffffff13fc6faff83f63f44dfc5ffffff0ff77ffffffffffc7fafffffffffff2ff0cffdffdefff4bf33ffd0fffa7ffffffffffffffff2c7fdefff286fff110cffa7f8bffffffffc4fff2dfffffff2bfffffd0fffffffffffffff2ffffffff0defff48608513fcffffffffffffff2ff0ffffffdefff4bf705fd0ffffff8ffffffff2c5ffffdf0defff4910bffd0c3fffffff6fffffffffcfffffde74efc6fc5ffffeffff8bf67f43fffffff2fffff77f286fff13fcfffff8ff67f4bffffffffff0de77fffffc5fffcffabf8ffffffcc2470bffffffffff4bffd8fd0fefa3f8dcfff40cfff0bffff6ff6bffc6fff13fcefabf81ffff44d2c6ffffff0ffffffff098ffffffffffffffffffffffcf2ff6ff4ce2bf27ffd0cbfffffffffffff2fffcffff6fffce4bf318fd0fffabf87fffffcfffffff2ff6fffd9291fffffffffffffffffffff2ffffffc70fffd94bf085fd0cbfafffffffffff27f0bffc76fffff4bffc5fd0fffffffffffffcf2c7ffffff0fffd9491098ffffecfff87ffff43fffffcf2fffff6bf28dffffffffffff85effffffffffcffc76ff6bffc630513ffefabf81efff44dffffff2fffff6bf2bf0bfffffffaff85efff48ffffffffff0fffd9fc60bffffc7fabffdf63ffff2ff0ffffffff4ff4bf33ffffcefafffdc6fffff27f0bffffffffff4bffc5fd0feffff8df63ffcf2c5ffffffffffff4910bffffc2da3f8bf6bf43ffc7fff2ffffffff28dffffffc2da3ffdd6bffff2ff0cfffffffffffff30513fc6dabf8dd63f4fffc5ffffff0fffcefcdfffffffeda3f89dfff40ffff0fffffffffff28627ffffcedabf83f6bf47ffc6fff2ff0fffff2bfffffffcacabffff6fffffffffcf2fffff4ff2bffffffffffffffde63ffff2fffcffff0ff4ce4bf0bfffffffffffde67ffffffffff2c70ff4ff2bf0bfffffefa7ffdefffffffff0ff2c7ffffff2bf27ffd0feffff87f67fffffc7fff2ff0fffff291fffffffffffffde67ffff2ffffffff0ff4ff486085ffffeda3fffffff43fffffcf2c7ffffce286fc5fffcbfaff87f6bfffffffffffff0fffcefc6085ffffffa7f87ffff4ffffffff2c70fffff2860bffff >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
private theorem boardOK (w : Fin 26) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
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
  | ⟨a+26,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 26) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 26) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 26) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 26) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 26) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 26) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 26) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 26) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 26) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 26) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 26) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 26) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 26) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 26) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 26) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 26) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 26) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 26) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 26) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 26) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 26) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 26) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 26) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 26) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 26) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 26) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 26) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 26) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 26) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 26) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 26) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 26) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 26) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 26) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 26) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
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
  obtain ⟨w,hw,on⟩ := member (List.range 26) full
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

private theorem baseGood (p : Fin 52) (a b : Fin 468)
    (cover : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ base, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  rcases List.mem_append.mp hw with raw | constants
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp raw
    have eq := congrArg (fun k : Nat => k.testBit j.val) cover
    simp only [Nat.testBit_and,Nat.testBit_or] at eq
    intro hp
    have yes : (pos p.val).testBit j.val = true := by simpa [input,p.isLt] using hp
    rw [yes,Bool.true_and,Bool.or_eq_true] at eq
    simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using eq
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at constants
    rcases constants with rfl | rfl <;> simp [good]

private theorem readGood {p a b : Nat} {s : List Column} (h : ∀ v ∈ s, good p a b v) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases e : s[j]? with
  | none => simp [good]
  | some v => exact h v (List.mem_of_getElem? e)

private theorem orGood (gs : List (Nat × Nat)) (s : List Column) {p a b : Nat}
    (h : ∀ v ∈ s, good p a b v) : ∀ v ∈ gs.foldl addOr s, good p a b v := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact h v old
    · obtain rfl := List.mem_singleton.mp last
      have hl := readGood h g.1
      have hr := readGood h g.2
      unfold good at *
      simp only [Bool.or_eq_true] at *
      tauto
end PEqualNP.Research.Plane975Family3Mask

open PEqualNP.Research.Plane975Family3Mask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Family3Mask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
    (tail : List Gate) (out : Nat),
    let s := ors.foldl addOr base
    let firstAnd := both (wire s left) (wire s right)
    let final := tail.foldl step (s ++ [firstAnd])
    (∀ p : Fin 52, firstAnd p.val = true → omittedFlags.testBit p.val = true) →
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro ors left right tail out
  dsimp only
  intro support hp hn
  apply separated_bound _ tail out _ hp hn
  refine ⟨idx,?_⟩
  intro i j lt
  obtain ⟨p,off,cover⟩ := retained i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact orGood ors base (baseGood p _ _ cover) w old
  · obtain rfl := List.mem_singleton.mp last
    intro on
    have no := support p on
    rw [off] at no
    contradiction
