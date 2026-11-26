import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975Mask
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
def omittedFlags : Nat := 0x10100001103f3

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x1d3e97479fcde5f1f89c3e16f779bbdd6e771b7da6cf65b0d7ebb5bacd5e9f4ba4d1e8b3b9acc6572590c7637198ac461f0b83c0e02fb7cbdde6ed74b9dc6e16fb75b2d768b2d8ec561b057ebd5dae566b157ab54ea551a75369749a451e8b43a0d027f3e9dcea6f3699cca612b954a64d259248a411f8f476371a8cc622d1489446210e86c2a11078341205017fbe5eef67abd1e6f1773add4e974389c0dd6e35daad368b419aca643198ac3602f978bb5cad164af55aa950a753291449f4f27132974b255248f47235188a4321106823f9f8fa7b3c9e0ec73381bcdc6d3599cca622d968b2582b958a64f2712c9246229047e3e1d8e06632188c0582b150a4502611888421e0e06832180a8502612088401e0d0602c14090401c0a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x39002303880038384021838002383220448320246031020703082430308043830606083020648300a4503008650b00426830024702e0008a2c8001a2c0009a2a8002a2a100a22a000aa2980032291022229082122900232288003a281828228102a22808292a8042a8262004a2520842250085224a080a2442890242084a24080d2a4048c824028d022a040a228042a222044a221848222104a222084c2a2040e822024e021808322130a0221282422120a422108252a104a60210287020c2c1020c0c1820b0c0220a0c0a2090c222082c302060e082052c80204a4902048690a044a882042c9020386022030e022028642a024a48a014aa02012ca0200a4d0a0068e01c2010c1c021141c0011c190203419002341882130186020c184021c1830304182030c1812124980432818021349700045964000d960004d9540015950005594c00199480119944001d1422144940414914021549310025930006592c0409929042192804299250405924040d1222444122044c92104259204069120246491502059140215911022591082519104261110207490c041990985019090521908851190841291082530106060c9050605904861110325041022544901870190143211012524900c341100a5500e2000e0ca010a0c420940c4009c0c301060c2010e0c021940b210060b010260aa100a0a430840a2100e0a100a68a050a80a030a409810320943014093020609212060910226090303408a110a088911288851280883130086120c08430940830306882530888143a008121a4880d380080b19088071a087100078700047864008d062004e861008786040c98590803858801385808138540815052084685108078508053050285484c0819849810384909038488113848490984508858444889044289404309068424948042294484181830412984040a1d084069c083900238389003838102383100278309043030306482984038290423828940382850290263404026140c825048582450890243484022344402124a4020b4c082070e081c1811819082381890130183830016380481492118145a0101438140130a068125a4001238448114a21810d241810786000e3c0080c941180c580900c3c1000b0d0200a950280a590800a3d0080985030092d20008b51080879200072c040070e048065a080063c0480586818054a810052c84804d281004b49000387020032d04802d340002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3ffffffffffffffffff0000000000000000000000000000000000000000000001fffc000000000000007fffffffffffffe0000000000000000000000000000000f001fffc00000000003ffe00000000000ffffffffc00000000000000000000000000e001ff000000001c00ffe000000007f0000001fffffff00000000000000003004e00807f8000000000700fff00000207f80000fc000007ffff0000000000104000f030003f800000c02606007e00000303f00061fe0003f0007ffe00000004180a440418103f00001000c0e000fc004041078000e0f801c7803c00fff00001020000010000187e000605504c1841c01810403004084380003e11e07807fc002180000d45038320f082c0040180009833541916010200380018808e23c3c1f00000246000610148660050004a250c2b81010a02c4508c9324c2220481199cc600180128082850032880000000004509300000201804250149500890244a09da80020002020204004320020040041040500020086a08005210044204b910928bc1c4800008808185907542805011041194888a228b000404b8211f192645e4ab600000000000000000000000000000000003ef5fd380000001b3dddfb7ee6633900000001f601affcd74000000000000000000000000bdafea000036fdbb5f62506fd000000fd01ffbcc0000007fa07bfa800000000000000003bbc0006ef6d742c1b00ef00003e026f80bd000000f80e680001c17400000000000006d8001b548000000000000000000727c0b80000f8fe9c000f3f8000f1fc000000001fe00ff0001583c2e3e0007c3c00000000000000322e0027cb00071e001dc0000000f83871f0001cf273e00066000a8e83638011800000000a8580330c01600d800000e75e18fb50025c30c00d1c3800d872cb030023c661900000005aa0550140140005e7358b9154022e26813e847c8002b29026403154100e7220800005a80a04010078e5e84655c401488428d4ce8aa808a00d45405480d008a4000a8000022020000000000000000000001f7df9b8fbc81b25fdd7c391f0e82d4143b8134000691000007ffef67e7c380e00000000000000033765d840dbb9c247dc00608032001000000000000000000000003fd7f37df3340000000077edfc23ef30730cc101a04 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010000000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xfffffffff6fffcd2bffffafffff769fff731b3fffffff83ffd5fffffffffaea6f2fd9ffffd8b3ffffffffdc6ff44cfffffffeafffb5657fff1ffffffffffdc6d5fccfffffffffff2b69fffff1ffffffffffff67fffffff0bffff8a14ff4bfff1b3ffffffffff67f4bfffffeffff0ffb7ffe00b1ffffffffffff67f47fffffffb9f0ff77ffff0b1b3ffffffffffffffcd2bffffbbf0f2fd9fff098b3ffffabf83ffd5ffffff0bffff6f2fd9ffffd8b3ffffffffff6fffccffffffbbffd74d6fd1ff1fffffffff89c656fffffffffbbfff24ff491ff1b3ffffffffff67f47ffffffffff0f2b7f2bfff1b3ffffffffdf65647ffff0fffffff2b7f2bfff1ffffffa7f89c67f4bf2bf0bffffff2b7ffffff1fffffffff81f67f47f2bfffffff0ffb7ffff0b1ffffffffffff6bffccfff0a78ff8bffe9920ff1ffffecffffdcfff47fffffffae6ff26bf93ffd8fffffffff83f6bfffffff0bfaff972fe9fffff1ffffffffffdcfffffffffff38eafe1699fe0fd8ffffffffffff6bfffffffffffea8a1fcefcd331fffffffe4fff6bffccfff0b3fff8bffe9fffff1ffffecffffffffffcd2bfff3adf6ffffffff718ffffffffffff6ff4bfffffffafffde74efcdff1ffffffffffff6fffcdfffff3fdffff7692bf731ffffecffffff6fffcd2bffffafffff769fff731ffffecfe481cfffffffffff3aea6fffffffffd8ffffffffffff6bffffffffcf2eaff2fce28d331fffffffff89d695fff2bffffaeaff2fcefff331ffffecfe5fdd6bffcdfffff32eaffffe92bfff1ffffedfe489c695fcc2bfffffffff2fe9fffff1ffffecffffdc67fffffff0bf8e68bf4fffffff1ffffecffffff67ffffffffe7fff97f4fffd1731ffffecffffff67f47f2ffffffff97f77f93fff1ffffffffffffffffcc2fffe7fe6ff24d9491fd8ffffffffffff6bfffffffffffe60d7fd657f0b1fffffffff8dc67fffffff0bffff9724fffffff1ffffffa7f81d67ffffffffff2e6972ffffffff1ffffffa7f8dc6564ff2ff0bffff972ffffffff1fffffffff81d656fff2ffffffe60f2fff93f0b1ffffecffffffffffccfffff38ff6e14d9491fd8ffffecabfffffff48c2bfff38ffffffd9fe0fd8ffffecfe6fff67fffffff0b3fff8bf4fffffff1ffffffffffff6bffffffffff2ff8a1fce28d331ffffffabffff695fff2bffff8ff8a1fcefffff1fffffffe6fff67f4cefffff3fff8bffff2a0ff1ffffeda64fff67f48c2bf0b3fff8bfffffffff1ffffedfe4fff67ffce2bfff38ff0ffffffe00b1ffffffae4fffffffcdfffff3fdf6fffd9fff718ffffffafffff6fffffffffcffdffff4ce4bfff1ffffecffffff67fffffffff32dffff4ff291731ffffecfe5fff67ffce2ffff3ffffff4ff4bf731ffffeca65fff67f47ffffff3ffffff77f2bfff1ffffeea64fff67f48e2bf0f3ffffff77ffffff1ffffeefe4fff67f47ffffff3fff0ff77ffffff1fffffffe6ffffff47f2ffff3ffffff6bf57f098ffffeefe6ffffff47f2ff0b3ffffff6bf57ffd8ffffffffffdfffffff2fffcffff6f24ff48d318fffffffe68ffffffcc2ffff3fff6fffd9491fd8fffffffff8dffff4bffffffffff6f26bffcd318ffffeeffffdffd5fcd2bfffffffff2fd9fff098ffffeeffffff6fffccfffff3ffffff4d6fd1ff1ffffffffffff6bffff2ffffffff0fffce54d0b1fffffffe6fff6bffcdfffff32ff0fffd62bfff1ffffedabffff6bffcdfff0f32ffffffd6fffff1ffffffae5fff6bf4cc2ff0b3fffffffd6fffff1fffffffe6fff6bffcd2ffffffff0fffd657f0b1ffffffffffdf6fffffffffff2ffff24cefcd331ffffffffffdf6fffff2fffffffffff4ce4bf331ffffecfff89f67ffceffffff2ffff24fffffff1ffffeefe589c656fcc2ffffffffff24fffffff1ffffffaff89d6954bffff0fffffff2fcefffff1ffffffabf8ff695ffffffffffff0f2fcefffff1ffffedfe683f656fffffffff2ff0f2ffffffff1ffffedfe48dd655fce2bfffffff0f2ffffffff1fffffffff87f63fffffff0bfaff97ffe9fd1fffb3fffffffffffd7ffffffffffe60ffb6993f0bfb3fffffff83f61747ffff0bffff97ffe9ffffffb3fffffffffffd5fcdffffeffdf0de769fff0bfb3fc7ffffffffd5fcd2bf0fffffffffe9fff73fb3fcbfffffffffffcd2bffeffeaffffd9fff098b3fffffe5fffffffccfff0afaeafd7fff491fffb3fc7ffe5fdcfff47ffff0afaeafd7fff57ffffb3ffffffffdefffffffff0fffeafff4ce4bf33fb3fffffe5fff617fccfff0affffffffe94bffffb3ffffffffdeffffffffffffaea0ffb4efcd0bfb3fcbffe4fdc6d548cfff0bfffffffb69ffffffb3fffffe4fde63ffcdfffffffeafffb69fff0bfb3ffffffffffffffceffffe7fdffdefff92073fb3ffffffffff63fffffff0bffe6897b56560fffb3ffffffffdcfd6ffffff0bffe68a1b7f93ffffb3ffffffffffffffffffffe7b9f95775657f73fb3fffffff83ffd6fffffffffb9f95efff93ffffb3ffffffffffffffffffffffba66d76bf57ffd8b3fcbffffffffd7fccffffe7ba6ffffd993ffd8b3fffffff81c63fffffff0bfbbf957b7fffffffb3ffffffffdeffffffffffffba60ff4ff4910bfb3ffffa7f85c656ffffff0bfbbf97ffffffffffb3ffffa7ffdefd647ffffffffe60ffb7f93f0bfb3ffffffffffffffffffffff8df89e74efcd33fb3fffffe4fffffffceffffeffdf89e77ffe073fb3ffffffffffffffffffffff8ff6d7696560fd8b3ffffffffffffffffffffff8fffe168efcd318b3fffffffffffd5fccfff0affff6e1699fe0fd8b3ffffffffffffffffffffcf8ff897b4e54d33fb3fffffe6fff63ffccfff0affff8bfb5657ffffb3ffffffffdfffffceffffefffffe1fff4910bfb3fc7ffe6ffffd6ffffff0bffff8a1fff4bffffb3ffffffffdf615fffffffffffffe1b4efcd33fb3fffffe4fdc65548cfff0bffff8bfb7fffffffb3fc7fffffdffff48effffefffffe1ffffe00bfb3fffffffffffffffffff0cffdffd774e54d33fb3fffffe5fffffffcdfff0effdfffffd657f73fb3fffffff8bffd5ffffff0ffbbffdefcefcd33fb3fffffe5ffffd6fcdfff0effdffdefff2bf73fb3ffffa648bffd5fce2bf0ffbbffffffffff73fb3fc7fa6483fffffffffffefb9f0deffffff0bfb3fffffe683ffffffffff0afbbf6d7fff57ffd8b3fcbffe6fffffffffffffcffff6fffff28d318b3fcbffe487fffffff2bffcfbbf6ffffffcd318fffcbffe6ffffd7fcdffffeffffffffd92bffd8fffcbffe487ffd5fcc2bf0affff6fffd9ffffd8fffcbfabffffffffcd2bffeffffffffd9fff098b3fc7fabf8bfffffccfff0afbbffd7fff491fffb3fffffff89ffffffffff0ffbbffd7b7ffcd33fb3ffffaa581f6ff44dfff0ffffffffb562bffffb3ffffffffff617fffffffcfbbf0fffce48d0bfb3fffffe687fffffceffffeffff0fffff4910bfb3ffffabffde6d7ffffff0ffffffffb4e2bf33fb3fffffff85e6d54bf2bf0ffffffffb7ffff33fb3ffffabf87f63f4bfffffffbbf0fffcefcd0bfb3fcbfa6585e656fcefff0effffffffff2bffffb3fcbffe6fff65647ffffffffff0ffb7f2bffffb3ffecffffdc63ffffffffe7fe6fe14e9fffffffffcacffffffffffccffffe7affffffd9fd1fd8fffc7fffffddffffcdffffe7ae6fd7ffffff0bffffc6dfff81cfffffffff0bfae6957fffffffffffffecffffde63ffffffffffae697f4cefff33fffffecfff85c63ffccfffffffe697f4e9ffffffffffedffffdd617fcdffffe7fe60fffe9fff0bffffffffe7fff63ffffffffff8df8bf4e949173ffffffffe4fff63f48ffffffffdf8bf769fe0ffffffcffffffdcffffffffffff8eafe14ff491fd8fffc7fffffddffffcffffffffea0d7fff5600bffffffffe7fdc63fffffffffffea8a14ff4bfffffffc7ffe4fddfd5fffffffcffeafe1ffffff33ffffcffffffdc69548cfff0bffeafe1fe9fffffffffc7fffffddfd5fcffffffffeafe1fe9fff0bffffcfffff83ffd5fff2bffffafffdefd9ffffd8fffffffe7fff63f47fffffffadf0ff75657fffffffc6cfe5fffffffffffffcfadffde4ff4bfffffffffffe58bfffffcfffffffadffde4e949173ffffc6cfe48bffff4bfffffcfadffff77fffffffffffeffe483f615ffffffffffdf0defe9fffffffffcbffe787fffffffffffffaea6ff4d9491fd8fffcbffe781efff47fffffff2ea6ff6bf2bffd8fffcaffff85cfff4bf2bf0bfafffff6bfffffd8fffcafffffdeffffcd2bffffafffff6bffff098ffffeffe589cffffffffffffaeafd74ff4bfffffffc7ffe781dffffffffffffaea0d7ffffff0bfffffecfe5fdefffffffff0cffeafff4fffff33fffffeffe585c6d7fccfffffffeafff4e94bfffffffcadfff85dfff4bf2bf0ffaeafffffffff33fffffedfe485dffffffffffcfaea0ffffffff0bffffcbffe5fdd6974cffff0fffeaffffe92bfffffffffffe7fdd697fcdfffffffea0fffe92bf0bfffffedfe485d695fcf2bfffffeaffffe9fff0bfffffffffffffffffffffffcf8df89e74e90d33fffffeca7ffffffffceffffe78df8bf77ffe073ffffc6dffffdcfff4ccffffe78e6fd7fd6fe0ffffffc6ca7ffdcffffffffffff8e6fe14ff4bfffffffc7fffffddffffffffffcf8e6fe1fff90d33fffffeda7ffdcfd64ccffffff8e6fe1fff920fffffffffffffffffffff2ffffffdf6defce90d318ffffffffffffffffffffffe72df6defd92bf718ffffffffffffffffcd2fffe7fdffff69993f718ffffeeafffff63ffcdffffe7fdffff756fff73ffffc7fa7f8ffffffceffffe7fdf95effffd173fffffffaff8ff63ffffffffcffdf95e74efcdfffffffeca7f83f67ffffffffff2df95e77ffffffffffc6ea7f83f61644d2fffe7fdffdeffffff0bfffffeeafffdcfff47f2fffe7fe6fd76bf57ffd8fffcacffffffffffffffffcf2e6fff6bf28d318fffcacffffdeffffff2fffcffe6fff6bf93f318fffcacffffdefff44dffffe72ffffffd9ffffd8fffcaeafffdcfd7fcc2fffe7fffffffd9ffffd8fffc7faff8ddfffffffffffffe6957ffffcd33fffffedaff8dc6bffccfff0bffe6957fd6fffffffffc7fafffddffffcdffffe7fe6fd7ffffff0bfffffffafffde63fffffffffffe6fff4ce4bf33ffffcaea7f85c67ffccfff0bffe697f4ffffffffffffeea7ffdeffffce2fffe7fe6fff4fffff0bffffffffff85d6bf4ffffffff2e697ffce28d33fffffffaff85d6174ff2ffffffe60fffce93f0bffffcada7ffdd67ffcdffffe72e60ffffffff0bffffcada7ffddfd64ce2ffffffe6ffffff93f0bfffffffffffffffffffffffcf8df6de6bffcd318fffcffffffffffffffffffff2dffde6992a0718fffcfffffffffd5fcf2bffffffffdefd9fe0718fffc6cfe4fff63ffffffffcffdf8bf77fffffffffffffa67fff67ffffffffff2df8bf77f2bffffffffefa64fff63ffce2bffff8df0ff77fffffffffffffffffffffffffffffcf2ff6e16bf28d318ffffecffffdfffffff2bffff8ff6ff6bffcd318fffcecabffdfffffcfffffff2fffe16bf2a0fd8fffcefffffdcfd548c2bffffffffe1699ffffd8ffffffabffff63ffcfffffff8fffff4d6fd10bfffffefabffff63ffccfff0bffff8bf4d6fd1ffffffc6dfe6fff63f4ffffffcf8ff8bffff54dfffffffedfe7fff6bf4ccfff0bf8ff8bffd6560fffffffffabffff63f4cffffffffff0fffd65600bfffffefffffdf616fcefffffffff0e14fffd10bffffc6daa4fdd6154bfffffcf8ff0e1ffffcdffffffcffffffdd6564ceffffffffffe1fff2a00bffffceda7ffddfd548e2bffffffffe1ffffe00bffffcfffe783fffffff2ffffffdf6d7fff57f718fffffffe48fffffffffffffffdf6defcefcd318fffcfffe783fffffffffffff2df6defff2bffd8fffcffae483ffd5fcd2bffffffffdefd9ffffd8ffffffae7fff63fffffffffffdf0fffd64910bffffceffe5fff6ff47ffff0ff2dffff7562bffffffffeeae5fff6fffcf2ff0fffdfffffd657f73fffffffae7fff63f47ffffffffdf0fffd657f0bffffc6cae5fffffffffffffcffdffff4ce4bfffffffcffa65ffffd6fce2ff0fffdffdefff4bffffffffffa67ffffd6fff2ffffffdf0defff4bffffffffeeae48bf6ff4bfffffcffdffff74efffffffffcefa658bf656fffffffff2dffdefff2bfffffffceea648ff6554bffffffffdf0ff77ffffffffffcffffffdfffffff2fffffffffd74ff491098fffceffff81fffffffffffff2fffd76bfffffd8fffceefe78dcffffff2ff0bffff6d76bfffffd8fffcffffffdffff47f2fffffffffd76bf57f098fffcacfe6fffffffff2fffcfffffff4ff4bffd8fffcbfabf87fffffcfffffff2ff6fffd9291fd8fffcbfae7ffffd7fcc2ff0bffffffffd94bffd8fffcbffe6ffffd7fcf2ffffffffffffd94bf098fffcacfe687fffffffffffcf2ff6fffff2bffd8fffcaefe485efff4bf2bffcffff0ff6bfffffd8fffcafaa681efd744dffffff2ffffffd92bffd8fffcaeafffdefd548f2bfffffffffffd9fff098fffc7ffff8dfffffffffffcffff0d74fffcdffffffc6efff89ffffffffff0ffffffd74fffcd33ffffceeaff89c6fffccfff0bfffffd74d6fd1ffffffffffff8df63ffcffffffffff0d7fd6fd10bfffffedabf8bffff4ffffffcf2fffd7fff28dfffffffedfe589dfff4ff2ff0ffffffd7fff54d33ffffc7ffe68fffff4fffffffffff0d7fff54d0bffffcedfe589d6bf4cffff0ffffffd7fff2bfffffffcffaa683f6bf47fffffff2ff0d7fff2bfffffffcacabf87f6fffffffffff2fffff4cefcdfffffffeefe687f617fffffffcffff0fffff48dffffffcafa7f85e67ffcefff0ff2fffff4fffd1fffffffeffff85e67ffceffffff2ff0ff4fffd10bfffffeefe785e656fce2fffffffffff4fffd10bffffcadfe587f6974ffffffcf2ffffffff28dffffffcadae487f6954bffffffffff0fffcefcdffffffcada6787f6564fffffffffff0fffff2bfffffff >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
end PEqualNP.Research.Plane975Mask

open PEqualNP.Research.Plane975Mask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Mask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
