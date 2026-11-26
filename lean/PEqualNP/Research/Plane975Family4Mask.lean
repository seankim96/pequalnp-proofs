import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975Family4Mask
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
def omittedFlags : Nat := 0xf000080f

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x1d1e873f9dcde672b8bc3e170781bfdf6f777badcee36fb5da6cf65b1d86b357a9d469f4da5d268f45a1d067f3197cb6532792c7637198bc56271187c2e0f0380b9dc2df6eb65aed368b3586c15eaed72b759ac55ead55aa54ea34ca55269147a35168942a0d027d3d9e4ee6d359a4ce653197cba572a92c92472290c823f1d8dc6a33118843e1d0d8642a110783416090280bf9fafa7cbe1eef67abd1e6f1783bddced763a9d2e872b89b8db6d361acd569b45a0c36130580be5e2ed74b95c2d568b258ac15eae56aad54a853a99409f4f271369a4ca2d14894421d0a8441a09027f3f1f4f6793c1d0e670379acc45f2f174b85b2d164b0562913c9c4b251248e46228ec502712888421e0d06430160a85026110803c180b050240e04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x3840218b804228380023832804283220448b204068320046830c041830804383060608304861030406183028640b02424830206483008650b00426830024702e0008a2c8001a2c080922c0009a2a8002a2a100a2aa040a82a000aa2900232288003aa84428828402982818282a8142a028102a22808292a8042a8262004a26080c2a6040c826000ca24a080a248081aa4448882440898a424848242084aa4048c824028d022a040a2290422228042a2228442222044a221848222104a222084c2a2040e822024e0210287020c0c1820b0c0220a0c0a2090c222082c30a064a082060e08a054a80a044a882042c902030e022028642a024a482018682a014aa02012ca0200a4d0a0068e01c801181c4001c1c2010c1c0011c98841281880138186020c184021c18303049824308182030c9814320181032498043281802134964000d162004c9604049960004d94c0019948811194841099480119944001d9424148142014c940c1419404149140215492c0409929042192840299280429126040c9250405924040d122044c9210425920406912024649104261110207490c841190c04199098501909412190905219088511908412910825301070604106060c905060590486111030704902c34090243481022544901c301901870190143211012524900c341100a5500e2000e0e100860e0008e0ca010a0c881120c8011a0c4009c0c301060c2010e0c101860c021940aa100a8a850280a8102a8a450880a4108c0a2100e0a100a68a050a80a030a4090303408a910288a510808a110a0889112888512808831308865208086120c884d280884528808430940830306882d30008293028825308881c380081838288143a008121a4880d380080b19088071a08644089864008d062004e8610087860c0c186080c386040c984c480984c081904b090284a490804a090a8494901849090384881138484909845488184508858444889044289404309068424948042294484149810412984040a1d084069c08381023030306482c500982c140902a940202a140a8298403829042382894038285029026140c824d081824508902434840223444821848302124a4820d0c1020b4c082070e00183830810786080e580800e1c0880c580900c3c1000b0d0280a590800a3d00809850380949210092d20008b51080879200070e048065a080063c048054a810052c84804d281004b4900032d04002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3ffffffffffffffffffc000000000000000000000000000000000000000000001ffff800000000000001fffffffffffffffe00000000000000000000000000000e0003fffe0000000000fffe000000000000ffffffffffe00000000000000000000001e000fff00000007800fffc000000007ff00000000ffffffe00000000000078008f007807fe000000007801ffc000003807fc000007f00000fffff00000000000004000000080000000000000180000000001000000000000600006000000118012100181c03e0008c001e07803fc0001c1c07e000003fe002ff002fff00040b8000600300010f802180888238181e000101800f800c180f00607807807f00213800004464c0663808b8203012000cf0246421c63c010380700c2203383870000002070001182893801300004481c5478828080011e04133260180c01393260029080248002a000520000082000290533080004846cc18040082a45801206aa2024044922a0080b14842a2258814240d50005112b2d58b29a5240b0ad24aa3c000100000008030841c0008002005010114008060840580000974006bc49caf600000000000000000000000000000000000003f7ffee1c0000007e7f3fec6cd90000000001fe007ffad00000000000000000000000000003fbff400003fedf950dfda0000000ff5f4eb000000037e9dbf2a8000000000000000003f4f42db55c381fe00bf80000007be00ff000000200fee80000007bfa0000000000000003508000000000000000000179fc1df0001f87fe3bc00fc1ffc01fc3f8000001fe03f00002dcfee660f8071f0000000000000000626370070ffbc01e3c0077c0001e38707e0000f0f19e00318000707c05e000e1800000000002e000668004e8000065da030fc6800317180343078000e1f1b00300031e1800c8000000c1409c0340054362b868814400c4205aa04361000e288021c401142008020841000004204040ffd6b6dc37fd5129a20ff65f7d5da109080b69fa35a101c762480d1a00e40400000000000000000000039d5d0a43ea01d2271f0ec04c0870005a8804d000054800000fdcb6e27f8703400000000000000003f7531602901a2b0408f810024000000000000000000000000002fe6f6d7f1874000000000037e3f8459eca0430284 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010002000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xffffff83f6ffffffc6fffaeafd7b7f57fff1fffffffff8bffd5fffffffffaffff2b69fc6ffffffffffff83f6d5ffffc6ffffffff2b69fffff1b3fffffffffffff4bffc7fffffffe1699fe0fffb30fffffffff67fffffc7ffffff8a14ff4bfff1b3ffffffffff67ffffffffff8c78a1b7fffffc5130fffffffff67f4bffc7fffffffe1b7ffe0ff1ff0fffabf83fffffffffffffbbf6d76bf57ffffff0fffabf83ffd5fffffffffbbf6f2fd9fffffffffffffff8bffffffffc7fffbbffd7fd6fd1ff1b3ffffffffffffffcdffffefffffd7b562bf27fff0fffabf83f6ff47f27ffffbbffd7fd6ffffffff0fffffffffffffceffffeffffff24ff29127fb3fffffff8bffd6fffffffffb87ff2fff4bffff13fffffff8bffd6fff247fffbbfff2fff4bffffb3fffffffffffd644dffffeffffff2b7f2bf27fffffffa7f8bffd54bfffffffbbfff2b7ffc6fffff0fffa7f83f65547f286fffbbfff2ffffffff1fffffffffffffff4fffc4ffffe68a1fe9920ff1ffffecfff83fffffffffffffaff6f26bf93ffffffffffffffffffffcdffffe7fe6972fe9fff271ffffecfff83f6bffff27ffffaff972ffffffff1fffffffffffffff4bffc4ff3feafe16bffe0ffffe8fffffffffffffff284ffffea8a1ffffcd331fe8ffffe4ffffffffffffff3fc78a1fe9ffffff128ffffe4fff6bffccfc4ff3feafe1ffffe0ff1ffffecfe483f6d5fcd284fffaffff2fe9fffff1fffffffe483ffd5fffffffffaea6f2fd9ffffd8ffffedfff8bffffffffffff3afffd7fff546fff13ffedfe583fffffff246ff3afffd7fff57fffffffffffe5ffffffffffc4ffffeaff2fff28d27ffffffffff8bfffffff2bffffac7ff2ffffc633f128ffffff8bfffffff284ffffeaff2ffffcd331fffffffe5fffffffcdfffff3feaff2fe92bf27fffffedfff8bffd5fccffffffaffff2fe9fc6fffffffffffffff656ffffc4fff8e6fe14ff4bfff1ffffffffffffffffcefc4fe7fe6fffffffe0271ff0fffa7fffffff4ffffffff8c7fe1fff93ffff130fffa7fffffff4ff244fff8e6fe1ffffffff1ff0ffffff8fffffffffc4ffffe66f2fd9fd1ffffd0fffaff83ffff47ffffffffe66f26bf93ffffff0ffffff8fffff4fffffffffff957fd6546fc5ff0fffaff83f6bfffffc6ffffe6957fd6fffff1fffffffff8fffd6ffffffffffff9724ff4bffff13fffffff8ff656ffffc4ffffff972fff491ffffffffffff8fffd64fffffffffff972fff906fff13ffffa7f83f65647ffc6ffffe6ff2fff93ffffffffecfe6ffffffffffffff38fffe14d94bfffffd0fecffffffffffff2bffcf8fffe16bffcd33fff0fecabfffffff48cfffff3ffffe16bffe0fffff0fecffffffffffcefffff3fff8bf4fffd1271ffffecfe6fff67ffff27ffff8ff8a14fffffff1fffffffffffffff4fffffffffff8a1fce28d271ff0fffabffff6bffff2bffff8fffe1fcefff331ff0ffffe6ffffff4cefc4ff3fffffffff2a027fffffeda64ffffffffffffff38c78a1fffffffffffffeda64fff65548e287fffffffe1ffffe0ff1ffffeea6483f65544d286ffffffff2fffffffffffffeefe683ffff47ffffff3fff6d76bf57fffffffffffff8fffffffffffffffff6f24ff48d318fffffffe68ffffffccfc4ff3fff6f2ffffd1fffffffecfff8fffff4bfffffcffffff26bffcd33fffffeeaa483ffd544dfffff3fff6f2fd9ffffffffffffaff8bf6ffffffffff3fc7fd74d6fc6fffffffeefff8bf6fffccfc7ff3ffffd7fd6fd1ffffffffffe5fffffffffffffcffc7fd7fff57f33f130fffae58bffff4ccffffffffffd7fff546fffff0fedaa683f6bf44dfc6ff3ffffd7fd6fffff1ffffecffffff6fffffffffcffffff24ce4bf331ffffecfff8bfffffcefffff3ffffff4fffd1271ffffeefe58bffd6ffffffffffc7ff2fff4bffff13ffffabf8bffff4fffc4ffffffff2fff28d271ffffffaff8bffd5ffffffffffc7ff2fcefc633fffffffabf8ff6954bf287ffffffff2fcefcd33fffffeda6683ffd644dfffff3fffffffff2bf27fffffeda648fffd548efffff3fffff2ffffc6ffffffcbffffffffffffffc6ffffe6fff6bf93ffd8b28c7ffff83fffffffffffffaff957b7f57fffffe8ffffff87ffffffffc5ffffe697f4e9fd1fffb3ffffffffff61747ffc5ffffe6fffb6993ffffb3fffffff87ffff4bfffffefaff6ff6bffc6fc5fe8cbffe4ffffffffffc6feffeaffffffffffd8b3fc7ffff8bfffffffffffefaeafd7ffffd1ffffd0c7ffe583ffff47fffffefafffd7fff57fffffe8ffffe5ffffffffffc5fcffeafff4ff4bf33fb3fcbfffffff6fffffffffefffffff4e94bffc5fd0ffffe5ffffd7fccfc5ffffeaffffff491fffb3ffffffffff6fffff2bfffffc7fffb4efff305128ffffffffffff4bffc5ffffeafffb4efcd33fb3fcbfffffff6ff48cffffffffffffb69fc6fc5fffc7ffe4fff61544dfc5feffeaffffe9ffffffb3fc3ffffffffff43ffc5fe7fe6fd7b56fe0ffffffc7ffffffffd6ffffffffffe6fe1fff4bffffb10c3ffffffffd6fffffffffffffe1b7f93ffc513fc3ffffffffd643ffc5fffffffe1b7f93ffffb3fc3ffff83ffffffffc6fffba6fd7fffffffd8ffffffa3ffffffffcdffffe7fe6ffffd9fff258b3fffffffffffd743fffffffb876ff699906fffffffffa3fffffd7fff246fffba6ffffffffffd8b3fc3fa3f83f63ffffffffffba6957fff57fffffffcbfffffff67ffffffffffb8797f4ffffffc5fd0fffa7f87ffffffffc5fffba6fffffffd1ffffffffffffffffff40effffe7fff97fb7f28627ffffffffff87f67f43f27ffffffffffb7f906fc5ffffffa7f83f61647ffc5fffba6fffb7f93fffffffc3ffffffffffffffc7fefffffd7fff560fd8b3fc3fffffffffffff2bffcfffffe168efff318b3fc3ffffffffd5fffffffeffc7fe1fd9ffffc5fffc3ffffffffd5fccfc7fefffffe1fd9ffffd8fffc7ffe6fffffffffffffeffff8974d64bfffffd0ffffffffffff43ffffffffff897b7f54d33fb3fc3ffe6fff63f40cffffefffffd7fff560ffffffc7ffe6ffffd6fffffffefffffe1fff4bffffb10fffffffff615fffffffcffff8a1b4efff33ffffc3ffe4fff655fffffffeffc78a1fffffffc5fffc7ffe4fff61548efc5fefffffe1ffffe0ffffffc3fa248bf67f40e2bffffbbffffb7fffffc5fffc7fa6483f61544d285fffffffffb7fffffffb3fc3fffffffffffcdffffeffff6d7fd6fff258fffc3ffe683fffffff246fffbbffd7fffffffd8fffffffffffffff43ffc7ffffff6ff6bf28d258b3ffffa3ffffffffff2bffffb876ff68efff33f13fffffff87fffffff287fffbbffff6bffcd318b3fc3ffe6ffffd7fcdffffeffffffffd92bf27fffffffa2487ffff40cffffffbbffff699fc6ffffffcbfaa483ffd5fcd286fffbbfffffffffffd8b3ffffffffffffffffffffffbbffd74ce48d33fb10c7fabf8bfffffccffffefbbffd7ffffd1ffffd0ffffff8bffff43fffffffffffd7b7f54d33ffffc3fffffff6fffcdffffefffffd7b56fff27fffffffabffff617fffffffffbbffff4ce4bf33ffd0fffffffffffffceffffeffc7fff4fffc6245fd0cbfa65fff67ffff27ffefffffff4ffffffc5fd0c7fa6687ffd6fcefc5fefffffffffffd1fffb3fffffe5ffffff43ffffffffc7fffb4e2bf27f13ffffffffff6d743ffc7fffffffffb4e2bf27fffffffa3ffff6fffff2bfffffc7fffb4efff305ffffffabf87f6154bf285fffffffffb4efcd33ffffffffe5ffffff40effffefffffffb7f28627ffffcbffe6fff65644dfc6feffffffffff2bf27ffffc6cffffffffffffffffe7fff8a14e9fffffffd0c7ffffffffffffffffffffe68a1fff90d33ffe8c6cfffffffff4ccffffe7ffffe1ffffe0ffffe8ffffff87ffffffffc4fe7ae66ffffffd1fd8ffffffffffffffffcdffffe7fe6fff6992bf27ffe8cacfffffffff47f244fe7fe6ffffffffffd8fe8c6dfff83fffffffffffe7afffd7fffffffffffffffffffff63ffffffffffae697f4ce4bf33fffffecfff87f63ffccfc4ffffe697ffe9fd1ffffffffffff87ffff4fffc4fffae697ffff90d33ffffc6dfff83f61744dfc5fe7ae697ffe9fffffffffcfffffffffffffffc4ffffeafe1fff4bffd8fd0cfffffffffd5fffffffffffffe1699fc6fc5128cfffffffffd54bffc4ffffeafe1ffffe0fd8fe8cffffffff6bfffffffffffc7897fff57ffc5fe8c7ffe7ffffff4fffc5ffffeafd7fff560ffffe8c7ffe7fff63fffffffffffea8a14ff4bfffffd0c7ffe4ffffffffffc4fcffeafe1ffffcd33ffffcffffffff695fffffffffffffe1fe9ffffc5fe8c7ffe4fff61548ffc5fffffffe1fe9fe0ffffe8c6ffe483f61544d285ffffeaffffe9ffffffffffffffffffffffcffffffffea6ff4d929127fffffeffff87fffffffffffffaff6ff4d9486fff13fffffe787fffffff244ffffea6fffff4bffd8fffffffe7ffffff44dfffffffeafff6992bf27fffffeffff87ffff4bfffffffafffff6bffc6fff13fcaffe483ffff47f286fffaeaffffffffffd8fffcfffff8bfffffffffffffafffd74ffffffc5fd0c6ffff8bffffffffc5fffafffd74fffd1ffffffffffff8bfffffcfffffffffffd7fd6fc6245fe8cfffff8bffff4ff27ffffafffd7fffffffc5fe8c6dfe783ffff47ffc5fffaeafd7fff57ffffffffecfe5fffffffffffffcffeafff4ff4bf33fffffffffffff6fffcfffffffffffff4e9fc624513ffffffffff6fffcffc4ffffeafff4e9fd127fffffefffffff6d7fff27ffffafffff4e9ffffc513fffffe5ffffff4ffffffcfac7ffffff2bf27f128cbffe5ffffff4fffc4fcffeaffffff2bf27ffffcadffffffffffff2bffcfac7fffffffff305fe8c6dfe487ffff4bf285fcffeafffffffcd33ffffffffff87ffd74cffffffffffffffe928627ffffcbffe7fff69744dfc6ffffffffffe92bf27ffffcadfe487f69548f2bffffac7ffffffffffc5fffc3fffffff6bffffffffe78c7fd7fd6ffffc5fffc2da3ffffffffccfc5fe7ffffd7fd6fe0ffffffc6ca7fffffd6fffffffe7ffffe1fff4bfffffd0fffa3fffffffffffc4fff8e6fe1fce90d33fffffffffffffffffceffffe7fc7fe1fff28627f13fc3fffffffffffcefc4fe7fe6fe1ffffe027ffffc2dfffffffd6fff27ffffffffe1fff93ffc513fc3ffff8ffffffffffffe7ffffd76bf546fc5fffc2efff83ffffffffc6ffffe6fd7fff57ffd8ffffffaffffffffffffffffffe6fff4ce4bf318fd0caeffffffffffffffffe7ffffff4d94bffc5110cbfafffffffffccfc4ffffe6ffffd9fd1fd8fd0feefffffffff43ffffffffc7fff6bf90633f13fffffffffffff43ffc4ffffe6fff6bf90d33fffffeca3ffffffffcdffffe7fe6ffffd9fff258ffffeefffffffd740cffffffffffff6bf906fff13ffffffffffffffffffffcffc7957fce57f30513fffffff8fffffffffc5ffffe6957fff54d33ffffc3ffff8ff6bffccffffe7fff957ffffc6fc5fffc6daff83f63ffcdfc5fe7ffffd7fffffffffffffffafffff63fffffffffffe697f4ce4bf33ffffcaeffffff67ffffffffe7ffffff4ffffffc5fffc6ea7f87f63ffcefc5ffffe6fffffffd1fffffffffa3ffff697ffffffffffc797ffce93f305ffffffaff87f6174fffc5ffffe6fffffffcd33ffffcada7f83f65644dfc6fe7ffffffffffff27ffffcada7f87f6564ceffffe7fc7ffffff906fff13fc2ca3fffffd540f284fffffffe1ffffe0fd8fffc6fa64fff61548e285fffffffe1ffffe0ffffffc3ffe7ffffff43fffffff8c7fd76bf57ffc5fffc2ffffffffff43f247fffffffd7fff560fd8ffffffffffffffffcfffffffffffe14d9fd1258fd0cffabffffffffff244fff8fffe1ffffd1fd8fd0fecfffffffff43fffffcfffffe16bf2bf27ffffc2cffffffffffff2bffcf8fffe16bffff33ffffffffffffffff40fffffffffffff6992a027ffffc2fa3fffffd5fffffffffffffe1fd9fc6fc513fc6fabffff63ffffffffff8fffd74d6fffffffd0fffffffffffffcffffffffc7897fd628627ffffc3fa27fff6bffff27fffffff897fd6ffffc5fffc6daa6fff63f4cffc5fffffffd7fd6fe0ffffffc6fa66fff616fffffffffffffe14ff4bfffffffc2cfe6fff6bffffffffcf8fffe1fff2bf27ffffc6daa4fff615fff2bffcfffffe1fcefff33ffffffffe7ffffd6fcefffffffc7fe1fff28627ffffcfffe6fff6564cefc7ffffffffffff2a027ffffceda64fff655fff2bffff8fffe1fffffffc5fffceeae483ffd544d286ffffffffffffffffd8fffceea648ff65548e2bfffffc7fffffffffffffffcfffff8fffffffffffffffc76d7fff486fc5fd0cfffff8fffffffffc7fffffffd7ffffd1fd8fffc3ffe78fffff43ffffffffff6d7fff546fc5fffceefe683ffff47ffc6fffffffd76bf57ffd8fffcacfe6fffffffffffffcfffffff4ff4bf318fd0feeae7ffffd7ffffffffffc7fff4d94bffff13fcbfaa687ffd7fcffc7ffffffffffd9fd1fd8fd0fecfe687ffff43fffffffffffff6bf28d27fffffeea24fffffffffffffcffc7fff68efff33ffffcaefe487ffff4bf287fffffffff6bffcd33fffffefaa683ffd744dfffffffffffffd92bf27fffffeeae487ffd548fffffffffffff699fc6fff13fc6effffffffffffffffcfffffd74ff4bf33ffd0cffaff8bf6fffffffffffffffd74ff4bffc5fd0c6eabf8ff63ffcffc5fffffffd7ffffd1ffffffc3ffe5fffffffffffffcffc7fd7fff57f33ffffc6dfe68fffff4fffc5fffffffd7ffffcd33fffffffa3f8bfffffcfffffffffffd7fd6fc6245fffcedaa683f6bf44dfc6fffffffd7fd6fff27ffffc6eaa6fff617fffffffffffffff4cefff33ffffcafa6687f656fcefc7fffffffffffffd127ffffcaea67fff656ffffffffffc7fff4ff4bffc5ffffeda25ffffd7ffffffffffc7ffffce2bf27ffffcadae4fff695fff2bffcffc7ffffcefff33fffffeda6787ffd64cefffffffffffffff28627ffff >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
end PEqualNP.Research.Plane975Family4Mask

open PEqualNP.Research.Plane975Family4Mask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Family4Mask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
