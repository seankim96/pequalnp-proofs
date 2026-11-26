import PEqualNP.Research.Plane888NineFlags

namespace PEqualNP.Research.Plane888ConflictGraph
open Plane888NineFlags

def partners : Array Nat := #[
  0x0, 0x1, 0x2, 0x3, 0x4, 0x5,
  0x6, 0x7, 0x8, 0x9, 0xa, 0xb,
  0xc, 0xd, 0xe, 0xf, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15, 0x17, 0x16,
  0x18, 0x19, 0x1a, 0x1b, 0x1d, 0x1c,
  0x1f, 0x1e, 0x20, 0x21, 0x22, 0x24,
  0x23, 0x25, 0x26, 0x27, 0x28, 0x29,
  0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
  0x3a, 0x31, 0x32, 0x33, 0x34, 0x35,
  0x36, 0x37, 0x38, 0x39, 0x30, 0x3b,
  0x3d, 0x3c, 0x44, 0x3f, 0x40, 0x42,
  0x41, 0x43, 0x3e, 0x45, 0x46, 0x48,
  0x47, 0x49, 0x55, 0x4b, 0x4d, 0x4c,
  0x4e, 0x4f, 0x51, 0x50, 0x52, 0x54,
  0x53, 0x4a, 0x56, 0x57, 0x58, 0x60,
  0x5a, 0x5b, 0x61, 0x5d, 0x5e, 0x5f,
  0x59, 0x5c, 0x62, 0x64, 0x63, 0x65,
  0x66, 0x67, 0x69, 0x68, 0x6a, 0x6b,
  0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x72,
  0x71, 0x73, 0x75, 0x74, 0x76, 0x77,
  0x78, 0x79, 0x7a, 0x7c, 0x7b, 0x7d,
  0x7e, 0x80, 0x7f, 0x81, 0x82, 0x83,
  0x84, 0x85, 0x86, 0x87, 0x88, 0x89,
  0x8a, 0x8b, 0x8c, 0x8d, 0x94, 0x90,
  0x8f, 0x91, 0x93, 0x92, 0x8e, 0x98,
  0x96, 0x97, 0x95, 0x99, 0x9a, 0x9b,
  0xa1, 0x9d, 0x9e, 0x9f, 0xa0, 0x9c,
  0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
  0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad,
  0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3,
  0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9,
  0xba, 0xbb, 0xbc, 0xbd, 0xbf, 0xbe,
  0xc0, 0xc1, 0xc2, 0xc3, 0xcb, 0xc5,
  0xcc, 0xc7, 0xc8, 0xc9, 0xca, 0xc4,
  0xc6, 0xce, 0xcd, 0xcf, 0xd0, 0xd1,
  0xd2, 0xd4, 0xd3, 0xd9, 0xd6, 0xd7,
  0xd8, 0xd5, 0xda, 0xdb, 0xdc, 0xde,
  0xdd, 0xdf, 0xe0, 0xe1, 0xe2, 0xe4,
  0xe3, 0xe6, 0xe5, 0xe7, 0xe8, 0xe9,
  0xea, 0xeb, 0xec, 0xed, 0xee, 0xf2,
  0xf0, 0xf1, 0xef, 0xf3, 0xf4, 0xf5,
  0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
  0xfc, 0xfd, 0xfe, 0xff, 0x100, 0x101,
  0x102, 0x103, 0x104, 0x105, 0x106, 0x107,
  0x109, 0x108, 0x10b, 0x10a, 0x10c, 0x10d,
  0x10e, 0x10f, 0x110, 0x111, 0x112, 0x113,
  0x114, 0x115, 0x116, 0x117, 0x118, 0x119,
  0x11a, 0x11c, 0x11b, 0x11d, 0x11e, 0x11f,
  0x120, 0x121, 0x122, 0x123, 0x124, 0x125,
  0x127, 0x126, 0x128, 0x129, 0x12a, 0x12b,
  0x12d, 0x12c, 0x12e, 0x12f, 0x130, 0x131,
  0x132, 0x133, 0x134, 0x135, 0x136, 0x138,
  0x137, 0x139, 0x13a, 0x13b, 0x13c, 0x13d,
  0x13e, 0x13f, 0x140, 0x141, 0x142, 0x143,
  0x144, 0x145, 0x146, 0x147, 0x148, 0x149,
  0x14a, 0x14b, 0x14c, 0x14d, 0x14e, 0x14f,
  0x150, 0x151, 0x152, 0x153, 0x154, 0x155,
  0x156, 0x157, 0x158, 0x159, 0x15a, 0x167,
  0x15c, 0x15d, 0x16a, 0x15f, 0x160, 0x161,
  0x162, 0x163, 0x164, 0x165, 0x166, 0x15b,
  0x168, 0x169, 0x15e, 0x16b, 0x16d, 0x16c,
  0x172, 0x16f, 0x170, 0x171, 0x16e, 0x173,
  0x174, 0x175, 0x176, 0x177, 0x178, 0x179,
  0x17a, 0x17b, 0x17c, 0x17e, 0x17d, 0x17f,
  0x180, 0x181, 0x182, 0x184, 0x183, 0x186,
  0x185, 0x187, 0x188, 0x189, 0x18a, 0x18b,
  0x18c, 0x18d, 0x18e, 0x18f, 0x191, 0x190,
  0x192, 0x193, 0x194, 0x195, 0x196, 0x199,
  0x198, 0x197, 0x19b, 0x19a, 0x19c, 0x19d,
  0x19e, 0x19f, 0x1a0, 0x1a1, 0x1a2, 0x1a3,
  0x1aa, 0x1a5, 0x1a6, 0x1a7, 0x1a8, 0x1a9,
  0x1a4, 0x1ab, 0x1ac, 0x1ad, 0x1ae, 0x1af,
  0x1b0, 0x1b1, 0x1b2, 0x1b3, 0x1b6, 0x1b5,
  0x1b4, 0x1b7, 0x1b8, 0x1b9, 0x1ba, 0x1bb,
  0x1bc, 0x1bd, 0x1be, 0x1bf, 0x1c0, 0x1c1,
  0x1c2, 0x1c3, 0x1c4, 0x1c5, 0x1c6, 0x1c7,
  0x1c8, 0x1c9, 0x1ca, 0x1cb, 0x1cc, 0x1cd,
  0x1ce, 0x1cf, 0x1d0, 0x1d1, 0x1d2, 0x1d3]

def mate (i : Fin 468) : Fin 468 := ⟨partners[i.val]! % 468,Nat.mod_lt _ (by decide)⟩

private def positiveWords : Array Nat := #[
  0xc002001, 0x10002002, 0x2008, 0x2200, 0x8004002, 0x8004004,
  0x8004010, 0x8004400, 0x8004, 0x8008, 0x8020, 0x8800,
  0x10008, 0x10010, 0x10040, 0x11000, 0x8020001, 0x20010,
  0x20020, 0x20080, 0x20040002, 0x40020, 0x40040, 0x40100,
  0x80004, 0x80040, 0x80080, 0x80200, 0x100008, 0x100080,
  0x100100, 0x100400, 0x200010, 0x200100, 0x200200, 0x200800,
  0x400020, 0x400200, 0x400400, 0x401000, 0x8800001, 0x800040,
  0x800400, 0x800800, 0x1000002, 0x1000080, 0x1000800, 0x1001000,
  0xa000001, 0x2000004, 0x2000100, 0x2001000]

private def negativeWords : Array Nat := #[
  0x800f1c0, 0x80169a0, 0x801c381, 0x8027940, 0x2b540, 0x802d340,
  0x802f140, 0x32d04, 0x38702, 0x4b490, 0x804d281, 0x52c84,
  0x8054a81, 0x8058681, 0x805c281, 0x63c04, 0x8065a08, 0x70e04,
  0x72c04, 0x8087920, 0x8b510, 0x92d20, 0x8094921, 0x8096920,
  0x8098503, 0xa3d00, 0x80a5908, 0x80a7900, 0xa9502, 0xab500,
  0xb0d02, 0xb2d00, 0xb8502, 0xc3c10, 0x80c5809, 0x80c9411,
  0xcb410, 0xe1c08, 0xe3c00, 0x80e5808, 0x8107860, 0x810d241,
  0x8114a21, 0x123844, 0x8125a40, 0x8127840, 0x129242, 0x812d240,
  0x130a06, 0x143814, 0x8145a01, 0x8149211, 0x814d201, 0x8150a05,
  0x8154a01, 0x161a04, 0x163804, 0x8165a00, 0x170a04, 0x183830,
  0x8185821, 0x8187820, 0x8189013, 0x8190823, 0x8194821, 0x81c1811,
  0x1c3810, 0x81c5801, 0x81c9011, 0x82070e0, 0x20b4c0, 0x820d0c1,
  0x820f0c0, 0x2124a4, 0x8218483, 0x223444, 0x229442, 0x22b440,
  0x243484, 0x8245089, 0x8249481, 0x24b480, 0x824d081, 0x8250485,
  0x252484, 0x8258481, 0x26140c, 0x263404, 0x8285029, 0x8289403,
  0x8290423, 0x8298403, 0x2a140a, 0x2a9402, 0x82c1409, 0x82c5009,
  0x82c9401, 0x2e1408, 0x303064, 0x8305061, 0x8307060, 0x8309043,
  0x830d041, 0x8310027, 0x321046, 0x323044, 0x329042, 0x8381023,
  0x8385021, 0x8389003, 0x8390023, 0x84069c0, 0x40a1d0, 0x840c1c1,
  0x840e1c0, 0x412984, 0x8414981, 0x8416980, 0x8418183, 0x841c181,
  0x422944, 0x8424948, 0x8426940, 0x430906, 0x432904, 0x442894,
  0x8444889, 0x8450885, 0x452884, 0x8454881, 0x8484909, 0x8488113,
  0x8490903, 0x8494901, 0x8498103, 0x4a090a, 0x84a4908, 0x4b0902,
  0x84c0819, 0x84c4809, 0x502854, 0x8508053, 0x8510807, 0x520846,
  0x522844, 0x530806, 0x8540815, 0x542814, 0x8550805, 0x8580813,
  0x8588013, 0x8590803, 0x85c0811, 0x86040c9, 0x86080c3, 0x860c0c1,
  0x8610087, 0x8618083, 0x62004e, 0x864008d, 0x8644089, 0x8650085,
  0x8700047, 0x8708043, 0x8710007, 0x720046, 0x88071a0, 0x80b190,
  0x880d380, 0x880f180, 0x8121a4, 0x88143a0, 0x88161a0, 0x818382,
  0x881c380, 0x8825308, 0x829302, 0x882d300, 0x830306, 0x838302,
  0x843094, 0x8845288, 0x849290, 0x84b090, 0x884d280, 0x86120c,
  0x8865208, 0x883130, 0x8885128, 0x8887120, 0x889112, 0x88b110,
  0x8a110a, 0x88a5108, 0x8a9102, 0x903034, 0x909212, 0x910226,
  0x921206, 0x929202, 0x930206, 0x941214, 0x943014, 0x949210,
  0x961204, 0x981032, 0x983030, 0x989012, 0xa030a4, 0x8a050a8,
  0x8a070a0, 0xa100a6, 0xa120a4, 0xa2100e, 0xa4108c, 0xa43084,
  0x8a45088, 0xa6100c, 0xa8102a, 0x8a85028, 0xaa100a, 0xb01026,
  0xb03024, 0xb10026, 0xb21006, 0xb81022, 0xc02194, 0xc08192,
  0xc0a190, 0xc10186, 0xc12184, 0xc18182, 0xc2010e, 0xc30106,
  0xc4009c, 0xc42094, 0xc8011a, 0xc88112, 0xca010a, 0xe0008e,
  0xe10086, 0xe2000e, 0xe4008c, 0x100a550, 0x900c341, 0x1012524,
  0x9014321, 0x9018701, 0x901c301, 0x1022544, 0x9024348, 0x1028740,
  0x102a540, 0x902c340, 0x1030704, 0x1032504, 0x1038700, 0x9048611,
  0x9050605, 0x9058601, 0x106060c, 0x1070604, 0x1082530, 0x9084129,
  0x9088511, 0x108a510, 0x9090521, 0x1092520, 0x9094121, 0x9098501,
  0x90c0419, 0x90c8411, 0x1102074, 0x9104261, 0x9108251, 0x910c241,
  0x9110225, 0x9114221, 0x9140215, 0x9148211, 0x9150205, 0x1202464,
  0x9204069, 0x9210425, 0x1212424, 0x122044c, 0x1222444, 0x924040d,
  0x9250405, 0x126040c, 0x9280429, 0x9284029, 0x9290421, 0x92c0409,
  0x9300065, 0x1302064, 0x9304061, 0x9310025, 0x1402154, 0x9404149,
  0x9408151, 0x140a150, 0x940c141, 0x142014c, 0x1422144, 0x9424148,
  0x944001d, 0x9480119, 0x9484109, 0x9488111, 0x94c0019, 0x9500055,
  0x1502054, 0x9508051, 0x9540015, 0x960004d, 0x9604049, 0x162004c,
  0x964000d, 0x9700045, 0x1802134, 0x9804328, 0x1810324, 0x1812124,
  0x9814320, 0x182030c, 0x9824308, 0x1830304, 0x184021c, 0x186020c,
  0x1880138, 0x1882130, 0x9884128, 0x1900234, 0x1902034, 0x1910224,
  0x1940214, 0x1c0011c, 0x1c02114, 0x1c2010c, 0x1c4001c, 0x1c80118,
  0xa0068e0, 0x200a4d0, 0x2012ca0, 0xa014aa0, 0xa0168a0, 0x2018682,
  0xa024a48, 0x2028642, 0x2030e02, 0x2038602, 0x2042c90, 0xa044a88,
  0x2048690, 0x204a490, 0x2050e80, 0x2052c80, 0xa054a80, 0x2058680,
  0x2060e08, 0xa064a08, 0x2070e00, 0x2082c30, 0x2090c22, 0x2092c20,
  0x20a0c0a, 0x20b0c02, 0x20c0c18, 0x20c2c10, 0x20e0c08, 0x2102870,
  0xa104a60, 0xa106860, 0x2108252, 0x2110a22, 0xa114a20, 0x2120a42,
  0xa124a40, 0x2128242, 0x2130a02, 0x2180832, 0x2182830, 0x2190822,
  0x22024e0, 0xa2040e8, 0xa2060e0, 0x22084c2, 0x220a4c0, 0x22104a2,
  0x22124a0, 0x2218482, 0x222044a, 0x2228442, 0x228042a, 0x2290422,
  0x22a040a, 0x24028d0, 0xa4048c8, 0xa4068c0, 0x24080d2, 0x240a0d0,
  0x242084a, 0xa424848, 0x2440898, 0x2442890, 0xa444888, 0x248081a,
  0x24a080a, 0x24c0818, 0x2500852, 0x2502850, 0x2508052, 0x2520842,
  0x2580812, 0x26000ca, 0xa6040c8, 0x26080c2, 0x262004a, 0xa8042a8,
  0x2808292, 0x28102a2, 0xa8142a0, 0x2818282, 0x2840298, 0xa844288,
  0x2848290, 0x288003a, 0x2900232, 0x2908212, 0x2910222, 0x2980032,
  0x2a000aa, 0xaa040a8, 0x2a100a2, 0x2a8002a, 0x2c0009a, 0x2c08092,
  0x2c40098, 0x2c8001a, 0x2e0008a, 0x3002470, 0xb004268, 0x3008650,
  0x300a450, 0x3020648, 0xb024248, 0x3028640, 0x3040618, 0x3048610,
  0x3060608, 0x3080438, 0x3082430, 0x30c0418, 0x3100270, 0x3102070,
  0xb104260, 0x3108250, 0x3200468, 0x3202460, 0xb204068, 0x3220448,
  0x3280428, 0x3800238, 0xb804228, 0x3840218, 0x3880038, 0x3900230]

private def boards : Array Nat := #[
  0xdefc5b7d8dfef58e01d00000000000000000001fbff46c7ec0d278e9cf2d849bd07c060c01407404, 0x1bdf8b6f5851fa8bac0d000e800000000000000000000000003f3abb428a1f5400d203c74e2e2d808406da03e001400c001400151000100, 0x1fe3aded8586c3fb510034c2278f65e2f9176802140436d01fd001b908038400d84a0005a3080000068880, 0x7f42d65db0b0d83dc550200054302103a1762785e882ea40040900406d5001f62000316208001c2000d8442000002d1408000000000a404010000, 0xe82fb1af0bd105eb32000604b080d00b76d0107ec340000c5c34200083c1c0000ee18c8d00080016c34082001000000000016480a001a00100200, 0xdddd8060fd86800000c67e1b838000740fc1f000003dc1e331cc000600002ec1f602838001c40000000000000589c05000221b800050000e80002,
  0x3fc0fe000007bc0fe31f0e78000030c00000bb83fdc0660f00003e180000000000000000002c4e01b0000707877c000039e00000fb0000000079, 0x17707fb8073e0ff000000ff0fc00000000000000000000000058cfc01df000001f07fc3be000003e0ff8000003fc7e00000000000007e07, 0x2e1cff003bfc0000003fc1fff873fc00000007f80fffc0000003fc1fff80000000000000000001fff801ff, 0xb8347ec0077f8000000001fd007d6fa01a3f60000000001fe003f6dd0000000001bf0076fe90000000000000000000000000006fdd60000037524, 0x6c3fba00000000001ff90007fdbde980000000000037fa00ef7fdaa80000000000000000000000000000000000037efb7e400000007bf336ab90, 0x6ffce000f7bfff7357400000000000000000000000000000000000000000000001bfdfb7ff3880000000000fbfe73de6ceef988a,
  0x37fe7fedffff383c00000000000003f7ff3c7f9fe7b9efbfe3e198679, 0x890120000000822a055402a282905c448090101248052010a409228085440954408a89016c000091001352d821400926b6429022952aabc8adb, 0x11100440202490048c006053002421640105210124908042a108025500000090600023522db410a00092646b69058810481a93254b7840cc9546f, 0x20298202492100302980840008ca880000002207000008ca30b3998209800008894c1cb63882c40204800c724612a2735d04018c21931106775, 0x440e0000008e09180b4f0cf00809c0000021119303c2dc1e102e080180120000c7c123092427398f840800c38060184610401c1e67986, 0x2004e0000004210c13001e04c700f00802e02003800260000031fe024301122011c7060f8020400383801f00070230c038000781f8e1fe0781f8,
  0x200270040070002700000000707ff001103004444002381c0c03e00040c0003c01e0007f00003811c0c03e0000003c0ffc01e07fe00fe0007fe00, 0x440380088880043801c00e007f80000201c000078003c0000ffc0000070021c00e007f800000001e00ffc00007803ff00001ff80000fffff80000, 0x803c00000f0007c000000fff800000001e000878003c001ff000000000003e000fff80000003c01fff00000007ffc0000001fffffff0000000000, 0x7c00010f000780001fff0000000000000000f80003fffe00000000078003ffff00000000003ffe00000000007fffffffffe00000000000000000, 0x1f00007ffffe00000000000003e0000fffffc00000000000007fffc000000000000003fffffffffffff8000000000000000000000000000, 0xf800001fffff80000000000000000003fffff00000000000000000007ffffffffffffffffffc00000000000000000000000000000000000000000,
  0xffffffe0000000000000000000000003ffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

private def mins : Array Nat := #[
  0x8000001, 0x2, 0x4, 0x8, 0x10, 0x20,
  0x40, 0x80, 0x100, 0x200, 0x400, 0x800,
  0x1000, 0x2000, 0x8004000, 0x8000, 0x10000, 0x20000,
  0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000,
  0x1000000, 0x2000000]

private def packed : Array Nat := #[
  0xfeda6787ffd64fffffffffff0fffff286fff13f, 0xcadae4fff695ffffffffffff0fffceffffc513f, 0xfeda25fddfd7ffffff0fffffffffce2bf27f13f, 0xcbfa67fde67ffff2ffffffc7ffffff4bf0bffd0, 0xcafa7f87f67fffffc7fff2ff0ffffffd1ffffd0, 0xfefa7ffdeffffcefff0ffffffffffffc627f110,
  0xfffa67fdeffffffffffff2c70ff4fffff0bffd0, 0xc6eaa6fff617ffffffffffff0fffce4bfffffd0, 0xcacabffde6ffffffff0ffffffff4cefff248fd0, 0xcffabf83f6bfffffc6ffffff0d7fd6ffffc8fff, 0xfeda3f89dffffcffff0fffffffffd6fc627f13f, 0xc7ffe68ddfff4ff23fffffff0fffff54d0bffff,
  0xc2dfe5fddffffff2ff0fffffffffff57f30513f, 0xc2dfff8bf6bf43ffc7fffffffd7ffffcdfc8fff, 0xfffa3f89dfffffffff0cf2c7fd7ffffff27f13f, 0xc7fabf8df63ffcffffffffffffffd6fd10bffd0, 0xceeafffdc6ffffffff0bffffffffd6ffffc5110, 0xc6eabffdfffffff23f0ffffffd7ffffff33ffd0,
  0xfffabf8df63ffffffffcffff0d74cefffffffd0, 0xfeeafffdefd548ffffffffffffffd9fc60bf13f, 0xcafaa681efd744dfc6ffffffffffd9ffffc8fff, 0xcaefe485efff4bf287fffffffffffffcdfd8fff, 0xfeea24fdefd5fffffffcffc7fff68effffff13f, 0xfeeae4fdefd5fffffffcffc7fff68effffff13f,
  0xc2cfe687ffff43ffc4fffffffff6bf28dfc8fff, 0xcbfabfffffd7fcf2c7ffffffffffd9fd10bffd0, 0xfeeae7ffffd7ffffff0bffff6fffff4bffff110, 0xfffaffffffd7fcffffffffc7ffffd94bf0bf110, 0xfffabf87ffd7fcfffffff2ffffffd9fd127ffd0, 0xfffabf87ffd7fcfffffff2ffffffd9fd10bffd0,
  0xcbfaa6ffffd7fff2fffcffffffffce4bffd8fd0, 0xcbfaa6ffffd7fff2fffcffffffffce4bffd8fd0, 0xfecabf87ffd7fffffffcf2ff6fffce2bfffffd0, 0xcffffffdffff47f2c6fffffffd7fff57f098fff, 0xfeefe78dcfff43ffff0bffff6fffff546fff13f, 0xc2ffff81ffffffffc6fff2fffd76bfffffc8fff,
  0xceffff81ffffffffc6fff2fffd76bfffffc8fff, 0xcffaa68fffffffffc70bffff6d7ffffffffffd0, 0xfffabffffffffcf2c7fffffffd7fd6fd1098fd0, 0xffffe78fffffffffff0bffc76d7ffffc6fff110, 0xceefff8ff6554bffffffffff0defffffffc513f, 0xfeffff8bffd640efff0ffffffff77f28627f13f,
  0xc2effffff6d5fff2bf0ffffffff74efff30513f, 0xc7fa678fffd6ffffc5ffffdf0ffffffd1ffffd0, 0xcfffffffffd6fce2ff0ffffffffffffff705110, 0xfffa67ffffd6fff2ffffffc70defff4bffc5fd0, 0xcffa7f8bfffffcefc40ffffffdeffffd1248fd0, 0xfeffffffffd6fcefff0ff2fffdeffffc627f110,
  0xc7fae5fffffffff23f0cffdfffffff4bf33ffd0, 0xfffae7fff63f44d23fffffff0ff75657f0bffff, 0xfeeffffff6ff40f2ff0fffffffffff57f70513f, 0xc2fa25fff6ffffffc6ffffdfffffd6ffffc8fff, 0xfffffffff6ff40ffff0ff2fffff756fc627f13f, 0xfeefe5ffffff43f2050ffffffff77f54d33ffff,
  0xfffffffff6ff43f2ff0cfffffff77f57f30513f, 0xfffafffffffffcf2050fffffffffd6fd173ffd0, 0xfffae7ffffffffffc5ffffdf0fffd6491ffffd0, 0xfffffffffffffcf2ff0fffffffffd6fc6705110, 0xc7fae5fffffffff23f0cffdfffffff4bf33ffd0, 0xcffae483ffd5fcd286ffffdfffffffffffd8fff,
  0xfffa3f8fffd5fcfffffffffffdefd9fc673f13f, 0xfffaff8fffd5fcfffffffffffdefd9fc60bf13f, 0xc3fa2783ffffffffc4fff2df6fffffffffc8fff, 0xc3ffe48ffffffff284ffffdffffffffcd318fff, 0xc3ffff8fffd5fffffffcffff6defceffffc513f, 0xc3ffe7fffffffff2c6ffffdfffffff57f718fff,
  0xcfffe7fffffffff2c6ffffdfffffff57f098fff, 0xfeefffffffff40f2ffffffff6ff6bf54673f13f, 0xc3fa2783ffffffffc6fff2df6fffffffffc8fff, 0xceda7ffddfd5fff2bffffffffe1ffffff08513f, 0xcfffe6fdd6564cefc7fffffffffffffe0fc8fff, 0xffffe7fddfd643ffffffffc7fe1fff286fff13f,
  0xffffe7fddfd64fffffffffc7fe1fff286fff13f, 0xc6daa4fdd615fff23ffff8fffe1fcefff0bffff, 0xc3ffe6fff6bf43ffc4fcffff8bffff28dfc8fff, 0xc6fa7ffdffd6fff23ffff8ffffffff4bf0bffd0, 0xceca7ffdf67ffffffffff2fffe14ffffffc8fd0, 0xcefa7ffdf67ffffffffff2fffe14ffffffc8fd0,
  0xfffabffddfff4cf23ffff8ffffffff5600bffff, 0xfeda27fff6bffff27f0bffff8bffff57ffc513f, 0xfffffffff6bf40ffc7ffffffffffd6fe0248fff, 0xfffffffff6bf4cffc7ffffffffffd6fe0088fff, 0xfeda3ffff6bffcfffffff2c78bffd6fff27f13f, 0xfedfe6ffffff43f23ffcf8ffffffff54d33ffff,
  0xfedfe6ffffff4ff23ffcf8ffffffff54d0bffff, 0xc3ffe6fff6bf43ffc7fcffff8bffff28dfc8fff, 0xfefaa6fff63fffffff0bffff8bf4d6fffffffd0, 0xfefabffffffffff23ffff8fffff4d64bf0bffd0, 0xfefa24fdcfd5ffffff0bffff6e1fd9ffffff13f, 0xc3fffffdffff40ffc4fffffffff6bffe0248fff,
  0xc2cffffdffff43f284fffffffe1ffffcd318fff, 0xfecffffdffff43ffc4fcfffffe16bf28dfc8fff, 0xcffaa6fffffffff27f0bf8ff6fffff4bffd8fd0, 0xfffabffffffffcfffffff2fffe14d9fd1248fd0, 0xc2ffffffffff40c247ffffffffffff560fd8fff, 0xffffe7ffffff43f27f0bf8c76ff6bf57ffff13f,
  0xc3fffffdffff40ffc7fffffffff6bffe0248fff, 0xcffaa6fffffffff27f0bf8ff6fffff4bffd8fd0, 0xfefa64fff63f48e205fff8fffff77ffe00bffff, 0xfefffffff655fff2bffff8fffde77fffffc513f, 0xfefffffff655fff2bffff8fffde77fffffc513f, 0xffffe7fff67f40efc4ffffdffffffffe0248fff,
  0xffffe7ffffd643ffffffffff89e77f286fff13f, 0xfeca24fff63ffff23ffff8dfffffcefff33ffff, 0xfffa67fffffffff204fff8dfffffff491ffffd0, 0xfffa67fffffffff205fff8dfffffff491ffffd0, 0xfffa67ffffffffffc4fff2df8bfffffd1fc8fd0, 0xc3fa3ffffffffcf284ffffdffffffffe0718fff,
  0xfffa3fffffd5fcfffffff8fffdefd9fc673f13f, 0xffffffffffff40ffc4ffffdfffffd92a0248fff, 0xc3fffffffffffff284fcf8dffffffffcd318fff, 0xcadfffffffd64ce2ffffffffffffff93f08513f, 0xcada7f81d67ffcdfc6ffffe6ffffffffffc8fff, 0xfedfff87ffd640effffe72ffffffff286fff13f,
  0xfedfff87ffd64ceffffe72ffffffff286fff13f, 0xfffaff85d6174ff205ffffffffffff90d0bffff, 0xfffffffff69743f2ffffffffffffce93ffc513f, 0xfffffffff6974ff2ffffffffffffce93ffc513f, 0xfffa3f87f6bf43ffc4ffffe6ffffff28dfc8fff, 0xfffa3ffff69743fffffff2ff97ffce286fff13f,
  0xc6ea7ffdeffffcefc5ffffe6fffffffd10bffd0, 0xcaeffffff656ffffff0bffff97ffff4bffff110, 0xfffa7ffdeffffce2fffe7fc7fff4fffff085fd0, 0xfffafffde63fffffc4ffffe6fff4cefff33ffd0, 0xfffafffde63fffffc5ffffe6fff4cefff0bffd0, 0xc7fafffddfff44d23fffffe6ffffd657f0bffff,
  0xc2dfff8ff6bffccfff0bffff97ffd6ffffc513f, 0xffffff8ddfff43f205ffffe6fd7fff54d33ffff, 0xffffff8ddfff4ff205ffffe6fd7fff54d0bffff, 0xc2dffffff6bffff2fffcffff957ffffff30513f, 0xfeefff87ffd740cfff0bffff6fffd993ffff13f, 0xc2ca3ffdeffffcdfc4ffffe6ffffd9fff248fff,
  0xc3fffffdefff43f2c4ffffe6fffffffcd318fff, 0xffffffffffd743f2fffffffffff68e93f30513f, 0xffffff87ffff43ffc4fff2e6fff6bf28dfc8fff, 0xcbfaff87fffffccfc40bffe66ffffffd1fd8fd0, 0xfeefffffffd7ffffff0a7fff6fffd94bffff110, 0xfffafffdefffffffc4ffffe6ffffcefcd318fd0,
  0xc2effffdcffffff246fe7fe6fd7fffffffd8fff, 0xffffff8fffff40cfff0a7fff6d76bffc6fff13f, 0xc6efff83f61644d23ffe7ffffff77f93f0bffff, 0xc2ca3f83f67fffffc4ffffdf97f77fffffc8fff, 0xffffff8ff63f43f23fffffff97f77f90d33ffff, 0xc7fa7f8ffffffcefc4fe7fdffdeffffd1ffffd0,
  0xc7fa7f8ffffffcefc5fe7fdffdeffffd1ffffd0, 0xfffafffff63fffffc4fcffdf95e4cefcdffffd0, 0xfeeffffff63ffcd23ffe7ffffff75657f73ffff, 0xfeeffffff63ffcd23ffe7ffffff75657f0bffff, 0xffffff8ff63f43f23fffffff97f77f54d33ffff, 0xc3fa3ffffffffcd2c4fe7fdffffffffff718fff,
  0xfeca3ffffffffcdfc4fe72dffdefd9ffffc8fff, 0xc3fffffffffffff2c4ffffdffdefff90d318fff, 0xc3fa3ffffffffcd2c6fe7fdffffffffff718fff, 0xc2dffffff656fff27f0bffff8a1fff93ffff13f, 0xc3fffffddfff40efc4ffffe6fffffffe0248fff, 0xc3fffffddfd643fffffe7ffffe1fff28627f13f,
  0xfffa3ffddfff43f23ffff8e6ffffff90d33ffff, 0xfffa3ffff6bf43ffc4ffffe6fe1fce28dfc8fff, 0xc6ca7ffdc63fffffff0bffe68a14fffffffffd0, 0xfeda3ffdcfff40cfc5ffffe6ffffd6fe0ffffff, 0xfffa3ffff6bffff27f0a78ff8bffd6ffffc513f, 0xfffa3ffddfff43f23ffff8e6ffffff54d33ffff,
  0xfecfffffffff40e23ffff8fffff77f92073ffff, 0xffffffffffff40efc4fe7fdffff77ffe0248fff, 0xfecfffffffff43f23ffff8fffff74e90d33ffff, 0xfeca7ffffffffff204fe78dffffffffd173ffd0, 0xcbffff87f6bf48f2bfffffffffffe9fc60bffe8, 0xcbffe7fff69747ffc6ffffff0fffe92bfffffe8,
  0xfffffffddfd74cffff0ffffffffffffc627f128, 0xffffff87ffff4cffffffffff0fffe92860bffe8, 0xc6dfe487ffff4bffc5ffffea0ffffffcdffffe8, 0xcadffffddffffff2bf0ffffffffffffff305128, 0xffffff87f6bf4bf2bffcfaff0ffffffc6fc5fe8, 0xcbffe5fddfff4fffc40ffffffffffffcd248fe8,
  0xcbffffffffff4fffff0cffffffffff2bf245128, 0xcafffffff6d7fff27f0bffffffffe94bffff110, 0xcbfffffde6fffcffc40fffffffffe9fd127ffd0, 0xfffffffdeffffcffff0ffffffff4e9fc627f110, 0xc6cfe5fdeffffff23f0fffeaffffff4bf33ffd0, 0xfffffffde6ffffffc40cffeafff4fffff248fd0,
  0xc7ffe781dfff47f23fffffeaffffff57f0bffe8, 0xcedfff8bffff4ff27f0bffffffffff57ffc5128, 0xcffffffddfff44dfc60ffffffd7ffffff27ffe8, 0xffffe7fff6bf47ffc6ffffea0d7fff2bffc8fe8, 0xfffffffddffffcffff0ffffffd7fd6fc627f128, 0xc6ffff89cfffffffc50bffeafd7ffffd1ffffd0,
  0xfefffffff6fffff27f0bfafffd74ffffffc5110, 0xcafffffdefff47f286ffffeafff6bffff0bffe8, 0xcaffff87ffff4bffff0bffff6fffffffffc5128, 0xffffff87ffff48fffffffafffff699fc60bffe8, 0xffffe7fdefd747ffffffffeafff6992bfffffe8, 0xffffe7fdefd747ffffffffeafff6992bfffffe8,
  0xcbffe787fffffff2440bffea6ffffffd1ffffd0, 0xfeffffffffd7ffffff0bfaff6fffd94bffff110, 0xcbfffffdeffffcffc4ffffea6ffffffd1248fd0, 0xc6ffff83f61547ffffffffff0ff769fffffffe8, 0xcffffffff6ff44dfff0ffffffff769fff248fe8, 0xc6cfff8bffff4bf23f0ffafffff77ffcd33ffe8,
  0xc7ffff8bfffffcf23f0ffafffffffffd173ffd0, 0xfffffffff6fffcffc40ffffffdefe9fd1248fd0, 0xfecfff8bfffffff23f0cfafffdefff4bf33ffd0, 0xfeffffffffff44d23f0ffaffffffff57f73ffe8, 0xffffe7ffffff47f23ffffaff0ff77f57f0bffe8, 0xcffffffff6ff44dfff0ffffffff756fff248fe8,
  0xc7ffff8bfffffcf23f0ffafffffffffd173ffd0, 0xcecfff83ffff47f2bffffafffde6bfffffd8fe8, 0xceffff83ffff47f2bffffafffde6bfffffd8fe8, 0xffffe7ffffff47fffffff2df6de6bf2bffc8fe8, 0xc7fffffddfd548ffc5ffffffffffe9fe00bffe8, 0xcffffffff6954bffff0bffff8bffffffffc5128,
  0xfffffffff6bf48f2bffffffffe1fe9fc6085fe8, 0xc7ffe4fddfff4bffc4fcffeafe1ffffcdffffe8, 0xc7ffe4fddfff4bffc5fcffeafe1ffffcdffffe8, 0xc7ffe7fdc63fffffff0bffea8bf4fffffffffd0, 0xc7ffe7fff63f4fffc50bffff8bffff57fffffe8, 0xffffffffffff4cffc5ffffeaffffd65600bffe8,
  0xcfffffffffff4fffff0bffff8bffff546fc5128, 0xc7ffe7fdc63fffffff0bffea8bf4fffffffffd0, 0xcfffe4fdcfff4bffc40bffff6ffffffe0fd8fe8, 0xcfffffffffff4bffff0bffff6e16bfffffc5128, 0xffffe7fffffffff2440bffea6e1fff4bffd8fd0, 0xfffffffff63f48ffc4fffffffff769fe073ffe8,
  0xfffffffff63f48ffc5fffffffff769fe00bffe8, 0xfecffffff63f4bffc4fcffdf8bf77ffcdffffe8, 0xc7fffffffffffcfffffff8df89e4e949173ffd0, 0xffffffffffff48ffc4fffffffff699fe0718fe8, 0xc6dfffffffd744d23fffffffffffe993f0bffe8, 0xcbfffffff69744dffffe7fffffffe92bffc8fe8,
  0xcbfffffff69744dffffe7fffffffe92bffc8fe8, 0xffffff87ffff4ff204fffaff97ffff90dffffe8, 0xffffff87ffff4ff205fffaff0fffff90dffffe8, 0xffffff87ffff4fffc4ffffe697ffff28dfc8fe8, 0xc6cfff87f63ffccfff0bffff97ffe9fd1ffffd0, 0xc6cffffdeffffff23ffcfaff97f4fffff33ffd0,
  0xc6dfff83f63f47ffff0bffff957ffffffffffe8, 0xfffffffddfff44d23ffe7afffd7fff57f0bffe8, 0xcacfff83ffff47f27f0bffff6fffff93ffd8fe8, 0xfecffffdefd747fffffe7ffffff6992bf27ffe8, 0xffffff87fffffff2440a7aff6ffffffd1fd8fd0, 0xc7fffffff63f4ccfff0a7fff8bfffffe0ffffe8,
  0xffffffffffff4ff204fcf8e6fe1fff90d33ffe8, 0xfecffffff63ffccfff0a7fff8a14e9fffffffd0, 0xc7fffffff63f4ccfff0a7fff8bfffffe0ffffe8, 0xcbffe6fff65647ffc6ffffff0ffb7f2bffc8b3f, 0xffffe5fdefd640efff0ffffffffb7ffc627f13f, 0xfffabf87f6154bffc5ffffff0ffb7ffcdfffb3f,
  0xfffa3ffde6d5fff2bf0ffffffffb7ffff30513f, 0xfffffffde6d743ffc70ffffffffffffcd248b3f, 0xfffffffff6d743ffff0fffc7fffb4e2bf27f13f, 0xc7fa6687fffffce23ffffbbffffffffd10bffd0, 0xcbfa65ffffd6fff27f0bfbbfffffff4bffc5110, 0xcbffffffffd6fcefc70ffffffffffffff248b10,
  0xfffa7f87fffffcefc7fef2ff0ffffffd1fc8fd0, 0xfffffffdeffffcefff0effc7fffffffc627f110, 0xfffabfffffd7fff2050ffffffffffffcd33fb10, 0xfffabf87fffffff23ffffbbf0fffce4bf0bffd0, 0xffffffffffd7ffffc70fffffffffcefcd248b10, 0xc3fffffdf6fffcdfc60ffffffffb56fff248b3f,
  0xffffff89ffff43f2050ffffffffb7f54d33fb3f, 0xfffffffff6ff43ffc70ffffffd7b7ffcd248b3f, 0xc7fabf8bfffffccfc50bfbbfffffd6fd1fffb10, 0xfffffffdfffffff2050ffbbffd7ffffcd33fb10, 0xcbfabfffffd5fcd286fffbbffffffffff098b3f, 0xfffa2487ffd5fccfff0bfbbf6fffd9fc6fff13f,
  0xffffe6ffffd7fcdfc6feffffffffd92bffc8b3f, 0xffffe6ffffd7fcdfc6feffffffffd92bffc8b3f, 0xc3ffff87fffffff287fffbbffffffffcd318b3f, 0xcbffff87fffffff287fffbbffffffffcd098b3f, 0xfffa3ffdefd5fff2bffffb876fffcefff33f13f, 0xffffff87ffff43ffc7ffffff6ff6bf28dfc8b3f,
  0xc3ffe683fffffff2460bfbbf6fffff57ffd8b3f, 0xc3fffffdfffffcdfc6feffff6d7ffffff248b3f, 0xc7fa6483ffd5ffffc5fffb9f0defffffffffb3f, 0xc3ffff8bffd5fce2bf0ffbbffffffffff70513f, 0xc3ffe5ffffd6fcdfc60ffffffdeffffff248b3f, 0xffffff8bffff40efff0efffffdefff28627f13f,
  0xfffa3f8bffd5fff2050ffffffdeffffcd33fb3f, 0xfffa3ffff6fffff2bf0ffbbffdefcefff30513f, 0xfffa25fffffffcd2050ffb9fffffff57f73fb3f, 0xfffa3ffff6ffffffc60effdfffffd6fff248b3f, 0xffffff8bffff43ffc50ffb9fffffff54d33fb3f, 0xc7fffffdffd548efc5fffffffffb7ffe00bfb3f,
  0xc3ffe4fdc655ffffff0bffff8a1b7fffffc513f, 0xfffffffdf61543ffc5fffffffe1b4efcdfffb3f, 0xfffffffdf6154bffc5fffffffe1b4efcdfffb3f, 0xc7ffe6ffffd6ffffc50bffff8bfffffd1fffb10, 0xfffa7ffdfffffce23ffef8fffe1fff4bf0bffd0, 0xffffe6fff63f40cfc50bffff8bfb7f560fffb3f,
  0xfffffffdffff43f205ffffff8bfb7f54d33fb3f, 0xffffe6fff63fffffc50affff8bffd6fd1fffb10, 0xc3ffe4ffffd5fccfc70bffff6ffffffe0fd8b3f, 0xfffa3fffffd5fccfff0affc76e1fd9ffffff13f, 0xc3fffffffffffff287fff8fffe1ffffcd318b3f, 0xffffffffffff43f2470affff6fffff560fd8b3f,
  0xffffe4ffffff40efc5feffdffffffffe073fb3f, 0xffffe4ffffff48efc5feffdffffffffe00bfb3f, 0xc3ffffffffd5fce2bffeffff89effffff70513f, 0xfffa3fffffd543ffc5ffffdf8bf74efcdfffb3f, 0xfffa7ffdefd647f205ffffe6fffb7f93f0bfb3f, 0xffffff87f65643f27f0bffff97fb7f93ffc513f,
  0xfffffffde656ffffc6ffffe6fffb7f2bffc8b3f, 0xfffffffde656ffffc6ffffe6fffb7f2bffc8b3f, 0xfffffffdefd640efffffffff97fb7f28627f13f, 0xfffa7f87ffd6ffffc50bffff97fffffd1fffb10, 0xfffa7ffdefffffffc5fffba6fffffffd10bfb10, 0xffffff87f656ffffff0bfbbf97ffff4bffc5110,
  0xfffa3f81c63fffffc50bffe697fb56ffffffb3f, 0xfffa3f83ffd7fff2460bffff6fffff93ffd8b3f, 0xffffffffffd743f27f0bfbbf6fffd9906fff13f, 0xfffa3fffffd7ffffc6ffffe6ffffd92bf248b3f, 0xfffa3ffffffffff2460bfba66d7fffffffd8b3f, 0xffffff83ffd6fff205fffb9ffdefff93ffffb3f,
  0xffffff83ffd6fff205fffb9ffdefff93ffffb3f, 0xc3ffffffffd6ffffc6ffffdf95efff2bffc8b3f, 0xfffa3ffffffffcd205fffb9f97ffd6fff73fb3f, 0xfffffffdc61643ffc50bffff8bffff920fffb3f, 0xffffffffffd643f27f0bffff8a1b7f93ffc513f, 0xffffffffffd6ffffc50bffe68a1ffffd1fffb10,
  0xffffffffffff40cfc50bffe68bfb56fe0fffb3f, 0xffffffffffff40efc5ffffdffff77f92073fb3f, 0xc7ffe4fde63f44dffffffffffffb69fff0bffe8, 0xcbfffffff6d548cfff0bfffffffb7fffffc5128, 0xfffffffdefd54bffc50ffffffffffffcd33fb28, 0xffffff87ffff4bffc5ffffea0ffb7ffcdfffb28,
  0xfffffffdeffffff2bf0fffc7fffb7ffff305128, 0xc7ffe5ffffd7fccfc50bffffffffe9fd1fffb10, 0xfffffffff6d7fff27f0affffffffe94bffc5110, 0xffffffffffd7ffffc50fffeaffffff48d33fb10, 0xc7ffe5fdcfff47ffc50bffeafffb7f57ffffb28, 0xffffff8bfffffccfc50affeafd7ffffd1fffb10,
  0xcbffe4ffffd5ffffc60bffff6fffffffffd8b28, 0xfffffffdefff47f286feffeafff6bffff098fe8, 0xcbffffffffff4bffff0affff6ffffffc6fc5128, 0xc7ffffffffd5fcdfc50fffffffffe9fff73fb28, 0xfffffffff61544dffffeffff0de769fffffffe8, 0xffffffffffd5ffffc50ffffffdefcefcd33fb28,
  0xfffffffffffffcd2050effdfffffff57f73fb28, 0xfffffffff61747ffc50bffff97ffff93ffffb28, 0xffffffffffd747f23ffffffffffb6993f0bfb28, 0xffffffffffd7ffffc50bffff97ffe9491fffb10, 0xfffffffff63f47ffc50bffe6957b7fffffffb28, 0xffffffffffd7ffffc60bffff6fffd993ffd8b28,
  0xfffa648ddfff48efffffffffff2ffffc60bfff0, 0xfeda6683ffd647ffffffffff0f2fff2bffffff0, 0xfffabf8ff6954bffc7ffffff0ffffffcdff1ff0, 0xfffafffddfd5fff2bf0ffffffffffffff305130, 0xffffff8ff6954bffffffffc70f2fcefc6fffff0, 0xfffabf89dfff4fffff0ff2fffffffffcd27fff0,
  0xfeea65fdcfd6ffffff0bffffff2fff4bffff110, 0xfeca7f89fffffcefff0fffffff2ffffd127ffd0, 0xfffabffdf6fffff2ff0ffffffff4fffff331fd0, 0xfecffffdf6ffffffff0ff2ffff24cefff27ffd0, 0xfffaa6fff6bf44d2ffffffffffffff57f0b1ff0, 0xfedae5ffffff4ccfff0bffffffffff546fff130,
  0xfedabffddfff44dfff0fffffffffd6fff27fff0, 0xffffe6fff6bf44dfffff32ff0fffd62bffffff0, 0xfffffffddfff4ff2c70fffffffffff57f331ff0, 0xffffff8fffff4fffc7ffffff0d7fff54dff1ff0, 0xfffffffddffffff2ff0fffc7ffffff57f305130, 0xfffabf89dfff4fffff0ff2fffffffffcd27fff0,
  0xfeeabffff6fffccfc70bffffffffd6fd1ff1fd0, 0xfffafffff6fffccfff0b3fc7fff4d6ffffff110, 0xfffabffdf6fffff2ff0ffffffff4fffff331fd0, 0xfeeabffdffd544dfffffffffff26bffff0bfff0, 0xffffff8dffff4bffc4ffffffff26bffcdfd8ff0, 0xffffff8dffff4bffc7ffffffff26bffcdfd8ff0,
  0xfffaa68ffffffccfff0b3fff6ffffffd1ffffd0, 0xfffabffffffffff2fffcffff6f24ce48d318fd0, 0xfeeaa683ffff47ffff0bffff6fffff57ffffff0, 0xffffe6ffffff47f2ffff3ffffff6bf57f098ff0, 0xfffaa68ffffffccfff0b3fff6ffffffd1ffffd0, 0xfeea64fff67f47ffc6ffffff0ff77ffffff1ff0,
  0xfeefffffffff48e2bf0ffffffffffffff705130, 0xffffff8fffff48efffff3fff0ff77ffc60bfff0, 0xfeca65ffffff44dfff0f3ffffff77f2bf27fff0, 0xfffafffff6ff4bf2840ffffffff77ffcd331ff0, 0xfffaffffffff4bf2bf0ffffffff74efff305130, 0xfffa65fffffffce2c40ffffffffffffd1731fd0,
  0xfffffffffffffce2ff0f3fffffffff4bf705110, 0xffffff8bfffffcefc40f32dffffffffd127ffd0, 0xfffffffff6fffff2c40fffdfffffce4bf331fd0, 0xfffae4ffffff44dfffff3fdffff699ffffffff0, 0xfffae4ffffff44dfffff3fdffff699ffffffff0, 0xffffff8fffff4bffc4ffffdf6ff6bffcdfd8ff0,
  0xfeda7fffffff48e287fffffffffffffe00b1ff0, 0xfeda64ffffff4bffff0bffff8bfffffc6fff130, 0xfffffffddfff48e2bfff38c7fffffffc60bfff0, 0xffffe6ffffff4cefc4ff3fffffffff2a0fc8ff0, 0xffffe6ffffff4cefc7ff3fffffffff2a0fc8ff0, 0xfffabffff6bf4bf284fff8ffffffcefcdff1ff0,
  0xfffabffff6bf4bf287fff8ffffffcefcdff1ff0, 0xffffe6ffffff4fffc4fcf2ff8bffce28dfc8ff0, 0xfeca66fff67ffff27f0bffff8bffff4bfff1fd0, 0xfeca7ffdfffffcefffff32ff8bf4fffff27ffd0, 0xfecaa4ffffff48cfff0bffff6fffd9fe0fffff0, 0xfecffffdffff4bffc4fff8fffff6bffcd318ff0,
  0xfecfe6fffffffff27f0b38ff6fffd94bfffffd0, 0xfffa7ffddfd647f2c6ffffffffffff93f0b1ff0, 0xfffa7f8fffd64fffff0bffff97fffffc6fff130, 0xffffffffffd64ff2ffffffffff2fff9060bf130, 0xfffa7f81dfd647fffffff2e6ff2fff2bffffff0, 0xfffa7f81dfd647fffffff2e6ff2fff2bffffff0,
  0xfffa7f8dc67fffffc40bffff97fffffd1ff1fd0, 0xfeefffffffd6ffffff0bffff9724ff4bffff110, 0xfffafffff6bf47ffc60bffe697ffd6ffffffff0, 0xfffffffff6bf47f2c6ffffe6ffffd657f0b1ff0, 0xfffaffffffff4fffff0bffff97ffd6546fff130, 0xfffaff81cfff47ffff0bffe66ff6bfffffffff0,
  0xffffff8ffffffccfc40bffe66f2fd9fd1ffffd0, 0xfffaff81cfff47ffff0bffe66ff6bfffffffff0, 0xfffffffff65647f2fffffffffff77f93fff1ff0, 0xfffffffff65647f2fffffffffff77f93fff1ff0, 0xfecffffff65647fffffff2ff95e77f2bffffff0, 0xfffa7ffffffffce2c4ffffdf97fffffd1731fd0,
  0xffffffffffff47f2fffe7fdffff69993f718ff0, 0xfffa7ffff67f4ff2440bffff8bffff920fffff0, 0xfffa7fffffff4fffff0bf8ff8bffff906fff130, 0xffffffffffff4cefc4ffffe6ffffff2a0248ff0, 0xfffffffff67ffff2440bf8e68bf4fffffff1fd0, 0xfedfff8bffd548cfff0bffffff2fe9fc6fff128,
  0xffffe5fddfff44dfff0f3feafffffffff27ffe8, 0xffffff89dfff4bf2840fffeafffffffff331fe8, 0xfffffffddffffff2bf0ffaffff2ffffff305128, 0xffffff8bffff4fffc40fffeaff2fff28d27ffe8, 0xfedfe5ffffff47f2460bffeaffffff57fff1fe8, 0xffffff8bffff4ff27f0b3affffffff546fff128,
  0xffffe5fddfff44dfff0f3feafffffffff27ffe8, 0xfecfe481cfff47ffff0bffea6f26bffffffffe8, 0xfecffffff6ff44d2bf0fffffffffe9fff731fe8, 0xfecffffff6fffcdfff0f3ffffff7692bf27ffe8, 0xfffffffff6fffff2840ffafffff77ffcd331fe8, 0xfecfffffffff44d2bfff3aff6ff6bffff73ffe8,
  0xffffe4fff6bf48cfc40bffff8bffe9fe0ff1fe8, 0xfffffffff6954bffff0b3fff8bffe9fc6fff128, 0xfffffffff6bf4bf284ffffea8bfffffcd331fe8, 0xffffffffffff48cfc40b3fea6ff6bffe0ffffe8, 0xffffff83f6bf47f27f0bfaff97ffff93fff1fe8, 0xfffffffff6bf47fffffe72e6972fe92bf248fe8,
  0xffffff83f6bf47f27f0bfaff97ffff57fff1fe8, 0xfecfffffffff47f27f0bfaff6f26bf93fffffe8, 0xffffffffffff4ff2440bffff8bffe9920ff1fe8, 0xfffa7f81f67f47f2bffffffffffb7ffff0b1ff0, 0xfffa7f89cfd54bffff0bfffffffb7ffc6fff130, 0xfffffffdffd647ffc60ffffffffffffff248b30,
  0xffffe6ffffd647ffffffffff0f2b7f2bffffb30, 0xfffa7f8bffd6fff2470bfffffffffffd1ff1b10, 0xffffff8bffd6fff27f0bfb87ff2fff4bffff110, 0xffffffffffd6ffffc70fffffff2ffffd1248b10, 0xfffabffff6ff47f2460bfffffffb7f57fff1b30, 0xfffffffdfffffcdfc60ffffffffb56fff248b30,
  0xfffffffff6fffff2470bfbbfffffd6fd1ff1b10, 0xfffabf83ffd5ffffc60bffff6fffffffffd8b30, 0xfffffffdffff44d2bffffbbfff2699fff0bfff0, 0xffffe6ffffff47ffc60bfbbf6fffff57ffd8b30, 0xfffa7fffffd5fff2860ffffffffffffff731b30, 0xfffffffff67f47f286fffb9f0ff77ffffff1ff0,
  0xfffffffffffffce2bf0ffbbffffffffc6705130, 0xffffffffffd6ffffc60fffdfffffff2bf248b30, 0xfffffffff6554bffc70bffff8bfffffffff1b30, 0xffffffffffff48efc7fffffffffb7ffe00b1b30, 0xfffa7fffffff4bffff0bffc78bfb7ffc6fff130, 0xffffffffffd6ffffc70bffff8bffff491ff1b10,
  0xffffffffffd5ffffc70bffff6fffd9fe0fd8b30, 0xfffffffdc6d547ffc60bffffffffe9fffff1b28, 0xfffffffff6ff48cfff0bffffff2b69fc6fff128, 0xfffffffff6fffff2460bffeafffb7f57fff1b28, 0xffffffffffd5ffffc60bffea6f2fffffffd8b28, 0xffffffffffd5ffffc60ffffffdefe9fff731b28]

private def flag (i w : Nat) := (packed[i]! >>> (6*w)) &&& 63
private def contribution (i w : Nat) : Nat :=
  let k := flag i w
  if k < 52 ∧
     positiveWords[k]! &&& (negativeWords[i]! ||| mins[w]!) = positiveWords[k]!
  then boards[w]! else 0

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
private theorem bits0 : ∀ j : Fin 468, boards[0]!.testBit j.val = true → mins[0]! &&& negativeWords[j.val]! = mins[0]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits1 : ∀ j : Fin 468, boards[1]!.testBit j.val = true → mins[1]! &&& negativeWords[j.val]! = mins[1]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits2 : ∀ j : Fin 468, boards[2]!.testBit j.val = true → mins[2]! &&& negativeWords[j.val]! = mins[2]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits3 : ∀ j : Fin 468, boards[3]!.testBit j.val = true → mins[3]! &&& negativeWords[j.val]! = mins[3]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits4 : ∀ j : Fin 468, boards[4]!.testBit j.val = true → mins[4]! &&& negativeWords[j.val]! = mins[4]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits5 : ∀ j : Fin 468, boards[5]!.testBit j.val = true → mins[5]! &&& negativeWords[j.val]! = mins[5]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits6 : ∀ j : Fin 468, boards[6]!.testBit j.val = true → mins[6]! &&& negativeWords[j.val]! = mins[6]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits7 : ∀ j : Fin 468, boards[7]!.testBit j.val = true → mins[7]! &&& negativeWords[j.val]! = mins[7]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits8 : ∀ j : Fin 468, boards[8]!.testBit j.val = true → mins[8]! &&& negativeWords[j.val]! = mins[8]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits9 : ∀ j : Fin 468, boards[9]!.testBit j.val = true → mins[9]! &&& negativeWords[j.val]! = mins[9]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits10 : ∀ j : Fin 468, boards[10]!.testBit j.val = true → mins[10]! &&& negativeWords[j.val]! = mins[10]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits11 : ∀ j : Fin 468, boards[11]!.testBit j.val = true → mins[11]! &&& negativeWords[j.val]! = mins[11]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits12 : ∀ j : Fin 468, boards[12]!.testBit j.val = true → mins[12]! &&& negativeWords[j.val]! = mins[12]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits13 : ∀ j : Fin 468, boards[13]!.testBit j.val = true → mins[13]! &&& negativeWords[j.val]! = mins[13]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits14 : ∀ j : Fin 468, boards[14]!.testBit j.val = true → mins[14]! &&& negativeWords[j.val]! = mins[14]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits15 : ∀ j : Fin 468, boards[15]!.testBit j.val = true → mins[15]! &&& negativeWords[j.val]! = mins[15]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits16 : ∀ j : Fin 468, boards[16]!.testBit j.val = true → mins[16]! &&& negativeWords[j.val]! = mins[16]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits17 : ∀ j : Fin 468, boards[17]!.testBit j.val = true → mins[17]! &&& negativeWords[j.val]! = mins[17]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits18 : ∀ j : Fin 468, boards[18]!.testBit j.val = true → mins[18]! &&& negativeWords[j.val]! = mins[18]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits19 : ∀ j : Fin 468, boards[19]!.testBit j.val = true → mins[19]! &&& negativeWords[j.val]! = mins[19]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits20 : ∀ j : Fin 468, boards[20]!.testBit j.val = true → mins[20]! &&& negativeWords[j.val]! = mins[20]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits21 : ∀ j : Fin 468, boards[21]!.testBit j.val = true → mins[21]! &&& negativeWords[j.val]! = mins[21]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits22 : ∀ j : Fin 468, boards[22]!.testBit j.val = true → mins[22]! &&& negativeWords[j.val]! = mins[22]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits23 : ∀ j : Fin 468, boards[23]!.testBit j.val = true → mins[23]! &&& negativeWords[j.val]! = mins[23]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits24 : ∀ j : Fin 468, boards[24]!.testBit j.val = true → mins[24]! &&& negativeWords[j.val]! = mins[24]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits25 : ∀ j : Fin 468, boards[25]!.testBit j.val = true → mins[25]! &&& negativeWords[j.val]! = mins[25]! := by decide +kernel
private theorem boardOK (w : Fin 26) (j : Fin 468) : boards[w.val]!.testBit j.val = true → mins[w.val]! &&& negativeWords[j.val]! = mins[w.val]! := by
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
private abbrev covering (i : Nat) := (union i (List.range 26) ||| (1 <<< i) ||| (1 <<< (partners[i]! % 468))) = 2^468-1
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, covering (r.val+0) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, covering (r.val+8) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, covering (r.val+16) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, covering (r.val+24) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, covering (r.val+32) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, covering (r.val+40) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, covering (r.val+48) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, covering (r.val+56) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, covering (r.val+64) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, covering (r.val+72) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, covering (r.val+80) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, covering (r.val+88) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, covering (r.val+96) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, covering (r.val+104) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, covering (r.val+112) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, covering (r.val+120) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, covering (r.val+128) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, covering (r.val+136) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, covering (r.val+144) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, covering (r.val+152) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, covering (r.val+160) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, covering (r.val+168) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, covering (r.val+176) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, covering (r.val+184) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, covering (r.val+192) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, covering (r.val+200) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, covering (r.val+208) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, covering (r.val+216) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, covering (r.val+224) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, covering (r.val+232) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, covering (r.val+240) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, covering (r.val+248) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 8, covering (r.val+256) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block33 : ∀ r : Fin 8, covering (r.val+264) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block34 : ∀ r : Fin 8, covering (r.val+272) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block35 : ∀ r : Fin 8, covering (r.val+280) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block36 : ∀ r : Fin 8, covering (r.val+288) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block37 : ∀ r : Fin 8, covering (r.val+296) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block38 : ∀ r : Fin 8, covering (r.val+304) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block39 : ∀ r : Fin 8, covering (r.val+312) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block40 : ∀ r : Fin 8, covering (r.val+320) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block41 : ∀ r : Fin 8, covering (r.val+328) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block42 : ∀ r : Fin 8, covering (r.val+336) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block43 : ∀ r : Fin 8, covering (r.val+344) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block44 : ∀ r : Fin 8, covering (r.val+352) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block45 : ∀ r : Fin 8, covering (r.val+360) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block46 : ∀ r : Fin 8, covering (r.val+368) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block47 : ∀ r : Fin 8, covering (r.val+376) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block48 : ∀ r : Fin 8, covering (r.val+384) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block49 : ∀ r : Fin 8, covering (r.val+392) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block50 : ∀ r : Fin 8, covering (r.val+400) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block51 : ∀ r : Fin 8, covering (r.val+408) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block52 : ∀ r : Fin 8, covering (r.val+416) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block53 : ∀ r : Fin 8, covering (r.val+424) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block54 : ∀ r : Fin 8, covering (r.val+432) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block55 : ∀ r : Fin 8, covering (r.val+440) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block56 : ∀ r : Fin 8, covering (r.val+448) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block57 : ∀ r : Fin 8, covering (r.val+456) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block58 : ∀ r : Fin 4, covering (r.val+464) := by decide +kernel
private theorem checked (i : Fin 468) : covering i.val := by
  have h (q : Fin 59) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 468) : covering (r+8*q.val) := by
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
    | ⟨32,_⟩ => exact block32 ⟨r,hr⟩
    | ⟨33,_⟩ => exact block33 ⟨r,hr⟩
    | ⟨34,_⟩ => exact block34 ⟨r,hr⟩
    | ⟨35,_⟩ => exact block35 ⟨r,hr⟩
    | ⟨36,_⟩ => exact block36 ⟨r,hr⟩
    | ⟨37,_⟩ => exact block37 ⟨r,hr⟩
    | ⟨38,_⟩ => exact block38 ⟨r,hr⟩
    | ⟨39,_⟩ => exact block39 ⟨r,hr⟩
    | ⟨40,_⟩ => exact block40 ⟨r,hr⟩
    | ⟨41,_⟩ => exact block41 ⟨r,hr⟩
    | ⟨42,_⟩ => exact block42 ⟨r,hr⟩
    | ⟨43,_⟩ => exact block43 ⟨r,hr⟩
    | ⟨44,_⟩ => exact block44 ⟨r,hr⟩
    | ⟨45,_⟩ => exact block45 ⟨r,hr⟩
    | ⟨46,_⟩ => exact block46 ⟨r,hr⟩
    | ⟨47,_⟩ => exact block47 ⟨r,hr⟩
    | ⟨48,_⟩ => exact block48 ⟨r,hr⟩
    | ⟨49,_⟩ => exact block49 ⟨r,hr⟩
    | ⟨50,_⟩ => exact block50 ⟨r,hr⟩
    | ⟨51,_⟩ => exact block51 ⟨r,hr⟩
    | ⟨52,_⟩ => exact block52 ⟨r,hr⟩
    | ⟨53,_⟩ => exact block53 ⟨r,hr⟩
    | ⟨54,_⟩ => exact block54 ⟨r,hr⟩
    | ⟨55,_⟩ => exact block55 ⟨r,hr⟩
    | ⟨56,_⟩ => exact block56 ⟨r,hr⟩
    | ⟨57,_⟩ => exact block57 ⟨r,hr⟩
    | ⟨58,_⟩ => exact block58 ⟨r,by change r + 464 < 468 at hs; omega⟩
    | ⟨a+59,ha⟩ => omega
  have eq : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [eq] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega)

private theorem posRows : ∀ p : Fin 52, positiveWords[p.val]! = pos p.val := by decide +kernel
private theorem negRows : ∀ i : Fin 468, negativeWords[i.val]! = neg i.val := by decide +kernel

private theorem bitLift (p a m b : Bool) (c : (p && (a || m)) = p) (d : (m && b) = m) : (p && (a || b)) = p := by
  cases p <;> cases a <;> cases m <;> cases b <;> simp_all

private theorem hit (a b : Fin 468) (lt : a < b) (ne : mate b ≠ a) :
    ∃ p : Fin 52, pos p.val &&& (neg b.val ||| neg a.val) = pos p.val := by
  have h : (union b.val (List.range 26) ||| (1 <<< b.val) ||| (1 <<< (mate b).val)) = 2^468-1 := checked b
  have full := congrArg (fun x : Nat => x.testBit a.val) h
  have diff : (mate b).val ≠ a.val := fun e => ne (Fin.ext e)
  have less : b.val ≠ a.val := by change a.val < b.val at lt; omega
  simp only [Nat.testBit_or,Nat.one_shiftLeft,Nat.testBit_two_pow,decide_eq_false less,
    decide_eq_false diff,Bool.or_false,Nat.testBit_two_pow_sub_one,decide_eq_true a.isLt] at full
  obtain ⟨w,hw,on⟩ := member (List.range 26) full
  let k := flag b.val w
  by_cases ok : k < 52 ∧ positiveWords[k]! &&& (negativeWords[b.val]! ||| mins[w]!) = positiveWords[k]!
  · have yes : boards[w]!.testBit a.val = true := by
      simpa only [contribution,← show k = flag b.val w from rfl,ite_eq_left ok] using on
    have sub := boardOK ⟨w,List.mem_range.mp hw⟩ a yes
    refine ⟨⟨k,ok.1⟩,?_⟩
    rw [← posRows ⟨k,ok.1⟩,← negRows b,← negRows a]
    apply Nat.eq_of_testBit_eq
    intro z
    have h1 := congrArg (fun t : Nat => t.testBit z) ok.2
    have h2 := congrArg (fun t : Nat => t.testBit z) sub
    simp only [Nat.testBit_and,Nat.testBit_or] at h1 h2 ⊢
    exact bitLift _ _ _ _ h1 h2
  · simp only [contribution,← show k = flag b.val w from rfl,ite_eq_right ok,Nat.zero_testBit] at on
    exact Bool.noConfusion on

private theorem missing : ∀ b : Fin 468, mate b < b → ∀ p : Fin 52, positiveWords[p.val]! &&& (negativeWords[b.val]! ||| negativeWords[(mate b).val]!) ≠ positiveWords[p.val]! := by decide +kernel
end PEqualNP.Research.Plane888ConflictGraph

open PEqualNP.Research.Plane888NineFlags PEqualNP.Research.Plane888ConflictGraph in
theorem PEqualNP.Research.Plane888ConflictGraph :
    (∀ i : Fin 468, mate (mate i) = i) ∧
    ((List.range 468).filter (fun i => decide (partners[i]! % 468 < i))).length = 54 ∧
    ∀ a b : Fin 468, a < b → (mate b ≠ a ↔
      ∃ p : Fin 52, pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro a b lt
  constructor
  · intro ne
    simpa only [Nat.or_comm (neg a.val) (neg b.val)] using hit a b lt ne
  · rintro ⟨p,h⟩ rfl
    have fail := missing b lt p
    rw [posRows,negRows,negRows] at fail
    rw [Nat.or_comm] at h
    exact fail h
