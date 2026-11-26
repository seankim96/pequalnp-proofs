import PEqualNP.Research.PlaneCase35FourthOrBudget

namespace PEqualNP.Research.PlaneCase35FifthTransport
open PEqualNP.Research.PlaneCase35FourthOrBudget
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
private def masks : Array Nat := #[66559, 151064335, 38655692548, 4222125724733184, 105553117253440, 4027515584, 105553117257472, 2251799814731264, 3298535928320, 9896142507776, 12617451008, 16492674546176, 84881152, 252248591, 17180853775, 52776559116815, 263882791256591, 1030807945728]
private def slot : Array (Fin 18) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 6, 7, 7, 7, 0, 2, 2, 2, 17, 17, 17, 17, 1, 13, 12, 1, 5, 5, 3, 5, 2, 10, 14, 2, 17, 17, 17, 17, 8, 8, 11, 9, 15, 4, 4, 16, 3, 3, 3, 3]
private def mask (k : Fin 18) := masks[k.val]!
private theorem allMasks (first : W 66559) (second : W 1030807945728) (k : Fin 18) : W (mask k) := by
  have h0 := hop 66559 281475144544271 1 first (by decide +kernel)
  have h1 := hop 281475144544271 151064335 2 h0 (by decide +kernel)
  have h2 := hop 281475144544271 2685337842 0 h0 (by decide +kernel)
  have h3 := hop 2685337842 4222137535623172 1 h2 (by decide +kernel)
  have h4 := hop 4222137535623172 38655692548 2 h3 (by decide +kernel)
  have h5 := hop 66559 1064944 0 first (by decide +kernel)
  have h6 := hop 1064944 687446487552 1 h5 (by decide +kernel)
  have h7 := hop 687446487552 5501585661952 0 h6 (by decide +kernel)
  have h8 := hop 5501585661952 2549767464876032 2 h7 (by decide +kernel)
  have h9 := hop 2549767464876032 4222125724733184 2 h8 (by decide +kernel)
  have h10 := hop 66559 264983107600399 2 first (by decide +kernel)
  have h11 := hop 264983107600399 4239729721606384 0 h10 (by decide +kernel)
  have h12 := hop 4239729721606384 563156111855375 0 h11 (by decide +kernel)
  have h13 := hop 563156111855375 6597069828340 0 h12 (by decide +kernel)
  have h14 := hop 6597069828340 105553117253440 0 h13 (by decide +kernel)
  have h15 := hop 4239729721606384 227599175446528 1 h11 (by decide +kernel)
  have h16 := hop 227599175446528 4222124661153536 2 h15 (by decide +kernel)
  have h17 := hop 4222124661153536 4027515584 2 h16 (by decide +kernel)
  have h18 := hop 4239729721606384 263921447403520 2 h11 (by decide +kernel)
  have h19 := hop 263921447403520 16535639818256 2 h18 (by decide +kernel)
  have h20 := hop 16535639818256 105553117257472 1 h19 (by decide +kernel)
  have h21 := hop 1064944 263886817200656 2 h5 (by decide +kernel)
  have h22 := hop 263886817200656 4222189075210496 0 h21 (by decide +kernel)
  have h23 := hop 4222189075210496 1030792482831 0 h22 (by decide +kernel)
  have h24 := hop 1030792482831 16492679790832 0 h23 (by decide +kernel)
  have h25 := hop 16492679790832 2251799814731264 1 h24 (by decide +kernel)
  have h26 := hop 281475144544271 2130306924559 1 h0 (by decide +kernel)
  have h27 := hop 2130306924559 282505768861855 2 h26 (by decide +kernel)
  have h28 := hop 282505768861855 159360466616335 2 h27 (by decide +kernel)
  have h29 := hop 159360466616335 860917605597424 0 h28 (by decide +kernel)
  have h30 := hop 860917605597424 3298535928320 1 h29 (by decide +kernel)
  have h31 := hop 151064335 2417029360 0 h1 (by decide +kernel)
  have h32 := hop 2417029360 263882790706960 2 h31 (by decide +kernel)
  have h33 := hop 263882790706960 4222124650918144 0 h32 (by decide +kernel)
  have h34 := hop 4222124650918144 9896142507776 2 h33 (by decide +kernel)
  have h35 := hop 2685337842 42965405472 0 h2 (by decide +kernel)
  have h36 := hop 42965405472 105553367944960 1 h35 (by decide +kernel)
  have h37 := hop 105553367944960 4290773248 2 h36 (by decide +kernel)
  have h38 := hop 4290773248 788590688 2 h37 (by decide +kernel)
  have h39 := hop 788590688 12617451008 0 h38 (by decide +kernel)
  have h40 := hop 38655692548 618491080768 0 h4 (by decide +kernel)
  have h41 := hop 618491080768 1030792187808 1 h40 (by decide +kernel)
  have h42 := hop 1030792187808 16492674546176 0 h41 (by decide +kernel)
  have h43 := hop 151064335 1103739486223 2 h1 (by decide +kernel)
  have h44 := hop 1103739486223 64434012175 1 h43 (by decide +kernel)
  have h45 := hop 64434012175 1030944194800 0 h44 (by decide +kernel)
  have h46 := hop 1030944194800 5305072 1 h45 (by decide +kernel)
  have h47 := hop 5305072 84881152 0 h46 (by decide +kernel)
  have h48 := hop 263921447403520 4222743158456320 0 h18 (by decide +kernel)
  have h49 := hop 4222743158456320 3299054977039 0 h48 (by decide +kernel)
  have h50 := hop 3299054977039 844425181794319 2 h49 (by decide +kernel)
  have h51 := hop 844425181794319 252248591 2 h50 (by decide +kernel)
  have h52 := hop 2685337842 280375465132034 2 h2 (by decide +kernel)
  have h53 := hop 280375465132034 4486007441915936 0 h52 (by decide +kernel)
  have h54 := hop 4486007441915936 4222124660097551 0 h53 (by decide +kernel)
  have h55 := hop 4222124660097551 269418591 2 h54 (by decide +kernel)
  have h56 := hop 269418591 4222141830565903 1 h55 (by decide +kernel)
  have h57 := hop 4222141830565903 17180853775 2 h56 (by decide +kernel)
  have h58 := hop 264983107600399 29796401167 1 h10 (by decide +kernel)
  have h59 := hop 29796401167 1120986525711 2 h58 (by decide +kernel)
  have h60 := hop 1120986525711 281526516322063 2 h59 (by decide +kernel)
  have h61 := hop 281526516322063 824633782514 0 h60 (by decide +kernel)
  have h62 := hop 824633782514 264501265960706 2 h61 (by decide +kernel)
  have h63 := hop 264501265960706 4225423185604640 0 h62 (by decide +kernel)
  have h64 := hop 4225423185604640 52776559116815 0 h63 (by decide +kernel)
  have h65 := hop 1064944 17235712 0 h5 (by decide +kernel)
  have h66 := hop 17235712 13198233177856 2 h65 (by decide +kernel)
  have h67 := hop 13198233177856 211171730845696 0 h66 (by decide +kernel)
  have h68 := hop 211171730845696 64435007232 2 h67 (by decide +kernel)
  have h69 := hop 64435007232 1030960246784 0 h68 (by decide +kernel)
  have h70 := hop 1030960246784 16495363948544 0 h69 (by decide +kernel)
  have h71 := hop 16495363948544 4238617325125664 2 h70 (by decide +kernel)
  have h72 := hop 4238617325125664 263882791256591 0 h71 (by decide +kernel)
  match k with
  | ⟨0,_⟩ => exact first
  | ⟨1,_⟩ => exact h1
  | ⟨2,_⟩ => exact h4
  | ⟨3,_⟩ => exact h9
  | ⟨4,_⟩ => exact h14
  | ⟨5,_⟩ => exact h17
  | ⟨6,_⟩ => exact h20
  | ⟨7,_⟩ => exact h25
  | ⟨8,_⟩ => exact h30
  | ⟨9,_⟩ => exact h34
  | ⟨10,_⟩ => exact h39
  | ⟨11,_⟩ => exact h42
  | ⟨12,_⟩ => exact h47
  | ⟨13,_⟩ => exact h51
  | ⟨14,_⟩ => exact h57
  | ⟨15,_⟩ => exact h64
  | ⟨16,_⟩ => exact h72
  | ⟨17,_⟩ => exact second
  | ⟨a+18,ha⟩ => omega
private theorem covers : ∀ u : Fin 52, let m := mask (slot[u.val]!)
    m.testBit 9 = true ∧ m.testBit 16 = true ∧ m.testBit u.val = true := by decide +kernel
end PEqualNP.Research.PlaneCase35FifthTransport
open PEqualNP.Research.PlaneCase35FifthTransport PEqualNP.Research.PlaneCase35FourthOrBudget in
theorem PEqualNP.Research.PlaneCase35FifthTransport : W 66559 → W 1030807945728 → ∀ u : Fin 52,
    ∃ f : Fin 257 → Fin 468, ∀ i j : Fin 257, i < j →
    ∃ p : Fin 52, p.val ≠ 9 ∧ p.val ≠ 16 ∧ p ≠ u ∧
      pos p.val ||| (neg (f i).val ||| neg (f j).val) = neg (f i).val ||| neg (f j).val := by
  intro first second u
  obtain ⟨f,h⟩ := allMasks first second (slot[u.val]!)
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,off,cov⟩ := h i j lt
  obtain ⟨a,b,c⟩ := covers u
  exact ⟨p,by rintro e; rw [e,a] at off; contradiction,
    by rintro e; rw [e,b] at off; contradiction,
    by rintro rfl; rw [c] at off; contradiction,cov⟩
