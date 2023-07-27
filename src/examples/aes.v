Require Import String List ZArith.
From Usuba Require Import ident usuba_AST syntax arch.
Open Scope Z_scope.


Definition SubBytes_single : ident := "SubBytes_single"%string.
Definition SubBytes : ident := "SubBytes"%string.
Definition inputSB : ident := "inputSB"%string.
Definition ShiftRows : ident := "ShiftRows"%string.
Definition inputSR : ident := "inputSR"%string.
Definition times2 : ident := "times2"%string.
Definition times3 : ident := "times3"%string.
Definition MixColumn_single : ident := "MixColumn_single"%string.
Definition inp : ident := "inp"%string.
Definition MixColumn : ident := "MixColumn"%string.
Definition AddRoundKey : ident := "AddRoundKey"%string.
Definition AES : ident := "AES"%string.
Definition r : ident := "r"%string.

Definition node_subBytes_single := table SubBytes_single args input:v8 returns output:v8 let
    99; 124; 119; 123; 242; 107; 111; 197; 48; 1; 103; 43; 254; 215; 171; 118;
    202; 130; 201; 125; 250; 89; 71; 240; 173; 212; 162; 175; 156; 164; 114; 192;
    183; 253; 147; 38; 54; 63; 247; 204; 52; 165; 229; 241; 113; 216; 49; 21;
    4; 199; 35; 195; 24; 150; 5; 154; 7; 18; 128; 226; 235; 39; 178; 117;
    
    9; 131; 44; 26; 27; 110; 90; 160; 82; 59; 214; 179; 41; 227; 47; 132;
    83; 209; 0; 237; 32; 252; 177; 91; 106; 203; 190; 57; 74; 76; 88; 207;
    208; 239; 170; 251; 67; 77; 51; 133; 69; 249; 2; 127; 80; 60; 159; 168;
    81; 163; 64; 143; 146; 157; 56; 245; 188; 182; 218; 33; 16; 255; 243; 210;
    
    205; 12; 19; 236; 95; 151; 68; 23; 196; 167; 126; 61; 100; 93; 25; 115;
    96; 129; 79; 220; 34; 42; 144; 136; 70; 238; 184; 20; 222; 94; 11; 219;
    224; 50; 58; 10; 73; 6; 36; 92; 194; 211; 172; 98; 145; 149; 228; 121;
    231; 200; 55; 109; 141; 213; 78; 169; 108; 86; 244; 234; 101; 122; 174; 8;
    
    186; 120; 37; 46; 28; 166; 180; 198; 232; 221; 116; 31; 75; 189; 139; 138;
    112; 62; 181; 102; 72; 3; 246; 14; 97; 53; 87; 185; 134; 193; 29; 158;
    225; 248; 152; 17; 105; 217; 142; 148; 155; 30; 135; 233; 206; 85; 40; 223;
    140; 161; 137; 13; 191; 230; 66; 104; 65; 153; 45; 15; 176; 84; 187; 22
tel.

Definition node_subbytes := node SubBytes args inputSB:b[16][8] returns out:b[16][8] vars nil
let
    (out, nil) :: nil <|- Fun SubBytes_single None (16%nat :: nil) nil (ECons inputSB Enil)
tel.

Definition node_shift_rows := node ShiftRows args inputSR:b[16][8] returns output:b[128] vars nil
let
    (output, nil) :: nil <|- inputSR $ [0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11 ]
tel.

Definition node_times2 := node times2 args i:b[8] returns o:b[8] vars nil
let
    (o, nil) :: nil <|- (i << 1) xor [0,0,0,i[0],i[0],0,i[0],i[0] ]
tel.

Definition node_times3 := node times3 args i:b[8] returns o:b[8] vars nil
let
    (o, nil) :: nil <|- times2 @ [i] xor i
tel.

(* XXX: this could be automatically produced by a matrix multiplication by a constant matrix *)
Definition node_MixColumn_single := node MixColumn_single args inp:b[4][8] returns out:b[4][8] vars nil
let
    (out, IInd 0 :: nil) :: nil <|- times2 @ [inp[0]] xor times3 @ [inp[1]] xor inp[2] xor inp[3];
    (out, IInd 1 :: nil) :: nil <|- inp[0] xor times2 @ [inp[1]] xor times3 @ [inp[2]] xor inp[3];
    (out, IInd 2 :: nil) :: nil <|- inp[0] xor inp[1] xor times2 @ [inp[2]] xor times3 @ [inp[3]];
    (out, IInd 3 :: nil) :: nil <|- times3 @ [inp[0]] xor inp[1] xor inp[2] xor times2 @ [inp[3]]
tel.

Definition node_MixColumn := node MixColumn args inp:b[4][32] returns out:b[4][32] vars nil
let
    for i in 0 to 3 do
       (out, IInd i :: nil) :: nil <|- MixColumn_single @ [inp[i]]
    done
tel.

Definition node_AddRoundKey := node AddRoundKey args  i:b[128], key:b[128] returns r:b[128] vars nil
let
    (r, nil) :: nil <|- i xor key
tel.

Definition node_AES := node AES args plain:b[128], key:b[11][128] returns cipher:b[128]
vars
    (tmp : b[10][128])%ua_var_decl :: nil
let
    (* Initial AddRoundKey *)
    (tmp, IInd 0 :: nil) :: nil <|- AddRoundKey @ [plain, key[0]];

    (* XXX: use imperative loops *)
    (* 9 rounds (the last is special) *)
    for i in 1 to 9 do
      (tmp, IInd i :: nil) :: nil <|- AddRoundKey @ [MixColumn @ [ShiftRows @ [SubBytes @ [tmp[i-1]]]], key[i]]
    done;

    (* Last (10th) round (no MixColumn) *)
    (cipher, nil) :: nil <|- AddRoundKey @ [ShiftRows @ [SubBytes @ [tmp[9]]], key[10]]
tel.

Definition prog_tl8 : prog := node_subBytes_single :: nil.
Definition prog_tl7 : prog := node_subbytes :: prog_tl8.
Definition prog_tl6 : prog := node_shift_rows :: prog_tl7.
Definition prog_tl5 : prog := node_times2 :: prog_tl6.
Definition prog_tl4 : prog := node_times3 :: prog_tl5.
Definition prog_tl3 : prog := node_MixColumn_single :: prog_tl4.
Definition prog_tl2 : prog := node_MixColumn :: prog_tl3.
Definition prog_tl : prog := node_AddRoundKey :: prog_tl2.
Definition prog_aes : prog := node_AES :: prog_tl.
