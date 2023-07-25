Require Import String List ZArith.
From Usuba Require Import ident usuba_AST syntax arch.
Open Scope Z_scope.
Definition simeck_box : string := "simeck_box".
Definition ACE_step : string := "ACE_step".
Definition ACE : string := "ACE".
Definition rc : ident := "rc"%string.
Definition Ar : ident := "Ar"%string.
Definition Br : ident := "Br"%string.
Definition Cr : ident := "Cr"%string.
Definition Dr : ident := "Dr"%string.
Definition Er : ident := "Er"%string.
Definition A : ident := "A"%string.
Definition B : ident := "B"%string.
Definition C : ident := "C"%string.
Definition D : ident := "D"%string.
Definition E : ident := "E"%string.
Definition A' : ident := "A'"%string.
Definition B' : ident := "B'"%string.
Definition C' : ident := "C'"%string.
Definition D' : ident := "D'"%string.
Definition E' : ident := "E'"%string.
Definition E'' : ident := "E''"%string.
Definition RC : ident := "RC"%string.
Definition SC : ident := "SC"%string.

Definition node_f := node f args (x:u32) returns (y:u32) vars nil
let
    (y, nil) :: nil <|- ((x <<< 5) & x) xor (x <<< 1)
tel.

Definition node_simeck_box := node simeck_box args input:u32[2], rc:u32 returns (output:u32[2])
vars
    (round:u32[9][2]) :: nil
let
    (round, IInd 0 :: nil) :: nil <|- input;

    for i in 0 to 7 do
      (round, (IInd (Var_e i + 1)%ua_aexpr :: ISlice (Const_e 0 :: Const_e 1 :: nil) :: nil))%ua_var :: nil <|- [f @ [Index round (IInd i :: IInd 0 :: nil)] xor (Index round (IInd i :: IInd 1 :: nil)) xor 0xfffffffe xor ((rc >> i) & 1), (Index round (IInd i :: IInd 0 :: nil))]
    done;

    (output, nil) :: nil <|- round[8]
tel.

Definition node_ACE_step := node ACE_step args A:u32[2],B:u32[2],C:u32[2],D:u32[2],E:u32[2],RC:u32[3],SC:u32[3]
returns Ar:u32[2],Br:u32[2],Cr:u32[2],Dr:u32[2],Er:u32[2]
vars
    (A':u32[2]) :: (B':u32[2]) :: (C':u32[2]) :: (D':u32[2]) :: (E':u32[2]) :: (E'':u32[2]) :: nil
let
    (A', nil) :: nil  <|- simeck_box @ [A,RC[0]];
    (C', nil) :: nil  <|- simeck_box @ [C,RC[1]];
    (E', nil) :: nil  <|- simeck_box @ [E,RC[2]];
    (B', nil) :: nil  <|- B xor C' xor [0,SC[0]] xor [0xffffffff,0xffffff00];
    (D', nil) :: nil  <|- D xor E' xor [0,SC[1]] xor [0xffffffff,0xffffff00];
    (E'', nil) :: nil <|- E' xor A' xor [0,SC[2]] xor [0xffffffff,0xffffff00];
    (Ar, nil) :: (Br, nil) :: (Cr, nil) :: (Dr, nil) :: (Er, nil) :: nil <|- [D', C', A', E'', B']
tel.


Definition node_ACE := node ACE args (input:u32[5][2]) returns (output:u32[5][2])
vars
    (SC:u32[3][16]) ::
    (RC:u32[3][16]) ::
    (tmp:u32[17][5][2]) :: nil
let
    (SC, nil) :: nil <|- [0x50,0x5c,0x91,0x8d,0x53,0x60,0x68,0xe1,0xf6,0x9d,0x40,0x4f,0xbe,0x5b,0xe9,0x7f,
          0x28,0xae,0x48,0xc6,0xa9,0x30,0x34,0x70,0x7b,0xce,0x20,0x27,0x5f,0xad,0x74,0x3f,
          0x14,0x57,0x24,0x63,0x54,0x18,0x9a,0x38,0xbd,0x67,0x10,0x13,0x2f,0xd6,0xba,0x1f];
    (RC, nil) :: nil <|- [0x07,0x0a,0x9b,0xe0,0xd1,0x1a,0x22,0xf7,0x62,0x96,0x71,0xaa,0x2b,0xe9,0xcf,0xb7,
          0x53,0x5d,0x49,0x7f,0xbe,0x1d,0x28,0x6c,0x82,0x47,0x6b,0x88,0xdc,0x8b,0x59,0xc6,
          0x43,0xe4,0x5e,0xcc,0x32,0x4e,0x75,0x25,0xfd,0xf9,0x76,0xa0,0xb0,0x09,0x1e,0xad];

    (tmp, IInd 0 :: nil) :: nil <|- input;

    for i in 0 to 15 do
        (tmp, IInd (i+1)%ua_aexpr :: nil) :: nil <|- ACE_step @ [tmp[i],
                            Index (Var RC) (ISlice (Const_e 0::Const_e 1::Const_e 2::nil) :: IInd i :: nil),
                            Index (Var SC) (ISlice (Const_e 0::Const_e 1::Const_e 2::nil) :: IInd i :: nil)]
    done;

    (output, nil) :: nil <|- tmp[16]
tel.

Definition prog_ace_bs := node_ACE :: node_ACE_step :: node_simeck_box :: node_f :: nil.
