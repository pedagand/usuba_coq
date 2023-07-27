
let rec to_nat n =
  if n = 0 then O
  else S (to_nat (n - 1))

let rec gen_zeros n =
  if 0 = n
  then []
  else Z.of_nat O::gen_zeros (n - 1)

let rec gen_bin_list n =
  if 0 = n
  then []
  else (if Random.int 2 = 0 then Z.of_nat O else Z.of_nat (S O))::gen_bin_list (n - 1)

let bit_list len' n =
  assert (n < 1 lsl len');
  let rec aux len = 
    if len = 0
    then ([], n)
    else
      let (tl, n') = aux (len - 1) in
      (Z.of_nat (to_nat (n' mod 2))::tl, n' / 2)
  in fst (aux len')

let convert (a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33) =
  [a00; a10; a20; a30; a01; a11; a21; a31; a02; a12; a22; a32; a03; a13; a23; a33]
  |> List.map (fun i -> (*List.rev*) (bit_list 8 i))
  |> List.flatten


let () =
    let input_raw = (0x19, 0xa0, 0x9a, 0xe9, 0x3d, 0xf4, 0xc6, 0xf8, 0xe3, 0xe2, 0x8d, 0x48, 0xbe, 0x2b, 0x2a, 0x08) in
    let input = convert input_raw in
    let out_raw   = (0xd4, 0xe0, 0xb8, 0x1e, 0x27, 0xbf, 0xb4, 0x41, 0x11, 0x98, 0x5d, 0x52, 0xae, 0xf1, 0xe5, 0x30) in
    let out = convert out_raw in
    match prog_sem default_arch prog_tl7 None [CoIR (DirB, input, [length input])] with
    | Some [CoIR (DirB, l, _)] when List.length l = List.length out ->
      if l <> out
      then
        begin
          for i = 0 to 15 do
            let k = ref 0 in
            for j = 0 to 7 do
              k := !k + Big_int_Z.int_of_big_int (List.nth l (i * 8 + j)) lsl (7 - j)
            done;
            Printf.printf "%X " !k;
          done;
          print_newline ();
          for i = 0 to 15 do
            let k = ref 0 in
            for j = 0 to 7 do
              k := !k + Big_int_Z.int_of_big_int (List.nth out (i * 8 + j)) lsl (7 - j)
            done;
            Printf.printf "%X " !k;
          done;
          print_newline ();
        end;
      assert (l = out)
    | Some _ -> assert false
    | None -> assert false;;

let () =
  let input_raw = (0xd4, 0xe0, 0xb8, 0x1e, 0x27, 0xbf, 0xb4, 0x41, 0x11, 0x98, 0x5d, 0x52, 0xae, 0xf1, 0xe5, 0x30) in
  let input = convert input_raw in
  let out_raw  = (0xd4, 0xe0, 0xb8, 0x1e, 0xbf, 0xb4, 0x41, 0x27, 0x5d, 0x52, 0x11, 0x98, 0x30, 0xae, 0xf1, 0xe5) in
  let out = convert out_raw in
  match prog_sem default_arch prog_tl6 None [CoIR (DirB, input, [length input])] with
  | Some [CoIR (DirB, l, _)] when List.length l = List.length out ->
    assert (l = out)
  | _ -> assert false;;

let () =
    let input = bit_list 8 0x57 in
    let out = bit_list 8 0xae in
    match prog_sem default_arch prog_tl5 None [CoIR (DirB, input, [length input])] with
    | Some [CoIR (DirB, l, _)] when List.length l = List.length out ->
      assert (l = out)
    | _ -> assert false;;

let () =
  let input = [0xd4; 0xbf; 0x5d; 0x30] |> List.map (bit_list 8) |> List.flatten in
  let out = [0x04; 0x66; 0x81; 0xe5] |> List.map (bit_list 8) |> List.flatten in
  match prog_sem default_arch prog_tl3 None [CoIR (DirB, input, [length input])] with
  | Some [CoIR (DirB, l, _)] when List.length l = List.length out ->
    for i = 0 to 3 do
      let k = ref 0 in
      for j = 0 to 7 do
        k := !k + Big_int_Z.int_of_big_int (List.nth l (i * 8 + j)) lsl (7 - j)
      done;
      Printf.printf "%X " !k;
    done;
    print_newline ();
    for i = 0 to 3 do
      let k = ref 0 in
      for j = 0 to 7 do
        k := !k + Big_int_Z.int_of_big_int (List.nth out (i * 8 + j)) lsl (7 - j)
      done;
      Printf.printf "%X " !k;
    done;
    print_newline ();
    assert (l = out)
  | _ -> assert false;;

let () =
  let input_raw = (0xd4, 0xe0, 0xb8, 0x1e, 0xbf, 0xb4, 0x41, 0x27, 0x5d, 0x52, 0x11, 0x98, 0x30, 0xae, 0xf1, 0xe5) in
  let input = convert input_raw in
  let out_raw   = (
    0x04, 0xe0, 0x48, 0x28,
    0x66, 0xcb, 0xf8, 0x06,
    0x81, 0x19, 0xd3, 0x26,
    0xe5, 0x9a, 0x7a, 0x4c
  ) in
  let out = convert out_raw in
  match prog_sem default_arch prog_tl2 None [CoIR (DirB, input, [length input])] with
  | Some [CoIR (DirB, l, _)] when List.length l = List.length out ->
    for i = 0 to 15 do
      let k = ref 0 in
      for j = 0 to 7 do
        k := !k + Big_int_Z.int_of_big_int (List.nth l (i * 8 + j)) lsl (7 - j)
      done;
      Printf.printf "%X " !k;
    done;
    print_newline ();
    for i = 0 to 15 do
      let k = ref 0 in
      for j = 0 to 7 do
        k := !k + Big_int_Z.int_of_big_int (List.nth out (i * 8 + j)) lsl (7 - j)
      done;
      Printf.printf "%X " !k;
    done;
    print_newline ();
    assert (l = out)
  | _ -> assert false;;


let test_aes =
  let input = (0x32, 0x88, 0x31, 0xe0, 0x43, 0x5a, 0x31, 0x37, 0xf6, 0x30, 0x98, 0x07, 0xa8, 0x8d, 0xa2, 0x34) |> convert  in
  let keys = [
    (0x2b, 0x28, 0xab, 0x09, 0x7e, 0xae, 0xf7, 0xcf, 0x15, 0xd2, 0x15, 0x4f, 0x16, 0xa6, 0x88, 0x3c);
    (0xa0, 0x88, 0x23, 0x2a, 0xfa, 0x54, 0xa3, 0x6c, 0xfe, 0x2c, 0x39, 0x76, 0x17, 0xb1, 0x39, 0x05);
    (0xf2, 0x7a, 0x59, 0x73, 0xc2, 0x96, 0x35, 0x59, 0x95, 0xb9, 0x80, 0xf6, 0xf2, 0x43, 0x7a, 0x7f);
    (0x3d, 0x47, 0x1e, 0x6d, 0x80, 0x16, 0x23, 0x7a, 0x47, 0xfe, 0x7e, 0x88, 0x7d, 0x3e, 0x44, 0x3b);
    (0xef, 0xa8, 0xb6, 0xdb, 0x44, 0x52, 0x71, 0x0b, 0xa5, 0x5b, 0x25, 0xad, 0x41, 0x7f, 0x3b, 0x00);
    (0xd4, 0x7c, 0xca, 0x11, 0xd1, 0x83, 0xf2, 0xf9, 0xc6, 0x9d, 0xb8, 0x15, 0xf8, 0x87, 0xbc, 0xbc);
    (0x6d, 0x11, 0xdb, 0xca, 0x88, 0x0b, 0xf9, 0x00, 0xa3, 0x3e, 0x86, 0x93, 0x7a, 0xfd, 0x41, 0xfd);
    (0x4e, 0x5f, 0x84, 0x4e, 0x54, 0x5f, 0xa6, 0xa6, 0xf7, 0xc9, 0x4f, 0xdc, 0x0e, 0xf3, 0xb2, 0x4f);
    (0xea, 0xb5, 0x31, 0x7f, 0xd2, 0x8d, 0x2b, 0x8d, 0x73, 0xba, 0xf5, 0x29, 0x21, 0xd2, 0x60, 0x2f);
    (0xac, 0x19, 0x28, 0x57, 0x77, 0xfa, 0xd1, 0x5c, 0x66, 0xdc, 0x29, 0x00, 0xf3, 0x21, 0x41, 0x6e);
    (0xd0, 0xc9, 0xe1, 0xb6, 0x14, 0xee, 0x3f, 0x63, 0xf9, 0x25, 0x0c, 0x0c, 0xa8, 0x89, 0xc8, 0xa6)
  ] |> List.map convert |> List.flatten in
  prog_sem default_arch prog_aes None [CoIR (DirB, input @ keys, [length (input @ keys)])]

let () = match test_aes with
  | None -> print_endline "Failure AES"
  | Some [CoIR (DirB, l, _)] when List.length l = 128 ->
    let l_expected = (0x39, 0x02, 0xdc, 0x19, 0x25, 0xdc, 0x11, 0x6a, 0x84, 0x09, 0x85, 0x0b, 0x1d, 0xfb, 0x97, 0x32)
      |> convert in
    List.iter (fun i -> print_int (Big_int_Z.int_of_big_int i)) l;
    print_newline ();
    List.iter (fun i -> print_int (Big_int_Z.int_of_big_int i)) l_expected;
    print_newline ();
    assert(l = l_expected);
    print_endline "Success AES"
  | Some _ -> print_endline "Weird AES"

let test_ace =
  let l = gen_zeros (2 * 5) in
  prog_sem default_arch prog_ace_bs None [CoIR (DirV (to_nat 32), l, [length l])]

let () = match test_ace with
  | None -> print_endline "Failure ACE"
  | Some [CoIR (DirV s, l, _)] when s = to_nat 32 && List.length l = 10 ->
    let l = List.map Big_int_Z.int_of_big_int l in
    let l2 = [
      0x5C93691A; 0xD5060935;
      0xDC19CE94; 0x7EAD550D;
      0xAC12BEE1; 0xA64B670E;
      0xF516E8BE; 0x1DFA60DA;
      0x409892A4; 0xE4CCBC15]
    in
    List.iter2 (fun i j -> assert (i = j)) l l2;
    print_endline "Success ACE (null test vector tested)"
  | Some _ -> print_endline "Weird ACE"
