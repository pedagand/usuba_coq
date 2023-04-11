open Semantic_aes

let rec to_nat n =
  if n = 0 then O
  else S (to_nat (n - 1))

let rec gen_bin_list n =
  if 0 = n
  then []
  else (if Random.int 2 = 0 then Z.of_nat O else Z.of_nat (S O))::gen_bin_list (n - 1)

let test_aes =
  let l = gen_bin_list (12 * 128) in
  prog_sem default_arch prog_aes None [CoIR (DirB, l, None)]

let () = match test_aes with
  | None -> print_endline "Failure AES"
  | Some _ -> print_endline "Success AES"

let test_ace =
  let l = gen_bin_list (2 * 5) in
  prog_sem default_arch prog_ace_bs None [CoIR (DirV (to_nat 32), l, None)]

let () = match test_ace with
  | None -> print_endline "Failure ACE"
  | Some _ -> print_endline "Success ACE"
