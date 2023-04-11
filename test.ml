

let rec gen_bin_list n =
  if 0 = n
  then []
  else (if Random.int 2 = 0 then O else S O)::gen_bin_list (n - 1)

let test_aes =
  let l = gen_bin_list (12 * 128) in
  prog_sem default_arch prog_aes None [CoIR (DirB, l, None)]

let () = match test_aes with
  | None -> print_endline "Failure AES"
  | Some _ -> print_endline "Success AES"
