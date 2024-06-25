let unwrap_option opt message =
  match opt with
  | Some(x) -> x
  | None -> raise (Failure message)
  
(* https://stackoverflow.com/a/10893700 *)
let list_cartesian l l' =
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)