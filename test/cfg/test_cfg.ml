open Failure_ssil_analyzer.Cfg

let n = Node.make "root" [
  (Node.make "left" [] []);
  (Node.make "right" [
    (Node.make "right->left" [] [])
  ] [])
] []

let () = print_endline (Node.show (fun fmt -> Format.fprintf fmt "%s") n)

let () = print_endline (string_of_int (Node.length n))

let cfg = CFG.make n

let () = Printf.printf "\n%s\n" (CFG.show (fun fmt -> Format.fprintf fmt "%s") cfg ) 

let () = Printf.printf "\n%s\n" (
  CFG.show_item (fun fmt -> Format.fprintf fmt "%s") 
  (CFG.get cfg 2)
)

let () = print_endline ( ( CFG.succ_of cfg 4) |> List.map (fun x -> string_of_int x) |> String.concat "; ")

