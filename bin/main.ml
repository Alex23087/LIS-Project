open In_channel
open Out_channel
open Failure_ssil_analyzer.Cfg
open Failure_ssil_analyzer.Parserlexer
open Failure_ssil_analyzer.Analysis
open Failure_ssil_analyzer.Analysis.DataStructures.Analysis

(* Command Line Arguments *)
let usage_message = "Usage: " ^ Sys.argv.(0) ^ " [-v|--verbose] [-t <traces file>] [--debug] <input file> [-o <output file>]"

let verbose = ref false
let debug = ref false
let input_file = ref ""
let output_file = ref ""
let traces_file = ref ""

let anon_fun filename =
  input_file := filename

let speclist = [
  ("-v", Arg.Set verbose, "Verbose - Print processing status to stdout");
  ("--verbose", Arg.Set verbose, "");
  ("-o", Arg.Set_string output_file, "Set output file");
  ("-t", Arg.Set_string traces_file, "Set traces file - Save analysis traces to file");
  ("--debug", Arg.Set debug, "Debug - Print debug informations between steps")
]

(* Utility Functions *)
let if_verbose fn = if (!verbose || !debug) then fn ()
let if_debug fn = if (!debug) then fn ()
let fail message = prerr_string message; exit(1)

let build_final_formula final_states =
  let final_formula =
    List.fold_left
    (fun acc x ->
      let formula = Prelude.get_last_block_precondition x |> Option.get in
      Prelude.disjunction_of_normalized_formulas acc formula
    )
    (NormalForm.make_from_formula (NormalForm.Formula.False))
    final_states
  in
  Prelude.simplify_formula final_formula

let parse_input source =
  let handle_error source lexeme_pos msg =
    let lines = String.split_on_char '\n' source in
    let line = List.nth lines (lexeme_pos.Location.line - 1) in
    let prefix = String.make (lexeme_pos.Location.start_column - 1) ' ' in
    let middle =
      String.make
        (lexeme_pos.Location.end_column - lexeme_pos.Location.start_column + 1)
        '^'
    in
    Printf.sprintf "Error: Syntax error at line %d - column (start, end): (%d,%d).\n%s\n%s%s\n*** %s\n\n"
      lexeme_pos.Location.line lexeme_pos.Location.start_column lexeme_pos.Location.end_column line prefix middle msg
  in

  let lexbuf = Lexing.from_string ~with_positions:true source in
  try
    lexbuf
    |> Parsing.parse Lexer.lex
    |> fun ast -> match Either.find_left ast with
      | Some command -> command
      | None -> fail ""
  with Lexer.Lexing_error (pos, msg) | Parsing.Syntax_error (pos, msg) ->
    fail (handle_error source pos msg)

(* Main Function *)
let () =
  Arg.parse speclist anon_fun usage_message;
  if String.equal !input_file "" then (
    print_endline usage_message;
    exit(0)
  );

  if_verbose (fun _ -> print_endline ("[0] Reading input file: " ^ !input_file));
  let file = (In_channel.open_gen [Open_rdonly] 0 !input_file) in
  let input = input_all file in 
  In_channel.close file;
  if String.equal input "" then
    fail ("Error: empty input file\n" ^ usage_message);
  
  (* Parsing *)
  if_verbose (fun _ -> print_endline ("[1] Parsing input..."));
  let ast = parse_input input in
      if_debug (fun _ ->
        print_endline "[*] Debug AST: ";
        DataStructures.Parser.Commands.show ast |> print_endline
      );

  (* AST Validation *)
  if_verbose (fun _ -> print_endline ("[2] Program validation..."));
  if Prelude.validate_ast ast |> not then (
    print_endline "The given program violates some semantic rules...";
    exit(1)
  );

  (* Cfg building *)
  if_verbose (fun _ -> print_endline ("[3] Constructing Control Flow Graph..."));
  let nodes = Converter.convert ~keep_structure:false ast in
      if_debug (fun _ ->
        print_endline "[*] Debug Nodes structure: ";
        Node.to_string nodes Prelude.Print.Parser.show_atomic_list |> print_endline
      );

  let cfg = Cfg.make nodes in
  let cfg = Cfg.map cfg Prelude.from_ast_commands in
      if_debug (fun _ ->
        print_endline "[*] Debug CFG: ";
        Cfg.to_string cfg CfgBlock.show |> print_endline
      );

  (* Analysis Step *)
  if_verbose (fun _ -> print_endline ("[4] Analysis..."));
  let final_states = CfgAnalysis.analyze_program cfg in
      if_debug (fun _ ->
        print_endline "[*] Debug analysis final states before reconciliation: ";
        List.iteri (fun i x -> x |> Prelude.get_last_block_precondition |> Option.get
          |> Prelude.Print.Analysis.pretty_print_normal_form |> (fun x -> "[" ^ string_of_int i ^ "] " ^ x)
          |> print_endline
        ) final_states
      );

  if not (String.equal !traces_file "") then (
    if_verbose (fun _ -> print_endline ("[5] Dump of analysis traces to file: " ^ !traces_file));
    let file = (Out_channel.open_gen [Open_wronly; Open_creat; Open_trunc] 0440 !traces_file) in
    List.iteri (fun i final_state -> 
      ("Trace " ^ string_of_int i ^ ": \n") |> output_string file;
      (Prelude.Print.Analysis.pretty_print_analysis_trace final_state.trace) |> output_string file;
      "\n\n" |> output_string file;
    ) final_states;
    Out_channel.close file;
  );

  let final_formula = final_states |> build_final_formula in
  print_endline (final_formula |> Prelude.Print.Analysis.pretty_print_normal_form);

  if not (String.equal !output_file "") then (
    if_verbose (fun _ -> print_endline ("[5] Writing output to file: " ^ !output_file));
    let file = Out_channel.open_gen [Open_wronly; Open_creat; Open_trunc] 0440 !output_file in
    final_formula |> Prelude.Print.Analysis.pretty_print_normal_form |> output_string file;
    Out_channel.close file;
  );

  ()
