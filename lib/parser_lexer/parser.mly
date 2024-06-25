%{
  open Prelude.Analysis
  open Parser
  open Commands
  open Either

  let annotateCommand command position formula = AnnotatedNode.make command (Commands.make_annotation position.Lexing.pos_lnum position.Lexing.pos_cnum formula)
  let annotateEmptyCommand command position = annotateCommand command position None

  let annotateFormula formula position = AnnotatedNode.make formula (LogicFormulas.make_annotation position.Lexing.pos_lnum position.Lexing.pos_cnum)

  (* (b?; then) + (¬b?; else) *)
  let rewriteIfThenElse overall_pos _guard _guard_pos _then _then_pos _else _else_pos formula =
    let b_guard = HeapAtomicCommand.Guard(_guard) in
    let b_guard_atom = annotateEmptyCommand b_guard _guard_pos in
    let b_guard_command = annotateEmptyCommand (HeapRegularCommand.Command(b_guard_atom)) _guard_pos in
    let b_neg_guard = HeapAtomicCommand.Guard(annotateEmptyCommand (BooleanExpression.Not(_guard)) _guard_pos) in
    let b_neg_guard_atom = annotateEmptyCommand b_neg_guard _guard_pos in
    let b_neg_guard_command = annotateEmptyCommand (HeapRegularCommand.Command(b_neg_guard_atom)) _guard_pos in
    let then_command = annotateEmptyCommand (HeapRegularCommand.Sequence(b_guard_command, _then)) _then_pos in
    let else_command = annotateEmptyCommand (HeapRegularCommand.Sequence(b_neg_guard_command, _else)) _else_pos in
    annotateCommand (HeapRegularCommand.NondeterministicChoice(then_command, else_command)) overall_pos formula

  (* (b?; body)*; ¬b? *)
  let rewriteWhile overall_pos _guard _guard_pos _body _body_pos formula =
    let b_guard = HeapAtomicCommand.Guard(_guard) in
    let b_guard_atom = annotateEmptyCommand b_guard _guard_pos in
    let b_guard_command = annotateEmptyCommand (HeapRegularCommand.Command(b_guard_atom)) _guard_pos in
    let b_neg_guard = HeapAtomicCommand.Guard(annotateEmptyCommand (BooleanExpression.Not(_guard)) _guard_pos) in
    let b_neg_guard_atom = annotateEmptyCommand b_neg_guard _guard_pos in
    let b_neg_guard_command = annotateEmptyCommand (HeapRegularCommand.Command(b_neg_guard_atom)) _guard_pos in
    let guard_body = annotateEmptyCommand (HeapRegularCommand.Sequence(b_guard_command, _body)) _body_pos in
    let guard_body_star = annotateEmptyCommand (HeapRegularCommand.Star(guard_body)) _body_pos in
    annotateCommand (HeapRegularCommand.Sequence(guard_body_star, b_neg_guard_command)) overall_pos formula

  let negate_formula_arithmetic_expression e =
    match AnnotatedNode.node e with
    | Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Literal i ->
      let synthesized_neg = Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Literal (-i) in
      synthesized_neg
    | _ ->
      let pos = AnnotatedNode.annotation e in
      let zero = AnnotatedNode.make (Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Literal 0) pos in
      let synthesized_neg = Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Operation(Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Minus, zero, e) in
      synthesized_neg

  let negate_command_arithmetic_expression e new_pos =
    match AnnotatedNode.node e with
    | ArithmeticExpression.Literal i ->
      let synthesized_neg = ArithmeticExpression.Literal (-i) in
      annotateEmptyCommand synthesized_neg new_pos
    | _ ->
      let formula = (AnnotatedNode.annotation e).logic_formula in
      let new_e = annotateEmptyCommand (AnnotatedNode.node e) new_pos in
      let zero = annotateEmptyCommand (ArithmeticExpression.Literal 0) new_pos in
      let synthesized_neg = ArithmeticExpression.BinaryOperation(ArithmeticOperation.Minus, zero, new_e) in
      annotateCommand synthesized_neg new_pos formula
%}

%token EqualEqual
%token Skip
%token Alloc
%token Free
%token Semicolon
%token Question
%token NonDet
%token Eof
%token LShift RShift
%token LParen RParen
%token LBracket RBracket
%token LBrace RBrace
%token True
%token False
%token Exists
%token <string> Identifier
%token And Or Emp Arrow Void Not
%token LessThan GreaterThan LessOrEqual GreaterOrEqual Equal NotEqual
%token <int> Integer
%token Plus Minus Times Div Mod
%token Dot
%token If Then Else
%token While

/* precedences */

%nonassoc LOW
%left Or
%left And
%right Not
%left Equal NotEqual
%left LessThan GreaterThan LessOrEqual GreaterOrEqual
%left Plus Minus
%left Times Div Mod
%left Semicolon
%nonassoc HIGH

%start <(Prelude.Analysis.Parser.Commands.t, Prelude.Analysis.Parser.LogicFormulas.t) Either.t> program
%type <Prelude.Analysis.Parser.Commands.t> toplevel_command
%type <Prelude.Analysis.Parser.Commands.t> toplevel_command_noformula
%type <Prelude.Analysis.Parser.Commands.atomic_t> atomic_command
%type <Prelude.Analysis.Parser.Commands.arithmetic_t> arithmetic_expression
%type <Prelude.Analysis.Parser.Commands.boolean_t> boolean_expression
%type <Prelude.Analysis.Parser.Commands.t> sequence
%type <Prelude.Analysis.Parser.Commands.t> nondetchoice
%type <Prelude.Analysis.Parser.Commands.t> star
%type <Prelude.Analysis.Parser.Commands.t> nondetchoice_noformula
%type <Prelude.Analysis.Parser.Commands.t> star_noformula

%type <Prelude.Analysis.Parser.LogicFormulas.t> formula
%type <Prelude.Analysis.Parser.LogicFormulas.t option> option(delimited(LShift, formula, RShift))
%type <Prelude.Analysis.Parser.LogicFormulas.arithmetic_t> arithmetic_expression_of_formula

%%

program:
  | toplevel_command Eof
    { left $1 }
  | LShift formula RShift Eof
    { right $2 }

toplevel_command:
  | atomic_command LShift formula RShift
    { annotateCommand (HeapRegularCommand.Command($1)) $startpos (Some $3) }
  | sequence
    { $1 }
  | nondetchoice
    { $1 }
  | star
    { $1 }
  | If boolean_expression Then toplevel_command_noformula Else toplevel_command_noformula LShift formula RShift
    {
      rewriteIfThenElse $startpos $2 $startpos($2) $4 $startpos($4) $6 $startpos($6) (Some $8)
    }
  | While boolean_expression LBrace toplevel_command RBrace option(delimited(LShift, formula, RShift))
    {
      (* thanks to braces there is no need to avoid sub-commands with formulae *)
      rewriteWhile $startpos $2 $startpos($2) $4 $startpos($4) $6
    }
  | toplevel_command_noformula
    { $1 }
  ;

toplevel_command_noformula:
  | atomic_command
    { annotateEmptyCommand (HeapRegularCommand.Command($1)) $startpos }
  | nondetchoice_noformula
    { $1 }
  | star_noformula
    { $1 }
  | If boolean_expression Then toplevel_command_noformula Else toplevel_command_noformula
    {
      rewriteIfThenElse $startpos $2 $startpos($2) $4 $startpos($4) $6 $startpos($6) None
    } %prec LOW
  | LBrace toplevel_command RBrace
    { $2 }
  ;

atomic_command:
  | Skip
    { annotateEmptyCommand (HeapAtomicCommand.Skip) $startpos }
  | id = Identifier Equal a = arithmetic_expression
    { annotateEmptyCommand (HeapAtomicCommand.Assignment(id, a)) $startpos }
  | id = Identifier Equal NonDet LParen RParen
    { annotateEmptyCommand (HeapAtomicCommand.NonDet(id)) $startpos }
  | b = boolean_expression Question
    { annotateEmptyCommand (HeapAtomicCommand.Guard(b)) $startpos }
  | id = Identifier Equal Alloc LParen RParen
    { annotateEmptyCommand (HeapAtomicCommand.Allocation(id)) $startpos }
  | Free LParen id = Identifier RParen
    { annotateEmptyCommand (HeapAtomicCommand.Free(id)) $startpos }
  | id1 = Identifier Equal LBracket id2 = Identifier RBracket
    { annotateEmptyCommand (HeapAtomicCommand.ReadHeap(id1, id2)) $startpos }
  | LBracket id1 = Identifier RBracket Equal a = arithmetic_expression
    { annotateEmptyCommand (HeapAtomicCommand.WriteHeap(id1, a)) $startpos }
;

arithmetic_expression:
  | Integer
    { annotateEmptyCommand (ArithmeticExpression.Literal($1)) $startpos }
  | id = Identifier
    { annotateEmptyCommand (ArithmeticExpression.Variable(id)) $startpos }
  | a1 = arithmetic_expression o = arithmetic_operator a2 = arithmetic_expression
    { annotateEmptyCommand (ArithmeticExpression.BinaryOperation(o, a1, a2)) $startpos }
  | LParen a = arithmetic_expression RParen
    { a }
  | Minus arithmetic_expression
    { negate_command_arithmetic_expression $2 $startpos }
;

%inline arithmetic_operator:
  | Plus
    { ArithmeticOperation.Plus }
  | Minus
    { ArithmeticOperation.Minus }
  | Times
    { ArithmeticOperation.Times }
  | Div
    { ArithmeticOperation.Division }
  | Mod
    { ArithmeticOperation.Modulo }
;

boolean_expression:
  | True
    { annotateEmptyCommand (BooleanExpression.True) $startpos }
  | False
    { annotateEmptyCommand (BooleanExpression.False) $startpos }
  | Not b = boolean_expression
    { annotateEmptyCommand (BooleanExpression.Not(b)) $startpos }
  | b1 = boolean_expression And b2 = boolean_expression
    { annotateEmptyCommand (BooleanExpression.And(b1, b2)) $startpos }
  | b1 = boolean_expression Or b2 = boolean_expression
    { annotateEmptyCommand (BooleanExpression.Or(b1, b2)) $startpos }
  | a1 = arithmetic_expression c = boolean_comparison_op a2 = arithmetic_expression
    { annotateEmptyCommand (BooleanExpression.Comparison(c, a1, a2)) $startpos }
  | LParen b = boolean_expression RParen
    { b }
;

%inline boolean_comparison_op:
  | EqualEqual
    { BooleanComparison.Equal }
  | NotEqual
    { BooleanComparison.NotEqual }
  | LessThan
    { BooleanComparison.LessThan }
  | LessOrEqual
    { BooleanComparison.LessOrEqual }
  | GreaterThan
    { BooleanComparison.GreaterThan }
  | GreaterOrEqual
    { BooleanComparison.GreaterOrEqual }
;

sequence:
  | toplevel_command Semicolon toplevel_command
    {annotateEmptyCommand (HeapRegularCommand.Sequence($1, $3)) $startpos }
;

nondetchoice:
  | toplevel_command_noformula Plus toplevel_command_noformula LShift formula RShift
    { annotateCommand (HeapRegularCommand.NondeterministicChoice($1, $3)) $startpos (Some $5)}
;

nondetchoice_noformula:
  | toplevel_command_noformula Plus toplevel_command_noformula
    { annotateEmptyCommand (HeapRegularCommand.NondeterministicChoice($1, $3)) $startpos }
;

star:
  | toplevel_command_noformula Times LShift formula RShift
    { annotateCommand (HeapRegularCommand.Star($1)) $startpos (Some $4) }
;

star_noformula:
  | toplevel_command_noformula Times
    { annotateEmptyCommand (HeapRegularCommand.Star($1)) $startpos  }
;

formula:
    | True
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.True) $startpos }
    | False
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.False) $startpos }
    | Exists Identifier Dot formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.Exists($2, $4)) $startpos } %prec HIGH
    | formula And formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.And($1, $3)) $startpos }
    | formula Or formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.Or($1, $3)) $startpos }
    | arithmetic_expression_of_formula binary_comparison_of_formula arithmetic_expression_of_formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.Comparison($2, $1, $3)) $startpos }
    | Emp
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.EmptyHeap) $startpos }
    | Identifier Arrow arithmetic_expression_of_formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.Allocation($1, $3)) $startpos } %prec LOW
    | Identifier Void
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.NonAllocated($1)) $startpos }
    | formula Times formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.Formula.AndSeparately($1, $3)) $startpos }
    | LParen formula RParen
      { $2 }
    ;

arithmetic_expression_of_formula:
    | Integer
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Literal($1)) $startpos }
    | Identifier
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Variable($1)) $startpos }
    | arithmetic_expression_of_formula binary_operator_of_formula arithmetic_expression_of_formula
      { annotateFormula (Prelude.Analysis.Parser.LogicFormulas.ArithmeticExpression.Operation($2, $1, $3)) $startpos }
    | LParen arithmetic_expression_of_formula RParen
      { $2 }
    | Minus arithmetic_expression_of_formula
      { annotateFormula (negate_formula_arithmetic_expression $2) $startpos }

%inline binary_comparison_of_formula:
  | LessThan { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.LessThan }
  | GreaterThan { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.GreaterThan }
  | LessOrEqual { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.LessOrEqual }
  | GreaterOrEqual { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.GreaterOrEqual }
  | Equal { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.Equals }
  | NotEqual { Prelude.Analysis.Parser.LogicFormulas.BinaryComparison.NotEquals }
  ;

%inline binary_operator_of_formula:
  | Plus  { Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Plus }
  | Minus { Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Minus }
  | Times { Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Times }
  | Div   { Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Division }
  | Mod   { Prelude.Analysis.Parser.LogicFormulas.BinaryOperator.Modulo }
  ;