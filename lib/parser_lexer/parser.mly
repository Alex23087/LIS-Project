%{
  open Prelude.Ast.Commands

  let annotateCommand command position formula = Prelude.Ast.Commands.annotate_parser command position.Lexing.pos_lnum position.Lexing.pos_cnum formula
  let annotateEmptyCommand command position = annotateCommand command position None

  let annotateFormula formula position = Prelude.Ast.LogicFormulas.annotate_parser formula position.Lexing.pos_lnum position.Lexing.pos_cnum
%}

/* commands */
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token EQ
%token EQEQ
%token NEQ
%token LT
%token LE
%token GT
%token GE
%token AND
%token OR
%token NOT
%token TRUE
%token FALSE
%token SKIP
%token ALLOC
%token FREE
%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN
%token SEMICOLON
%token QUESTION
%token <int> INT
%token <string> IDENTIFIER
%token NONDET
%token STAR
%token EOF

/** formulas */
%token True
%token False
%token Exists
%token <string> Identifier
%token And Or Star Emp Arrow Void
%token LTf GTf LEf GEf EQf NEf
%token <int> Integer
%token Plus Minus Times Div Mod

/* precedences */

/* commands */
%nonassoc SEMICOLON
%nonassoc EQ
%left OR
%left AND
%right NOT
%left PLUS MINUS
%left TIMES DIV MOD
%left STAR

/* formulas */
%left Or
%left And
%left Star
%left Plus Minus
%left Times Div Mod
%nonassoc PREC

%start <Prelude.Ast.Commands.HeapRegularCommand.t> program
%type <Prelude.Ast.Commands.HeapRegularCommand.t> toplevel_command
%type <Prelude.Ast.Commands.HeapRegularCommand.t> toplevel_command_nof
%type <Prelude.Ast.Commands.HeapAtomicCommand.t> atomic_command
%type <Prelude.Ast.Commands.ArithmeticExpression.t> arithmetic_expression
%type <Prelude.Ast.Commands.BooleanExpression.t> boolean_expression
%type <Prelude.Ast.Commands.HeapRegularCommand.t> sequence
%type <Prelude.Ast.Commands.HeapRegularCommand.t> nondetchoice
%type <Prelude.Ast.Commands.HeapRegularCommand.t> star
%type <Prelude.Ast.Commands.HeapRegularCommand.t> nondetchoice_nof
%type <Prelude.Ast.Commands.HeapRegularCommand.t> star_nof

%type <Prelude.Ast.LogicFormulas.Formula.t> formula
%type <Prelude.Ast.LogicFormulas.ArithmeticExpression.t> arithmetic_expression_f

%%

program:
  | toplevel_command EOF
    { $1 }
  | formula EOF
    { annotateCommand (HeapRegularCommand.Command(annotateEmptyCommand HeapAtomicCommand.Skip $startpos)) $startpos (Some $1) }

toplevel_command:
  | atomic_command formula
    { annotateCommand (HeapRegularCommand.Command($1)) $startpos (Some $2) }
  | sequence
    { $1 }
  | nondetchoice
    { $1 }
  | star
    { $1 }
  | toplevel_command_nof
    { $1 }
  ;

toplevel_command_nof:
  | atomic_command
    { annotateEmptyCommand (HeapRegularCommand.Command($1)) $startpos }
  | nondetchoice_nof
    { $1 }
  | star_nof
    { $1 }
;

atomic_command:
  | SKIP
    { annotateEmptyCommand (HeapAtomicCommand.Skip) $startpos }
  | id = IDENTIFIER EQ a = arithmetic_expression
    { annotateEmptyCommand (HeapAtomicCommand.Assignment(id, a)) $startpos }
  | id = IDENTIFIER NONDET
    { annotateEmptyCommand (HeapAtomicCommand.NonDet(id)) $startpos }
  | b = boolean_expression QUESTION
    { annotateEmptyCommand (HeapAtomicCommand.Guard(b)) $startpos }
  | id = IDENTIFIER EQ ALLOC
    { annotateEmptyCommand (HeapAtomicCommand.Allocation(id)) $startpos }
  | FREE LPAREN id = IDENTIFIER RPAREN
    { annotateEmptyCommand (HeapAtomicCommand.Free(id)) $startpos }
  | id1 = IDENTIFIER EQ LBRACKET id2 = IDENTIFIER RBRACKET
    { annotateEmptyCommand (HeapAtomicCommand.ReadHeap(id1, id2)) $startpos }
  | LBRACKET id1 = IDENTIFIER RBRACKET EQ a = arithmetic_expression
    { annotateEmptyCommand (HeapAtomicCommand.WriteHeap(id1, a)) $startpos }
;

arithmetic_expression:
  | INT
    { annotateEmptyCommand (ArithmeticExpression.Literal($1)) $startpos }
  | id = IDENTIFIER
    { annotateEmptyCommand (ArithmeticExpression.Variable(id)) $startpos }
  | a1 = arithmetic_expression o = arithmetic_operator a2 = arithmetic_expression
    { annotateEmptyCommand (ArithmeticExpression.BinaryOperation(o, a1, a2)) $startpos }
;

%inline arithmetic_operator:
  | PLUS
    { ArithmeticOperation.Plus }
  | MINUS
    { ArithmeticOperation.Minus }
  | TIMES
    { ArithmeticOperation.Times }
  | DIV
    { ArithmeticOperation.Division }
  | MOD
    { ArithmeticOperation.Modulo }
;

boolean_expression:
  | TRUE
    { annotateEmptyCommand (BooleanExpression.True) $startpos }
  | FALSE
    { annotateEmptyCommand (BooleanExpression.False) $startpos }
  | NOT b = boolean_expression
    { annotateEmptyCommand (BooleanExpression.Not(b)) $startpos }
  | b1 = boolean_expression AND b2 = boolean_expression
    { annotateEmptyCommand (BooleanExpression.And(b1, b2)) $startpos }
  | b1 = boolean_expression OR b2 = boolean_expression
    { annotateEmptyCommand (BooleanExpression.Or(b1, b2)) $startpos }
  | a1 = arithmetic_expression c = boolean_comparison_op a2 = arithmetic_expression
    { annotateEmptyCommand (BooleanExpression.Comparison(c, a1, a2)) $startpos }
;

%inline boolean_comparison_op:
  | EQEQ
    { BooleanComparison.Equal }
  | NEQ
    { BooleanComparison.NotEqual }
  | LT
    { BooleanComparison.LessThan }
  | LE
    { BooleanComparison.LessOrEqual }
  | GT
    { BooleanComparison.GreaterThan }
  | GE
    { BooleanComparison.GreaterOrEqual }
;

sequence:
  | toplevel_command SEMICOLON toplevel_command
    {annotateEmptyCommand (HeapRegularCommand.Sequence($1, $3)) $startpos }
;

nondetchoice:
  | toplevel_command_nof PLUS toplevel_command_nof formula
    { annotateCommand (HeapRegularCommand.NondeterministicChoice($1, $3)) $startpos (Some $4)}
;

nondetchoice_nof:
  | toplevel_command_nof PLUS toplevel_command_nof
    { annotateEmptyCommand (HeapRegularCommand.NondeterministicChoice($1, $3)) $startpos }
;

star:
  | toplevel_command_nof STAR formula
    { annotateCommand (HeapRegularCommand.Star($1)) $startpos (Some $3) }
;

star_nof:
  | toplevel_command_nof STAR
    { annotateEmptyCommand (HeapRegularCommand.Star($1)) $startpos  }
;

formula:
    | True
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.True) $startpos }
    | False
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.False) $startpos }
    | Exists Identifier formula
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.Exists($2, $3)) $startpos } %prec PREC
    | formula And formula
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.And($1, $3)) $startpos }
    | formula Or formula
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.Or($1, $3)) $startpos }
    | arithmetic_expression_f BinaryComparison arithmetic_expression_f
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.Comparison($2, $1, $3)) $startpos }
    | Emp
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.EmptyHeap) $startpos }
    | Identifier Arrow arithmetic_expression_f
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.Allocation($1, $3)) $startpos }
    | Identifier Void
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.NonAllocated($1)) $startpos }
    | formula Star formula
      { annotateFormula (Prelude.Ast.LogicFormulas.Formula.AndSeparately($1, $3)) $startpos }
    ;

arithmetic_expression_f:
    | Integer
      { annotateFormula (Prelude.Ast.LogicFormulas.ArithmeticExpression.Literal($1)) $startpos }
    | Identifier
      { annotateFormula (Prelude.Ast.LogicFormulas.ArithmeticExpression.Variable($1)) $startpos }
    | arithmetic_expression_f BinaryOperator arithmetic_expression_f
      { annotateFormula (Prelude.Ast.LogicFormulas.ArithmeticExpression.Operation($2, $1, $3)) $startpos }

%inline BinaryComparison:
  | LTf { Prelude.Ast.LogicFormulas.BinaryComparison.LessThan }
  | GTf { Prelude.Ast.LogicFormulas.BinaryComparison.GreaterThan }
  | LEf { Prelude.Ast.LogicFormulas.BinaryComparison.LessOrEqual }
  | GEf { Prelude.Ast.LogicFormulas.BinaryComparison.GreaterOrEqual }
  | EQf { Prelude.Ast.LogicFormulas.BinaryComparison.Equals }
  | NEf { Prelude.Ast.LogicFormulas.BinaryComparison.NotEquals }
  ;

%inline BinaryOperator:
  | Plus  { Prelude.Ast.LogicFormulas.BinaryOperator.Plus }
  | Minus { Prelude.Ast.LogicFormulas.BinaryOperator.Minus }
  | Times { Prelude.Ast.LogicFormulas.BinaryOperator.Times }
  | Div   { Prelude.Ast.LogicFormulas.BinaryOperator.Division }
  | Mod   { Prelude.Ast.LogicFormulas.BinaryOperator.Modulo }
  ;