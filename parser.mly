%{
open Ast;;

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a loc =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT
%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token RETURN   /* return */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */

                       

%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE

/* ---------------------------------------------------------------------- */

%start prog
%start const
%start exp_top
%start stmt_top
%type <Ast.exp> exp_top
%type <Ast.stmt> stmt_top
%type <Ast.prog> prog
%type <Ast.fdecl> fdecl 
%type <Ast.exp> exp
%type <Ast.block> block
%type <Ast.const> const
%type <Ast.typ> typ
%type <Ast.stmt> stmt
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(gdecl) EOF  { p }

gdecl:
  | d=vdecl  { Gvdecl d }
  | f=fdecl  { Gfdecl f }

ident:
  | id=IDENT  { loc $startpos $endpos id }

arg:
  t=typ id=ident { (t, id) }

arglist:
    l=separated_list(COMMA, arg)  { l }
    
fdecl:
  | rtyp=rtyp id=ident LPAREN args=arglist RPAREN body=block    { loc $startpos $endpos @@ {rtyp; name=id; args; body} } 

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

vdecl:
    | ty=typ id=ident EQ c=const SEMI
         { let e = loc $startpos(c) $endpos(c) @@ Const(c) in
           loc $startpos $endpos @@ {ty; id; init=e } }

decl:
  | ty=typ id=ident EQ init=exp { loc $startpos $endpos @@ {ty; id; init} }

typ:
  | TINT  { loc $startpos $endpos TInt }

  | r=reft { loc $startpos $endpos @@ TRef r }

reft:
  | TSTRING { loc $startpos $endpos RString }


%inline rtyp:
  | TVOID  { None }
  | t=typ  { Some t } 

const:
  | NULL     { loc $startpos $endpos CNull } 
  | i=INT    { loc $startpos $endpos @@ CInt i }
  | s=STRING { loc $startpos $endpos @@ CStr s } 

%inline bop:
  | PLUS { Add }
  | DASH { Sub }
  | STAR { Mul }
  | EQEQ { Eq }


%inline uop:
  | DASH { Neg }
  | BANG { Lognot }
  | TILDE  { Bitnot }

exp:
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | c=const { loc $startpos $endpos @@ Const c }
  | p=path  { loc $startpos $endpos @@ Path p }

  | LPAREN e=exp RPAREN { e } 

path:
  | id=ident s=suffixpath
    { (loc $startpos(id) $endpos(id) @@ Field(id))::s }                     
  | id=ident LPAREN es=separated_list(COMMA, exp) RPAREN s=suffixpath
    { (loc $startpos(id) $endpos(id) @@ Call(id,es))::s }                     

suffixpath:
  | l=list(accessor) { l }

accessor:
  | LBRACKET e=exp RBRACKET   { loc $startpos $endpos @@ Index(e) }

stmt: 
  | d=decl SEMI           { loc $startpos $endpos @@ Decl(d) }
  | p=path EQ e=exp SEMI  { loc $startpos $endpos @@ Assn(p,e) }
  | p=path SEMI           { loc $startpos $endpos @@ SCall(p) }
  | ifs=if_stmt            { ifs }
  | RETURN SEMI           { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI     { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  { loc $startpos $endpos @@ While(e, b) }


if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
       { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)  { [] }
  | ELSE b=block { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
