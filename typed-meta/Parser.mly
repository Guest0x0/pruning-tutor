%{
open Syntax
open Surface
%}

%token TOK_EOF
%token TOK_LPAREN TOK_RPAREN TOK_LBRACE TOK_RBRACE
%token TOK_MINUS_GT
%token TOK_EQ
%token TOK_COLON
%token TOK_UNDERSCORE

%token<string> TOK_NAME
%token<int   > TOK_INT
%token TOK_KW_TYPE TOK_KW_FORALL
%token TOK_KW_FUN TOK_KW_LET TOK_KW_IN
%token TOK_KW_UNIFY



%right    TOK_MINUS_GT
%left     TOK_COLON


%type<Syntax.Surface.expr> single_expr
%start single_expr

%%

single_expr :
    | expr TOK_EOF { $1 }
;

expr :
    | binop_expr
        { $1 }

    | TOK_KW_LET TOK_NAME TOK_EQ expr TOK_KW_IN expr
        { Let($2, $4, $6) }

    | TOK_KW_FORALL param_list TOK_MINUS_GT expr
        { List.fold_right (fun (name, typ) body -> TyFun(name, typ, body)) $2 $4 }

    | binop_expr TOK_MINUS_GT expr
        { TyFun("", $1, $3) }

    | TOK_KW_FUN param_list_opt_ann TOK_MINUS_GT expr
        { List.fold_right (fun (name, typ) body -> Fun(name, typ, body)) $2 $4 }

    | error
        { failwith "expecting expression" }
;

binop_expr:
    | app_expr
        { $1 }

    | TOK_KW_UNIFY atom_expr atom_expr
        { Unify($2, $3) }

    | binop_expr TOK_COLON binop_expr
        { Ann($1, $3) }
;

app_expr:
    | atom_expr
        { $1 }

    | app_expr atom_expr
        { App($1, $2) }
;

atom_expr :
    | TOK_LPAREN expr TOK_RPAREN
        { $2 }

    | TOK_NAME
        { Var $1 }

    | TOK_KW_TYPE
        { Type }

    | TOK_UNDERSCORE
        { Hole }
;


param_list :
    | param_decl
        { $1 }
    | param_decl param_list
        { $1 @ $2 }
    | error
        { failwith "expected function parameter" }
;


param_list_opt_ann :
    | param_decl_opt_ann
        { $1 }
    | param_decl_opt_ann param_list_opt_ann
        { $1 @ $2 }
    | error
        { failwith "expected function parameter" }
;



param_decl :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, $4)) $2 }
;

param_decl_opt_ann :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, Some $4)) $2 }
    | TOK_NAME
        { [$1, None] }
;

name_list_nonempty :
    | TOK_NAME                    { [$1] }
    | TOK_NAME name_list_nonempty { $1 :: $2 }
;
