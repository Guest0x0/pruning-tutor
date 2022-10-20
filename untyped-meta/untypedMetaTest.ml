
open UntypedMeta

let expr_of_string label src =
    let lexbuf = Lexing.from_string src in
    Lexing.set_filename lexbuf label;
    Parser.single_expr Lexer.token lexbuf


let tests = ref []

let run_test () =
    let total  = List.length !tests in
    let passed = ref 0 in
    Format.printf "@[<v>";
    List.rev !tests |> List.iter begin fun (label, expected, src) ->
        MetaContext.reset ();
        let expr = expr_of_string label src in
        let result =
            try ignore (Typecheck.infer Typecheck.empty_ctx expr); None with
              Failure msg -> Some msg
        in
        let pp_result fmt = function
            | None     -> Format.fprintf fmt "well typed"
            | Some msg -> Format.fprintf fmt "error: %s" msg
        in
        if result = expected
        then begin
            incr passed;
            Format.printf "test %s passed@ " label
        end
        else begin
            Format.printf "test %s failed:@ " label;
            Format.printf "@[<v2>expected:@ %a@]@ " pp_result expected;
            Format.printf "@[<v2>actual:@ %a@]@ " pp_result result;
        end
    end;
    Format.printf "summary: %d of %d tests passed@ " !passed total;
    Format.printf "@]";
    if !passed <> total then
        failwith "test failed"

let register_test label expected src =
    tests := (label, expected, src) :: !tests
;;



register_test "basic" None "
fun (A : Type) (B : A -> Type) (f : forall (a : A) -> B a) (a : A) -> f a
" ;;

register_test "hole.infer" None "
fun (A : Type) (f : A -> A) (a : _) -> f a
" ;;

register_test "hole.check" None "
fun (A : Type) (B : A -> Type) (f : forall (a : A) -> B a) (a0 : A) ->
    (f _ : B a0)
" ;;


register_test "unify.context.1" None "
fun (A : Type) ->
    let M = _ : Type in
    fun (a : A) ->
        unify M A
" ;;

register_test "unify.context.2" (Some "variable may escape its scope") "
fun (A : Type) ->
    let M = _ : A in
    fun (a : A) ->
        unify M a
" ;;


register_test "unify.app.1" None "
let f = _ : (Type -> Type) in
fun (A : Type) ->
    unify (f A) A
" ;;

register_test "unify.app.2" None "
fun (A : Type) ->
    let f = _ : (A -> (A -> Type) -> Type) in
    fun (B : A -> Type) (a0 : A) ->
        unify (f a0 B) (B a0)
" ;;


register_test "unify.let.1" None "
fun (A : Type) ->
    let T = A in
    let M = _ : Type in
    unify M T
" ;;

register_test "unify.let.2" None "
fun (A : Type) ->
    let M = _ : Type in
    let T = A in
    unify M T
" ;;


let _ = run_test ()
