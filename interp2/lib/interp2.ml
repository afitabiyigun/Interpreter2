include Utils

type ctxt = ty Env.t

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let rec curryFun (args : (string * ty) list)  (body: expr) : expr = 
(*anonymous functions with multiple args are nested functions with single args*)
(*we only desugar the body sfexpr in desugar_expr before calling curryFun*)
(* fun (x : int) (y : int) -> x + y becomes Fun("x", int, Fun("y", int, Bop(Add, Var "x", Var "y"))) *)
  match args with
  | [] -> body
  | (arg_name, arg_ty)::rest ->
      (* One parameter: wrap the rest of the function inside a Fun *)
      Fun (arg_name, arg_ty, curryFun (rest) (body))

let rec curryFunTypes (args : (string * ty) list) (return_ty : ty) : ty = 
(* (x : int) (y : int) : int becomes int -> int -> int *)
  match args with 
  | [] -> return_ty (*no args means no type currying is necessary, return original return type*)
  | (_, arg_ty1)::rest ->  FunTy (arg_ty1, curryFunTypes (rest) (return_ty))


let rec desugar_expr (se : sfexpr) : expr = 
(*converting each sfexpr (surface sugared) to expr (desugared)*)
  match se with 
  | SUnit -> Unit (*e.g. "()"*)
  | SBool b -> Bool b
  | SNum n -> Num n
  | SVar x -> Var x
  | SFun {args; body} -> (*args is the list, body is the sfexpr*)
    let desugared_body = desugar_expr (body) (*sfexpr to expr*)
    in curryFun (args) (desugared_body)
  | SApp (sel) -> (
    match sel with
    | [] -> Unit 
    | f::args -> (
    (* SApp [f; x; y; z] -> App (App (App (f', x'), y'), z') -> ((f x) y) z*)
      let desugared_f = desugar_expr f in
      let desugared_args = List.map desugar_expr args in
      List.fold_left (fun acc arg -> App (acc, arg)) (desugared_f) (desugared_args) ))
  | SLet {is_rec; name; args; ty; binding; body} -> (
    (*args: list of (param_name, param,type) pairs; body: function body after "in"*)
    (*ty is the return type of the let expr*)
    (*binding is the the expression on the right of = *)
    let desugared_binding = desugar_expr (binding) in 
    let desugared_body = desugar_expr (body) in
    match args with (* list of (arg_name, arg_type) tuples OR empty *)
    | [] -> (*empy args means it's just a simple let-binding*) 
        Let {
          is_rec; 
          name; 
          ty; 
          binding = desugared_binding; 
          body = desugared_body 
        }
    | _ -> (*non-empty args becomes an anynomous function with those args, which gets curried into nested single arg functions*)
    (*for fun-let exprs, these single arg functions become the bindings after "="*)
      Let {
        is_rec; 
        name; 
        ty = curryFunTypes (args) (ty); (*the types need to get curried as well*)
        binding = curryFun (args) (desugared_binding);
        body = desugared_body 
        }
  )
  (*recursive cases: *)
  | SIf(se1, se2, se3) -> If(desugar_expr se1, desugar_expr se2, desugar_expr se3)
  | SBop(op, se1, se2) -> Bop(op, desugar_expr se1, desugar_expr se2)
  | SAssert sfexpr -> Assert (desugar_expr sfexpr) 

let desugar_toplet (t : toplet) (body_expr : expr) : expr =
  let desugared_binding = desugar_expr (t.binding) in 
  match t.args with (*can access record's fields with dot notation*)
    | [] -> 
      Let { 
        is_rec = t.is_rec;
        name = t.name;
        ty = t.ty;
        binding = desugared_binding;
        body = body_expr 
        } 
    | _ -> 
      Let {
        is_rec = t.is_rec;
        name = t.name;
        ty = curryFunTypes (t.args) (t.ty);
        binding = curryFun (t.args) (desugared_binding);
        body = body_expr 
        } 

(*surface program that the parser produced*)
let rec desugar (p : prog) : expr = 
 (*conversts a prog of top-level let exprs (list) into a single expr of nested let exprs*)
 (* a program is just a list of top-level lets with no explicit "in" after them*)
 (*the goal is to turn an empty list into Unit
  OR turn a non-empty list into nested Let expressions, ending in Var last_name*)
 match p with 
 (*trivial cases*) 
 | [] -> Unit 
 | [toplet] -> (* must be the last toplet, whole program evaluates to its name *)
    desugar_toplet (toplet) (Var toplet.name)
 | toplet::rest -> 
    desugar_toplet (toplet) (desugar rest)

let rec type_of (ctxt : ctxt) (e : expr) : (ty, error) result = 
  match e with
  | Unit -> Ok UnitTy
  | Num _ -> Ok IntTy 
  | Bool _ -> Ok BoolTy
  | Var x -> (
    match (Env.find_opt x ctxt) with
    | Some t -> Ok t
    | None -> Error (UnknownVar x) )
  | If (e1, e2, e3) -> (
    match type_of ctxt e1 with
    | Error err -> Error err
    | Ok BoolTy -> (
      (*types of e2 and e3 must match*)
      match type_of ctxt e2 with
      | Error err -> Error err
      | Ok t2 -> (
        match type_of ctxt e3 with
        | Error err -> Error err
        | Ok t3 -> 
          if t2 = t3 then Ok t2
          else Error (IfTyErr (t2, t3))) )
    | Ok tcond -> Error (IfCondTyErr (tcond)) )
  | Bop (op, e1, e2) ->
    let (expected_arg_ty, result_ty) =
      match op with
      | Add | Sub | Mul | Div | Mod -> (IntTy, IntTy)
      | Lt | Lte | Gt | Gte | Eq | Neq -> (IntTy, BoolTy)
      | And | Or -> (BoolTy, BoolTy)
    in
    (match type_of ctxt e1 with
    | Error err -> Error err
    | Ok t1 ->
        if t1 = expected_arg_ty then
          match type_of ctxt e2 with
          | Error err -> Error err
          | Ok t2 ->
              if t2 = expected_arg_ty then Ok result_ty
              else Error (OpTyErrR (op, expected_arg_ty, t2))
        else Error (OpTyErrL (op, expected_arg_ty, t1)))
  | Fun (x, t1, body) -> (
    match type_of (Env.add x t1 ctxt) body with 
    | Ok t2 -> Ok (FunTy (t1, t2))
    | Error err -> Error err ) (*error is in the body, not the argument??*)
  | App (e1, e2) -> ( 
    match type_of ctxt e1 with 
    | Error err -> Error err
    | Ok (FunTy (t1, t)) -> (
      match type_of ctxt e2 with 
      | Error err -> Error err
      | Ok t2 ->
        if t2 = t1 then Ok t
        else Error (FunArgTyErr (t1, t2)))
    | Ok t' -> Error (FunAppTyErr t') )
  | Let { is_rec; name; ty; binding; body } -> (
    if is_rec then ( (*LetRec case*)
      (* side condition: binding must be an anonymous function *)
      match binding with
      | Fun (_, _, _) -> (
        let ctxt' = Env.add name ty ctxt in
        match type_of ctxt' binding with
        | Error err -> Error err
        | Ok binding_ty ->
          if binding_ty = ty then type_of (Env.add name ty ctxt) body
          else Error (LetTyErr (ty, binding_ty)))
      | _ -> Error (LetRecErr name) )
    else ( (*Let case*)
      (*type check the binding (e1) in the current context*)
      match type_of ctxt binding with
      | Error err -> Error err (*propogating the error if the binding itself is ill-typed*)
      | Ok binding_ty ->
      (*if the binding matches the expected type, match the body (e2) in the updated context*)
        if binding_ty = ty then type_of (Env.add name ty ctxt) body
        else Error (LetTyErr (ty, binding_ty))) )
  | Assert (e) -> (
    match type_of ctxt e with
    | Error err -> Error err
    | Ok BoolTy -> Ok UnitTy
    | Ok ty -> Error (AssertTyErr ty) )
   
let type_of (e : expr) : (ty, error) result = 
(*type-inference with all function arguments and values annotated with types*)
(*how to we repesent the typing contect? for each expression, we need to determine its type*)
(*given an expression, type_of returns Ok (ty) if the expression is well-typed, or Error error if it's not*)
  type_of (Env.empty) (e) 

exception AssertFail
exception DivByZero

module Env = Map.Make(String)

let lookup (x : string) (env : dyn_env) : value option =
  (* if type_of is correct, this should never fail. *)
  Env.find_opt x env

let insert ((x, v) : string * value) (env : dyn_env) : dyn_env =
  Env.add x v env

let rec eval (env : dyn_env) (e : expr) : value option = 
  match e with
  | Unit -> Some VUnit
  | Num n -> Some (VNum n)
  | Bool b -> Some (VBool b)
  | Var x -> lookup x env 
  | If (e1, e2, e3) -> (
    match eval env e1 with
    | Some (VBool b) -> (
      if b then eval env e2 
      else eval env e3)
    | _ -> None )
  | Bop (op, e1, e2) -> (
    match op with
    | Add -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VNum (n1 + n2))
      | _ -> None)
    | Sub -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VNum (n1 - n2))
      | _ -> None)
    | Mul -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VNum (n1 * n2))
      | _ -> None)
    | Div -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> 
        if n2 = 0 then raise DivByZero
        else Some (VNum (n1 / n2))
      | _ -> None)
    | Mod -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> 
        if n2 = 0 then raise DivByZero
        else Some (VNum (n1 mod n2))
      | _ -> None)
    | Lt -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 < n2))
      | _ -> None)
    | Lte -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 <= n2))
      | _ -> None)
    | Gt -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 > n2))
      | _ -> None)
    | Gte -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 >= n2))
      | _ -> None)
    | Eq -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 = n2))
      | _ -> None)
    | Neq -> (
      match eval env e1, eval env e2 with
      | Some (VNum n1), Some (VNum n2) -> Some (VBool (n1 <> n2))
      | _ -> None)
    | And -> (
      match eval env e1 with
      | Some (VBool false) -> Some (VBool false)
      | Some (VBool true) -> eval env e2
      | _ -> None)
    | Or -> (
      match eval env e1 with
      | Some (VBool true) -> Some (VBool true)
      | Some (VBool false) -> eval env e2
      | _ -> None))
  | Fun (x, _t1, body) -> Some (VClos {arg = x; body = body; env = env; name = None})
  | App (e1, e2) -> (
    match eval env e1 with
    | Some (VClos {arg = x; body = body; env = clos_env; name = None}) -> (
      match eval env e2 with
      | Some v -> eval (insert (x, v) clos_env) body
      | None -> None)
    | Some (VClos {arg = x; body = body; env = clos_env; name = Some f}) -> (
      match eval env e2 with
      | Some v -> (
        let env_ref = ref (Env.add f (VClos {arg = x; body = body; env = clos_env; name = Some f}) clos_env) in
        let self = VClos {arg = x; body = body; env = !env_ref; name = Some f} in
        env_ref := Env.add f self clos_env;
        eval (insert (x, v) !env_ref) body)
      | None -> None)
    | _ -> None )
  | Let { is_rec; name; ty = _ty; binding; body } -> (
    if is_rec then (
      match binding with
      | Fun (arg_name, _arg_ty, fun_body) -> (
        let env_ref = ref env in
        let self = VClos {arg = arg_name; body = fun_body; env = !env_ref; name = Some name} in
        env_ref := Env.add name self env;
        eval !env_ref body)
      | _ -> None)
    else (
      match eval env binding with
      | Some v -> eval (insert (name, v) env) body
      | None -> None))
  | Assert (e) -> (
    match eval env e with
    | Some (VBool true) -> Some VUnit
    | Some (VBool false) -> raise AssertFail
    | _ -> None)




let eval (e : expr) : value = 
  (* by the time we get to eval, we only evaluate expressions that makes sense (well-typed) *
   so, it's no longer a value option, but a value*)
  match eval Env.empty e with
  | Some v -> v
  | None -> assert false


let interp (s : string) : (value, error) result = 
  match parse s with
  | None -> Error ParseErr
  | Some prog ->
      let e = desugar prog in
      match type_of e with
      | Error err -> Error err
      | Ok _ -> Ok (eval e)