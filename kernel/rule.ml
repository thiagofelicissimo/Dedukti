open Basic
open Format
open Term

type pattern =
  | Var of loc * ident * int * pattern list (* Y x1 ... xn *)
  | Pattern of loc * name * pattern list
  | Lambda of loc * ident * pattern
  | Brackets of term

type wf_pattern =
  | LJoker
  | LVar of ident * int * int list
  | LLambda of ident * wf_pattern
  | LPattern of name * wf_pattern array
  | LBoundVar of ident * int * wf_pattern array
  | LACSet of name * wf_pattern list

type rule_name = Beta | Delta of name | Gamma of bool * name

let rule_name_eq : rule_name -> rule_name -> bool =
 fun n1 n2 ->
  match (n1, n2) with
  | Delta x, Delta y -> name_eq x y
  | Gamma (b1, x), Gamma (b2, y) -> b1 = b2 && name_eq x y
  | _, _ -> false

type 'a rule = {name : rule_name; ctx : 'a context; pat : pattern; rhs : term}

type partially_typed_rule = term option rule

type typed_rule = term rule

type arity_rule = int rule

type constr = int * term

let pp_constr fmt (i, t) = fprintf fmt "%i =b %a" i pp_term t

type rule_infos = {
  l : loc;
  name : rule_name;
  nonlinear : int list;
  cst : name;
  args : pattern list;
  rhs : term;
  ctx_size : int;
  esize : int;
  pats : wf_pattern array;
  arity : int array;
  constraints : constr list;
}

let infer_rule_context ri =
  let res = Array.make ri.ctx_size (dloc, mk_ident "_", -1) in
  let rec aux k = function
    | LJoker                 -> ()
    | LVar (name, n, _)      ->
        if n >= k then res.(n - k) <- (dloc, name, ri.arity.(n - k))
    | LLambda (_, body)      -> aux (k + 1) body
    | LPattern (_, args)     -> Array.iter (aux k) args
    | LBoundVar (_, _, args) -> Array.iter (aux k) args
    | LACSet (_, args)       -> List.iter (aux k) args
  in
  Array.iter (aux 0) ri.pats;
  Array.to_list res

let infer_rule_context_without_arity ri =
  ri |> infer_rule_context |> List.map (fun (loc, id, _) -> (loc, id, None))

let pattern_of_rule_infos r = Pattern (r.l, r.cst, r.args)

type rule_error =
  | BoundVariableExpected of loc * pattern
  | DistinctBoundVariablesExpected of loc * ident
  | VariableBoundOutsideTheGuard of loc * term
  | UnboundVariable of loc * ident * pattern
  (* FIXME : this exception seems never to be raised *)
  | AVariableIsNotAPattern of loc * ident
  | NonLinearNonEqArguments of loc * ident
  (* FIXME: the reason for this exception should be formalized on paper ! *)
  | NotEnoughArguments of loc * ident * int * int * int
  | NonLinearRule of loc * rule_name

exception Rule_error of rule_error

let rec pp_pattern out pattern =
  match pattern with
  | Var (_, x, n, [])    -> fprintf out "%a[%i]" pp_ident x n
  | Var (_, x, n, lst)   ->
      fprintf out "%a[%i] %a" pp_ident x n (pp_list " " pp_pattern_wp) lst
  | Pattern (_, n, [])   -> fprintf out "%a" pp_name n
  | Pattern (_, n, pats) ->
      fprintf out "%a %a" pp_name n (pp_list " " pp_pattern_wp) pats
  | Lambda (_, x, p)     -> fprintf out "%a => %a" pp_ident x pp_pattern p
  | Brackets t           -> fprintf out "{ %a }" pp_term t

and pp_pattern_wp out pattern =
  match pattern with
  | (Var (_, _, _, _ :: _) | Pattern _ | Lambda _) as p ->
      fprintf out "(%a)" pp_pattern p
  | p -> pp_pattern out p

let rec pp_wf_pattern fmt wf_pattern =
  match wf_pattern with
  | LJoker -> fprintf fmt "_"
  | LVar (x, n, []) -> fprintf fmt "%a[%i]" pp_ident x n
  | LVar (x, n, lst) ->
      fprintf fmt "%a[%i] %a" pp_ident x n (pp_list " " pp_print_int) lst
  | LPattern (n, pats) when Array.length pats = 0 -> fprintf fmt "%a" pp_name n
  | LPattern (n, pats) ->
      fprintf fmt "%a %a" pp_name n
        (pp_list " " pp_wf_pattern_wp)
        (Array.to_list pats)
  | LLambda (x, p) -> fprintf fmt "%a => %a" pp_ident x pp_wf_pattern p
  | LBoundVar (x, n, pats) when Array.length pats = 0 ->
      fprintf fmt "%a[%i]" pp_ident x n
  | LBoundVar (x, n, pats) ->
      fprintf fmt "%a[%i] %a" pp_ident x n
        (pp_list " " pp_wf_pattern_wp)
        (Array.to_list pats)
  | LACSet (cst, l) ->
      fprintf fmt "%a{%a}" pp_name cst (pp_list "; " pp_wf_pattern_wp) l

and pp_wf_pattern_wp fmt wf_pattern =
  match wf_pattern with
  | (LVar (_, _, _ :: _) | LPattern _ | LLambda _) as p ->
      fprintf fmt "(%a)" pp_wf_pattern p
  | _ -> pp_wf_pattern fmt wf_pattern

let get_loc_pat = function
  | Var (l, _, _, _) | Pattern (l, _, _) | Lambda (l, _, _) -> l
  | Brackets t -> get_loc t

let get_loc_rule r = get_loc_pat r.pat

let pp_rule_name fmt = function
  | Beta             -> fprintf fmt "Beta"
  | Delta n          -> fprintf fmt "Delta: %a" pp_name n
  | Gamma (true, n)  -> fprintf fmt "Gamma: %a" pp_name n
  | Gamma (false, n) -> fprintf fmt "Gamma (default): %a" pp_name n

let pp_rule pp_ctxt fmt (rule : 'a rule) =
  fprintf fmt " {%a} [%a] %a --> %a" pp_rule_name rule.name pp_ctxt rule.ctx
    pp_pattern rule.pat pp_term rule.rhs

let pp_untyped_rule fmt = pp_rule pp_untyped_context fmt

let pp_typed_rule = pp_rule pp_typed_context

let pp_part_typed_rule = pp_rule pp_part_typed_context

(* FIXME: do not print all the informations because it is used in utils/errors *)
let pp_rule_infos out r =
  pp_untyped_rule out
    {
      name = r.name;
      ctx = infer_rule_context r;
      pat = pattern_of_rule_infos r;
      rhs = r.rhs;
    }

let pattern_to_term p =
  let rec aux k = function
    | Brackets t           -> t
    | Pattern (l, n, args) -> mk_App2 (mk_Const l n) (List.map (aux k) args)
    | Var (l, x, n, args)  -> mk_App2 (mk_DB l x n) (List.map (aux k) args)
    | Lambda (l, x, pat)   -> mk_Lam l x None (aux (k + 1) pat)
  in
  aux 0 p

type pattern_info = {
  constraints : constr list;
  context_size : int;
  arity : int array;
  nonlinear : int list;
}

(* ************************************************************************** *)

(* ************************************************************************** *)

let bracket_ident = mk_ident "{_}" (* FIXME: can this be replaced by dmark? *)

let rec all_distinct = function
  | []       -> true
  | hd :: tl -> if List.mem hd tl then false else all_distinct tl

module IntHashtbl = Hashtbl.Make (struct
  type t = int

  let equal i j = i = j

  let hash i = i land max_int
end)

(* TODO : cut this function in smaller ones *)

(** [check_patterns size pats] checks that the given pattern is a well formed
Miller pattern in a context of size [size] and linearizes it.

More precisely:
- Context variables are exclusively applied to distinct locally bound variables
- Occurences of each context variable are all applied to the same number of arguments

Returns the representation of the corresponding linear well formed pattern
together with extracted pattern information:
- Convertibility constraints from non-linearity and brackets
- Size of generated context
- Arity infered for all context variables
*)
let check_patterns (esize : int) (pats : pattern list) :
    wf_pattern list * pattern_info =
  let nonlinear = ref [] in
  let constraints = ref [] in
  let context_size = ref esize in
  let arity = IntHashtbl.create 10 in
  let extract_db k = function
    | Var (_, _, n, []) when n < k -> n
    | p -> raise (Rule_error (BoundVariableExpected (get_loc_pat p, p)))
  in
  let rec aux (k : int) (pat : pattern) : wf_pattern =
    match pat with
    | Lambda (_, x, p) -> LLambda (x, aux (k + 1) p)
    | Var (_, x, n, args) when n < k ->
        LBoundVar (x, n, Array.of_list (List.map (aux k) args))
    | Var (l, x, n, args) (* Context variable (n>=k)  *) ->
        (* Miller variables should only be applied to locally bound variables *)
        let args' = List.map (extract_db k) args in
        (* Miller variables should be applied to distinct variables *)
        if not (all_distinct args') then
          raise (Rule_error (DistinctBoundVariablesExpected (l, x)));
        let nb_args' = List.length args' in
        if IntHashtbl.mem arity (n - k) then
          if nb_args' <> IntHashtbl.find arity (n - k) then
            raise (Rule_error (NonLinearNonEqArguments (l, x)))
          else nonlinear := (n - k) :: !nonlinear
        else IntHashtbl.add arity (n - k) nb_args';
        LVar (x, n, args')
    | Brackets t ->
        let unshifted =
          try Subst.unshift k t
          with Subst.UnshiftExn ->
            raise (Rule_error (VariableBoundOutsideTheGuard (get_loc t, t)))
          (* Note: A different exception is previously raised at rule type-checking for this. *)
        in
        IntHashtbl.add arity !context_size 0;
        (* Brackets are variable with arity 0 *)
        incr context_size;
        let nvar = !context_size - 1 in
        (* DB indice for a fresh context variable *)
        constraints := (nvar, unshifted) :: !constraints;
        LVar (bracket_ident, nvar + k, [])
    | Pattern (_, n, args) -> LPattern (n, Array.of_list (List.map (aux k) args))
  in
  let wf_pats = List.map (aux 0) pats in
  ( wf_pats,
    {
      context_size = !context_size;
      constraints = !constraints;
      arity = Array.init !context_size (fun i -> IntHashtbl.find arity i);
      nonlinear = !nonlinear;
    } )

let to_rule_infos (r : 'a rule) : rule_infos =
  let ctx_size = List.length r.ctx in
  let l, cst, args =
    match r.pat with
    | Pattern (l, cst, args) -> (l, cst, args)
    | Var (l, x, _, _)       -> raise
                                  (Rule_error (AVariableIsNotAPattern (l, x)))
    | Lambda _ | Brackets _  -> assert false
    (* already raised at the parsing level *)
  in
  let pats2, infos = check_patterns ctx_size args in
  {
    l;
    name = r.name;
    nonlinear = infos.nonlinear;
    cst;
    args;
    rhs = r.rhs;
    ctx_size;
    esize = infos.context_size;
    pats = Array.of_list pats2;
    arity = infos.arity;
    constraints = infos.constraints;
  }

let untyped_rule_of_rule_infos ri : partially_typed_rule =
  {
    name = ri.name;
    ctx = infer_rule_context_without_arity ri;
    pat = pattern_of_rule_infos ri;
    rhs = ri.rhs;
  }

(*         Rule checking       *)

(* Checks that all Miller variables are applied to at least
   as many arguments on the rhs as they are on the lhs (their arity). *)
let check_arity (r : rule_infos) : unit =
  let check _ id n k nargs =
    let expected_args = r.arity.(n - k) in
    if nargs < expected_args then
      raise
      @@ Rule_error (NotEnoughArguments (r.l, id, n, nargs, expected_args))
  in
  let rec aux k = function
    | Kind | Type _ | Const _ -> ()
    | DB (l, id, n) -> if n >= k then check l id n k 0
    | App (DB (l, id, n), a1, args) when n >= k ->
        check l id n k (List.length args + 1);
        List.iter (aux k) (a1 :: args)
    | App (f, a1, args) -> List.iter (aux k) (f :: a1 :: args)
    | Lam (_, _, None, b) -> aux (k + 1) b
    | Lam (_, _, Some a, b) | Pi (_, _, a, b) ->
        aux k a;
        aux (k + 1) b
  in
  aux 0 r.rhs

(** Checks that all rule are left-linear. *)
let check_linearity (r : rule_infos) : unit =
  if r.nonlinear <> [] then raise (Rule_error (NonLinearRule (r.l, r.name)))
