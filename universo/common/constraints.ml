module B = Kernel.Basic
module F = Files
module R = Kernel.Rule
module S = Kernel.Signature
module T = Kernel.Term
module U = Universes
module M = Api.Meta


let equations : (U.univ * U.univ) list ref = ref []         
         
type t = {file : F.cout F.t; meta : M.cfg}

type print_cstrs = {
  eqvar : (B.name * B.name) list;
  axiom : (U.univ * U.univ) list;
  cumul : (U.univ * U.univ) list;
  rule : (U.univ * U.univ * U.univ) list;
}

let dummy_name =
  R.Gamma (false, B.mk_name (B.mk_mident "dummy") (B.mk_ident "dummy"))

let mk_rule vl vr =
  let pat = R.Pattern (B.dloc, vl, []) in
  let rhs = T.mk_Const B.dloc vr in
  R.{ctx = []; pat; rhs; name = dummy_name}

let print_rule pp fmt (l, r) = Format.fprintf fmt "@.[] %a --> %a" pp l pp r

let print_eq_var fmt (l, r) =
  Format.fprintf fmt "%a.@." (print_rule Api.Pp.Default.print_name) (l, r)

let print_predicate fmt p =
  let l' = U.term_of_pred p in
  let r' = U.true_ () in
  Format.fprintf fmt "%a.@." (print_rule Api.Pp.Default.print_term) (l', r')

(** [mk_var_cstre env f l r] add the constraint [l =?= r]. Call f on l and r such that
    l >= r. *)
let mk_var_cstr f l r =
  (* FIXME: is it really necessary to compare number and not the full string ? *)
  let get_number s = int_of_string (String.sub s 1 (String.length s - 1)) in
  let il = B.string_of_ident @@ B.id l in
  let ir = B.string_of_ident @@ B.id r in
  let nl = get_number il in
  let nr = get_number ir in
  if nl = 0 && nr = 0 then if r < l then (f l r; (l, r)) else (f r l; (r, l))
  else if nr < nl then (f l r; (l, r))
  else (f r l; (r, l))

let deps : B.mident list ref  = ref []

exception NotAnUexpTerm
         
let rec uexp_term_to_pattern t =
  match t with
  | T.Const (_, n) ->
     R.Pattern (B.dloc, n, [])
  | T.App (T.Const(_,n), t1, [t2]) when B.name_eq n (U.ctsmax ())->
     let l1 = uexp_term_to_pattern t1 in
     let l2 = uexp_term_to_pattern t2 in     
     R.Pattern (B.dloc, U.ctsmax (), [l1; l2])
  | _              -> raise NotAnUexpTerm


(*let print_uexp l = Api.Pp.Default.print_term (U.term_of_univ l)*)

let print_uexp fmt e =
  let t = U.term_of_univ e in
  Format.fprintf fmt "%a" Api.Pp.Default.print_term t

let print_equations () =
  List.fold_left
    (fun _ (l,r) ->
      Format.printf "%a = %a@." print_uexp l print_uexp r)
    (Format.printf "constraints: @.") !equations

exception FoundCumul
     
let add_pred_cstr p =
  let eq p = 
  match p with
  | U.Axiom (u1, u2) -> U.LSucc u1, u2
  | U.Rule (u1, u2, u3) -> U.LMax (u1, u2), u3
  | _ -> raise FoundCumul
  in equations := (eq p) :: (!equations)

  
let mk_cstr env _ cstr =
  let fmt = F.fmt_of_file env.file in
  match cstr with
  | U.Pred p       ->
     Format.fprintf fmt "%a@." print_predicate p;
     add_pred_cstr p;
     (*     Format.printf "%a@." print_predicate p;     *)
     true
(*  | U.EqVar (l, r) ->
      let l, r = mk_var_cstr f l r in
      (* FIXME: explain the rationale. *)
      Api.Meta.add_rules env.meta [mk_rule l r];
      if not (List.mem (B.md r) !deps) then deps := B.md r :: !deps;
      Format.fprintf fmt "%a@.\n" print_eq_var (l, r);
      Format.printf "%a@.\n" print_eq_var (l, r);            
      true*)
  | U.EqLvlExp (l, r) ->
     equations := (l, r) :: !equations;
     (*     let print_uexp l = Api.Pp.Default.print_term (U.term_of_univ l) in     *)
     let l' = U.term_of_univ l in
     let r' = U.term_of_univ r in     
     Format.fprintf fmt "[] %a --> %a.@." Api.Pp.Default.print_term l' Api.Pp.Default.print_term r';
     (*     Format.printf "[] %a --> %a.@." Api.Pp.Default.print_term l Api.Pp.Default.print_term r;*)
     (*     Api.Meta.add_rules env.meta [R.{ctx = []; pat = uexp_term_to_pattern l; rhs = r; name = dummy_name}];*)
     true

let rec term_to_uexp t =
  match t with
  | T.Const(_,n) when B.name_eq n (U.ctszero ())->
     U.LZero
  | T.App (T.Const(_,n), t1, []) when B.name_eq n (U.ctssucc ())->
     U.LSucc (term_to_uexp t1)
  | T.App (T.Const(_,n), t1, [t2]) when B.name_eq n (U.ctsmax ())->
     U.LMax (term_to_uexp t1, term_to_uexp t2)
  | T.Const (_, n) ->
     let s = B.string_of_ident (B.id n) in
     U.LVar s
  | _              -> raise NotAnUexpTerm


       
let get_deps () = !deps

let flush () = deps := []
