(********** universes' variables ************)


module Log =
struct
  let file = ref "stderr"
  let in_c = ref stderr
  let log_file () = !file


  let set_log_file s =
    file := s;
    in_c := (open_out s)


  let out_channel () = in_c

  let append s =
    Format.fprintf (Format.formatter_of_out_channel !in_c) "%s@." s

  let close () = close_out !in_c

end


module UVar =
struct

  type uvar = Basic.ident

  let basename = "univ_variable"

  let is_uvar t =
    match t with
    | Term.Const(_,n) ->
      let s = Basic.string_of_ident (Basic.id n) in
      let n = String.length basename in
      String.length s > n && String.sub s 0 n = basename
    | _ -> false

  let extract_uvar t =
    match t with
    | Term.Const(_,n) when is_uvar t -> Basic.id n
    | _ -> failwith "is not an uvar"

  let fresh =
    let counter = ref 0 in
    fun () ->
      let name = Format.sprintf "%s%d" basename !counter in
      incr counter; Basic.mk_ident name

end


module Mapping =
struct

  type index = int

  exception MappingError of index

  type t =
    {
      to_index: (UVar.uvar, index) Hashtbl.t;
      from_index: (index, UVar.uvar) Hashtbl.t
    }

  let memory =
    {
      to_index = Hashtbl.create 251;
      from_index = Hashtbl.create 251
    }

  let to_index =
    let counter = ref 0 in
    fun name ->
      if Hashtbl.mem memory.to_index name then begin
        Hashtbl.find memory.to_index name end
      else
        let n = !counter in
        Hashtbl.add memory.to_index name n;
        Hashtbl.add memory.from_index n name;
        incr counter; n

  let from_index n =
    if Hashtbl.mem memory.from_index n then
      Hashtbl.find memory.from_index n
    else
      raise (MappingError n)
end

module ReverseCiC =
struct

  open UVar
  open Basic
  (* Only Prop and Type 0 are necessary actually *)
  type univ =
    | Prop
    | Type of int

  let term_of_univ univ =
    let md = Basic.mk_mident "cic" in
    let prop = Basic.mk_ident "prop" in
    let utype = Basic.mk_ident "type" in
    let z = Basic.mk_ident "z" in
    let s = Basic.mk_ident "s" in
    let mk_const id = Term.mk_Const Basic.dloc (Basic.mk_name md id) in
    let rec term_of_nat i =
      assert (i>= 0);
      if i = 0 then
        mk_const z
      else
        Term.mk_App (mk_const s) (term_of_nat (i-1)) []
    in
    match univ with
    | Prop -> mk_const prop
    | Type i -> Term.mk_App (mk_const utype) (term_of_nat i) []


  let cic = mk_mident "cic"

  let mk_const id = Term.mk_Const dloc (mk_name cic id)

  let z = mk_name cic (mk_ident "z")

  let s = mk_name cic (mk_ident "s")

  let succ = mk_name cic (mk_ident "succ")

  let sort = mk_name cic (mk_ident "Sort")

  let lift = mk_name cic (mk_ident "lift")

  let rule = mk_name cic (mk_ident "rule")

  let prop = mk_name cic (mk_ident "prop")

  let type_ = mk_name cic (mk_ident "type")

  let is_const cst t =
    match t with
    | Term.Const(_,n) -> name_eq cst n
    | _ -> false

  let is_prop t =
    match t with
    | Term.Const(_,n) when is_const prop t -> true
    | _ -> false

  let is_type t =
    match t with
    | Term.App(t,_,[]) when is_const type_ t -> true
    | _ -> false

  let is_succ t =
    match t with
    | Term.App(c,arg,[]) when is_const succ c -> true
    | _ -> false

  let is_lift t =
    match t with
    | Term.App(c, s1, [s2;a]) when is_const lift c -> true
    | _ -> false

  let is_rule t =
    match t with
    | Term.App(c, s1, [s2]) when is_const rule c -> true
    | _ -> false

  let extract_type t =
    let rec to_int t =
      match t with
      | Term.Const(_,z) when is_const z t -> 0
      | Term.App(t,u, []) when is_const s t -> 1+(to_int u)
      | _ -> assert false
    in
    match t with
    | Term.App(t,u,[]) when is_const type_ t -> to_int u
    | _ -> failwith "is not a type"

  let extract_succ t =
    match t with
    | Term.App(c,arg,[]) when is_const succ c -> arg
    | _ -> failwith "is not a succ"

  let extract_lift t =
    match t with
    | Term.App(c,s1,[s2;a]) when is_const lift c -> s1,s2
    | _ -> failwith "is not a lift"

  let extract_rule t =
    match t with
    | Term.App(c, s1, [s2]) when is_const rule c -> s1, s2
    | _ -> failwith "is not a rule"
end



module type ConstraintsInterface =
sig

  type var

  type constraints =
    | Univ of var * ReverseCiC.univ
    | Eq of var * var
    | Lift of (var * var) * (var * var)
    | Succ of var * var
    | Rule of var * var * var

  val var_of_index : Mapping.index -> var

  val generate_constraints : Term.term -> Term.term -> bool
  (** generate_constraints [l] [r] returns [true] if some constraints has been generated *)

  module ConstraintsSet : Set.S with type elt = constraints

  val export : unit -> ConstraintsSet.t

  val info : unit -> string

  val string_of_var : var -> string
end


module BasicConstraints:ConstraintsInterface with type var = Mapping.index =
struct

  open UVar
  open Mapping
  open ReverseCiC

  type var = index

  type constraints =
    | Univ of index * univ
    | Eq of index * index
    | Lift of (var * var) * (var * var)
    | Succ of index * index
    | Rule of index * index * index

  module Variables = Set.Make (struct type t = index let compare = compare end)

  module ConstraintsSet = Set.Make (struct type t = constraints let compare = compare end)

  module CS = ConstraintsSet

  module UF = Unionfind

  let uf = ref (UF.create 10000)

  let var_of_index i = UF.find !uf i

  let var_of_ident ident = var_of_index (to_index ident)

  let global_variables = ref Variables.empty

  let global_constraints = ref ConstraintsSet.empty

  let add_variable v =
    global_variables := Variables.add v !global_variables

  let add_variables vs =
    List.iter add_variable vs

  let add_constraint c =
    global_constraints := ConstraintsSet.add c !global_constraints

  let add_constraint_prop ident =
    let n = var_of_ident ident in
    add_variables [n];
    add_constraint (Univ(n, Prop))

  let add_constraint_type ident i =
    let n = var_of_ident ident in
    add_variables [n];
    add_constraint (Univ(n, Type i))

  let add_constraint_eq ident ident' =
    let n = var_of_ident ident in
    let n' = var_of_ident ident' in
    add_variables [n;n'];
    uf := UF.union !uf n n'

  let add_constraint_succ ident ident' =
    let n = var_of_ident ident in
    let n' = var_of_ident ident' in
    add_variables [n;n'];
    add_constraint (Succ(n,n'))

  let add_constraint_lift ident ident' ident'' ident''' =
    let n = var_of_ident ident in
    let n' = var_of_ident ident' in
    let n'' = var_of_ident ident'' in
    let n''' = var_of_ident ident''' in
    add_variables [n;n';n'';n'''];
    add_constraint (Lift((n,n'),(n'',n''')))

  let add_constraint_rule ident ident' ident'' =
    let n = var_of_ident ident in
    let n' = var_of_ident ident' in
    let n'' = var_of_ident ident'' in
    add_variables [n;n';n''];
    add_constraint (Rule(n,n',n''))

  let info () =
    let open ReverseCiC in
    let prop,ty,eq,succ,lift,rule = ref 0, ref 0, ref 0, ref 0, ref 0, ref 0 in
    CS.iter (fun x ->
        match x with
        | Univ(_,Prop) -> incr prop
        | Univ (_, Type _) -> incr ty
        | Eq _ -> incr eq
        | Succ _ -> incr succ
        | Lift _ -> incr lift
        | Rule _ -> incr rule) !global_constraints;

    let hash_to_string fmt (k,v) =
      Format.fprintf fmt "%a --> %d@." Basic.pp_ident k (var_of_index v)
    in
    let print fmt () =
      Format.fprintf fmt "Variable correspondance:@.";
      Hashtbl.iter (fun k v -> Format.fprintf fmt "%a" hash_to_string (k,v)) Mapping.memory.to_index;
      Format.fprintf fmt "Number of variables  : %d@." (Variables.cardinal !global_variables);
      Format.fprintf fmt "Number of constraints:@.";
      Format.fprintf fmt "@[prop  :%d@]@." !prop;
      Format.fprintf fmt "@[ty  :%d@]@." !ty;
      Format.fprintf fmt "@[eq  :%d@]@." !eq;
      Format.fprintf fmt "@[succ:%d@]@." !succ;
      Format.fprintf fmt "@[le  :%d@]@." !lift;
      Format.fprintf fmt "@[rule:%d@]@." !rule
    in
    Format.asprintf "%a" print ()

  module V = UVar

  let rec generate_constraints (l:Term.term) (r:Term.term) =
    let open ReverseCiC in

  Log.append (Format.asprintf "debugl: %a@." Term.pp_term l);
  Log.append (Format.asprintf "debugr: %a@." Term.pp_term r);
    if is_uvar l && is_prop r then
      let l = extract_uvar l in
      add_constraint_prop l;
      true
    else if is_prop l && is_uvar r then
      generate_constraints r l
    else if is_uvar l && is_type r then
      let l = extract_uvar l in
      let i = extract_type r in
      add_constraint_type l i;
      true
    else if is_type l && is_uvar r then
      generate_constraints r l
    else if is_uvar l && is_uvar r then
      let l = extract_uvar l in
      let r = extract_uvar r in
      add_constraint_eq l r;
      true
    else if is_succ l && is_uvar r then
      begin
        let l = extract_succ l in
        let uvar = extract_uvar l in
        let uvar' = extract_uvar r in
        add_constraint_succ uvar uvar';
        true
      end
    else if is_uvar l && is_succ r then
      generate_constraints r l (* just a switch of arguments *)
    else if is_rule l && is_uvar r then
      let s1,s2 = extract_rule l in
      let s1 = extract_uvar s1 in
      let s2 = extract_uvar s2 in
      let r = extract_uvar r in
      add_constraint_rule s1 s2 r;
      true
    else if is_uvar l && is_rule r then
      generate_constraints r l (* just a switch of arguments *)
    else if is_lift l && is_lift r then
      let s1,s2 = extract_lift l in
      let s3,s4 = extract_lift r in
      let s1 = extract_uvar s1 in
      let s2 = extract_uvar s2 in
      let s3 = extract_uvar s3 in
      let s4 = extract_uvar s4 in
      add_constraint_lift s1 s2 s3 s4;
      true
    else if is_lift l && is_succ r then
      failwith "BUG"
    else if is_succ l && is_lift r then
      failwith "BUG"
    else if is_lift l && is_prop r then
      failwith "BUG"
    else if is_prop l && is_lift r then
      failwith "BUG"
    else if is_lift l && is_uvar r then
      failwith "BUG"
    else if is_uvar l && is_lift r then
      failwith "BUG"
    else if is_succ l && is_prop r then
      failwith "BUG"
    else if is_prop l && is_succ r then
      failwith "BUG"
    else if is_prop l && is_rule r then
      failwith "BUG"
    else if is_rule l && is_prop r then
      failwith "BUG"
    else if is_succ l && is_type r then
      failwith "BUG"
    else if is_type l && is_succ r then
      failwith "BUG"
    else if is_type l && is_rule r then
      failwith "BUG"
    else if is_rule l && is_type r then
      failwith "BUG"
    else if is_succ l && is_rule r then
      failwith "BUG"
    else if is_rule l && is_succ r then
      failwith "BUG"
    else if is_succ l && is_type r then
      failwith "BUG"
    else if is_type l && is_succ r then
      failwith "BUG"
    else
      false

  let export () =
    let uf = !uf in
    let find n = UF.find uf n in
    let normalize c =
      match c with
      | Univ(n,u) -> Univ(find n,u)
      | Eq(n,n') -> Eq(find n, find n')
      | Lift((n,n'),(n'',n''')) -> Lift((find n, find n'),(find n'', find n'''))
      | Succ(n,n') -> Succ(find n, find n')
      | Rule(n,n',n'') -> Rule(find n, find n', find n'')
    in
    ConstraintsSet.map (fun c -> normalize c) !global_constraints

  let string_of_var n = string_of_int n

end

module Elaboration =
struct

  let new_uvar sg =
    let id = UVar.fresh () in
    let md = Signature.get_name sg in
    let name = Basic.mk_name md id in
    let cst = Term.mk_Const Basic.dloc name in
    Signature.add_declaration sg Basic.dloc id Signature.Static
      (Term.mk_Const Basic.dloc ReverseCiC.sort);
    cst

  let rec elaboration sg term =
    let open Term in
    let open ReverseCiC in
    if is_prop term then
      term
    else if  is_type term then
      new_uvar sg
    else
      match term with
      | App(f, a, al) ->
        let f' = elaboration sg f in
        let a' = elaboration sg a in
        let al' = List.map (elaboration sg) al in
        mk_App f' a' al'
      | Lam(loc, id, t_opt, t) ->
        let t' = elaboration sg t in
        begin
          match t_opt with
          | None -> mk_Lam loc id t_opt t'
          | Some x -> let x' = elaboration sg x in
            mk_Lam loc id (Some x') t'
        end
      | Pi(loc, id, ta, tb) ->
        let ta' = elaboration sg ta in
        let tb' = elaboration sg tb in
        mk_Pi loc id ta' tb'
      | _ ->     term
end

module Reconstruction =
struct

  type model = UVar.uvar -> Term.term

  let rec reconstruction model term =
    let open Term in
    if UVar.is_uvar term then
      let var = UVar.extract_uvar term in
      model var
    else
      match term with
      | App(f, a, al) ->
        let f' = reconstruction model f in
        let a' = reconstruction model a in
        let al' = List.map (reconstruction model) al in
        mk_App f' a' al'
      | Lam(loc, id, t_opt, t) ->
        let t' = reconstruction model t in
        begin
          match t_opt with
          | None -> mk_Lam loc id t_opt t'
          | Some x -> let x' = reconstruction model x in
            mk_Lam loc id (Some x') t'
        end
      | Pi(loc, id, ta, tb) ->
        let ta' = reconstruction model ta in
        let tb' = reconstruction model tb in
        mk_Pi loc id ta' tb'
      | _ ->     term

end
