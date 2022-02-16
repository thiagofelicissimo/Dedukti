module B = Kernel.Basic
module F = Common.Files
module T = Kernel.Term
module U = Common.Universes

exception Not_uvar

(** prefix for all the universe variables. *)
let basename = "?"

(** Check if a term should be elaborated by a fresh variable *)
let is_pre_var t =
  match t with T.Const (_, n) when n = U.pvar () -> true | _ -> false

(** Check if a term is universe variable, i.e. its ident should be ?11, ?43... *)
let is_uvar t =
  match t with
  | T.Const (_, n) ->
      let s = B.string_of_ident (B.id n) in
      let n = String.length basename in
      String.length s > n && String.sub s 0 n = basename
  | _              -> false

(** Check if a term is universe expression *)
let rec is_uexp t =
  match t with
  | T.Const(_,n) when B.name_eq n (U.ctszero ())->
     true
  | T.App (T.Const(_,n), t1, []) when B.name_eq n (U.ctssucc ())->
     is_uexp t1
  | T.App (T.Const(_,n), t1, [t2]) when B.name_eq n (U.ctsmax ())->
     is_uexp t1 && is_uexp t2
  | T.Const (_, n) ->
     let s = B.string_of_ident (B.id n) in
     let n = String.length basename in
     String.length s > n && String.sub s 0 n = basename
  | _              -> false

                    
(** [name_of_uvar t] returns the name of universe variable if [t] is a universe variable, raise [Not_uvar] otherwise *)
let name_of_uvar t =
  match t with T.Const (_, n) when is_uvar t -> n | _ -> raise Not_uvar

(** Internal counter use by this module to generate fresh variables *)
let counter = ref 0

(** Generate a fresh name for a universe variable *)
let fresh () =
  let name = Format.sprintf "%s%d" basename !counter in
  incr counter; B.mk_ident name

(** [fresh_uvar env ()] returns a fresh term representing a universe variable. Add a new declaration into the module env.md *)
let fresh_uvar : F.cout F.t -> unit -> T.term =
 fun file () ->
  let id = fresh () in
  let uvar = B.mk_name file.md id in
  let uterm = T.mk_Const B.dloc uvar in
  let sort_type =
    let md_theory = !U.md_theory in
    T.mk_Const B.dloc (B.mk_name md_theory (B.mk_ident "Sort"))
  in
  Format.fprintf (F.fmt_of_file file) "%a@." Api.Pp.Default.print_entry
    (Parsers.Entry.Decl
       ( B.dloc,
         id,
         Kernel.Signature.Public,
         Kernel.Signature.Definable T.Free,
         sort_type ));
  uterm
