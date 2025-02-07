open Term
open Basic
open Rule
open Ac

(** {2 Error} *)

type dtree_error =
  | HeadSymbolMismatch of loc * name * name
  | ArityInnerMismatch of loc * ident * ident
  | ACSymbolRewritten of loc * name * int

exception Dtree_error of dtree_error

(** This represent a meta variables applied to distinct
    locally bounded variables:  X x_1 ... x_n.
    - [arity] is the number of arguments
    - [depth] is the number of locally bounded variables available
    - [vars] is the list of successive arguments in order
    - [mapping] is a mapping for all available bounded variable n to
      - either -1 is this variable is absent from the list of arguments
      - or the index of that integer in the [vars] list

    The following invariants should therefore be verified:
    - [arity] is the length of vars
    - [depth] is the length of mapping
    - All elements of [vars] are between 0 and [depth]-1
    - Non negative elements of [mapping] are between 0 and [arity]-1
    - [mapping].(i) = n >= 0  iff  List.nth [vars] ([arity]-n-1) = i
    - This means exactly [arity] elements of [mapping] are non negative

    An example:
    \{
      arity   = 2;
      depth   = 5;
      vars    = [4; 2];
      mapping = [| (-1) ; (-1) ; 0 ; (-1) ; 1 |]
    \}
*)
type miller_var = {
  arity : int;  (** Arity of the meta variable *)
  depth : int;
      (** Depth under which this occurence of the meta variable is considered *)
  vars : int list;  (** The list of local DB indices of argument variables*)
  mapping : int array;
      (** The mapping from all local DB indices for either -1 or position
        in the list of argument variables (starting from the end)
    *)
}

(** [mapping_of_vars depth arity vars] build a reverse mapping
    from the list [vars] of DB indices arguments of a Miller variable.
    For instance the pattern x => y => z => F y x produces a call to
    [mapping_of_vars 3 2 \[1; 0\] ] which returns the array
    [| 1 ; 0 ; (-1) |] *)
val mapping_of_vars : int -> int -> int list -> int array

val fo_var : miller_var

(** {2 Pre-Matching problems} *)

(** Abstract matching problems. This can be instantiated with
    - When building a decision tree ['a = int] refers to positions in the stack
    - When matching against a term, ['a = term Lazy.t] refers to actual terms
*)

(* TODO: add loc to this to better handle errors *)

(** [(vars, matched)] is the higher order equational problem:
       X x1  ... xn = [matched]   with [vars]=\[ x1 ; ... ; xn \] *)
type 'a eq_problem = miller_var * 'a

(** ([n], [vars]) represents the [n]-th variable applied
    to the [vars] bound variables. *)
type var_p = int * miller_var

(** [(depth, symb, njoks, vars, terms)]
      Represents the flattenned equality under AC symbol [symb] of:
      - [njoks] jokers and the given variables [vars]
      - The given [terms]
      e.g.
        [ +{ X\[x\] , _, Y\[y,z\] } = +{ f(a), f(y), f(x)} ]
      the [depth] field in all elements of [vars] should be equal to [depth]
      FIXME: do we need [depth] here then ?
   *)
type 'a ac_problem = int * ac_ident * int * var_p list * 'a

(** A problem with int indices referencing positions in the stack  *)
type pre_matching_problem = {
  pm_eq_problems : int eq_problem list LList.t;
      (** For each variable of a rewrite rule (array),
        a list of equational problems under various depths *)
  pm_ac_problems : int ac_problem list;
      (** A list of AC-matching problems under a certain depth *)
  pm_arity : int array;  (** Constant time access to a variable's arity *)
}

val pp_var_type : var_p printer

val pp_eq_problems : string -> 'a printer -> (int * 'a eq_problem list) printer

val pp_ac_problem : 'a printer -> 'a ac_problem printer

(** int matching problem printing function (for dtree). *)
val pp_pre_matching_problem : string -> pre_matching_problem printer

(** {2 Decision Trees} *)

(** Arguments of a pattern may be the following:
    - a constant
    - a variable
    - a lambda expression
*)
type case =
  | CConst of int * name * bool
      (** [(size,name,ac)] where [size] is the number of arguments expected for the
      constant [c] and [ac] is true iff the constant is a definable AC(U) symbol. *)
  | CDB of int * int
      (** [(size,db_index)] where [size] is the number of *static* arguments expected
      for the bounded variable [db_index] *)
  | CLam  (** A lambda headed term *)

(** An atomic matching problem.
     stack.(pos) ~? X[ DB(args_0), ..., DB(args_n)]
  where X is the variable and the problem is considered under depth abstractions.*)
type atomic_problem = {
  a_pos : int;  (** position of the term to match in the stack. *)
  a_depth : int;  (** depth of the argument regarding absractions *)
  a_args : int array;  (** Arguments DB indices (distinct bound variables) *)
}

(** A matching problem to build a solution context from the stack *)
type matching_problem = atomic_problem LList.t

(** Type of decision trees *)
type dtree =
  | Switch of int * (case * dtree) list * dtree option
      (** [Switch i \[(case_0,tree_0) ; ... ; (case_n, tree_n)\] default_tree]
      tests whether the [i]-th argument in the stack matches with one of the given cases.
      If it does then proceed with the corresponding tree
      Otherwise, branch to the given default tree. *)
  | Test of rule_name * pre_matching_problem * constr list * term * dtree option
      (** [Test name pb cstrs rhs default_tree] are the leaves of the tree.
      Checks that each problem can be solved such that constraints are satisfied.
      If it does then return a local context for the term [rhs]. *)
  | Fetch of int * case * dtree * dtree option
      (** [Fetch i case tree_suc tree_def] assumes the [i]-th argument of a pattern is a
   * flattened AC symbols and checks that it contains a term that can be matched with the given
   * case.
   * If so then look at the corresponding tree, otherwise/afterwise, look at the default tree *)
  | ACEmpty of int * dtree * dtree option
      (** [ACEmpty i tree_suc tree_def] assumes the [i]-th argument of a pattern is a
   * flattened AC symbols and checks that it is now empty. *)

(** Type mapping arities to decision trees (also called "forest") *)
type t

(** Empty forest for a free algebra *)
val empty : t

(** [find_dtree ar forest] returns a pair (arity,dtree) in given forest
    such that arity <= ar. Returns [None] when not found. *)
val find_dtree : int -> t -> algebra * (int * dtree) option

(** Printer for a single decision tree. *)
val pp_dtree : dtree printer

(** Printer for forests of decision trees. *)
val pp_dforest : t printer

(** Compilation of rewrite rules into decision trees.
    Returns a list of arities and corresponding decision trees.
    Invariant : arities must be sorted in decreasing order.
    (see use case in [state_whnf] in [reduction.ml])
    May raise Dtree_error.
*)
val of_rules : name -> (name -> algebra) -> rule_infos list -> t
