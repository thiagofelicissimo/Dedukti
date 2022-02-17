module B = Kernel.Basic
module T = Kernel.Term
module C = Constraints
module U = Universes
open Str

let remove_dup l =
  List.fold_left (fun acc x -> if List.mem x acc then acc else (x :: acc) ) [] l
                                                             
let get_var_list l =  
  let rec get_var l =
    match l with
    | U.LVar x -> [x]
    | U.LZero -> []
    | U.LSucc t -> get_var t
    | U.LMax (t, s) -> get_var t @ get_var s
  in let var_list = List.fold_left (fun acc x -> (get_var x) @ acc) [] l in
     remove_dup var_list

let rec find_y l x =
  match l with
  | [] -> None
  | (x', y') :: l' -> if x' = x then Some y' else find_y l' x
                                                             
let rec print_lvl l =
  match l with
  | U.LVar s -> "l" ^ s
  | U.LMax (s1, s2) -> "(cts.max " ^ (print_lvl s1) ^ " " ^ (print_lvl s2) ^ ")"
  | U.LZero -> "cts.zero"
  | U.LSucc s -> "(cts.succ " ^ (print_lvl s) ^ ")"

let read_lines fp =
  let lines = ref [] in
  try
    while true do
      lines := (input_line fp) :: !lines
    done; !lines
  with
    _ -> !lines


let rec appears_in (name : string) (i : U.univ) =
  match i with
  | U.LVar s -> name = s
  | U.LSucc s -> appears_in name s
  | U.LMax (s,k) -> (appears_in name s) || (appears_in name k)
  | _ -> false

let rec substitute (t : U.univ) (n : string) (u : U.univ) =
  match t with
  | U.LVar m -> if n = m then u else U.LVar m
  | U.LSucc t' -> U.LSucc (substitute t' n u)
  | U.LMax (t1, t2) -> U.LMax (substitute t1 n u, substitute t2 n u)
  | _ -> t


let rec simplify t =
  match t with
  | U.LMax (t1, t2) ->
     let t1' = simplify t1 in
     let t2' = simplify t2 in
     if t1' = U.LZero then t2'
     else if t2' = U.LZero then t1'
     else if t1' = t2' then t1'
     else if t1' = U.LSucc t2' then t1'
     else if t2' = U.LSucc t1' then t2'
     else U.LMax (t1', t2')
  | U.LSucc t1 -> U.LSucc (simplify t1)
  | x -> x
  
let rec unify (subst : (string * U.univ) list) (l : (U.univ * U.univ) list) : (string * U.univ) list option =
  match l with
  | [] -> Some subst
  | (U.LZero, U.LZero) :: l' -> unify subst l'
  | (U.LVar m, t) :: l' ->
     if U.LVar m = t then unify subst l'
     else if appears_in m t
     then None
     else
       let new_subst = (m, t) :: (List.map (fun (n, s) -> n, simplify (substitute s m t)) subst) in
       let new_l = List.map (fun (x,y) -> simplify (substitute x m t), simplify (substitute y m t)) l in
       unify new_subst new_l
  | (t, U.LVar m) :: l' -> unify subst ((U.LVar m, t) :: l')
  | (U.LSucc t1, U.LSucc t2) :: l' -> unify subst ((t1, t2) :: l')
  | (U.LMax (t1, s1), U.LMax (t2, s2)) :: l' -> unify subst ((t1, t2) :: (s1, s2) :: l')
  | _ :: _ -> None

exception E
            
let rec add_up fin fout list_var =
  let rec generate_up_prod l =
    match l with
    | [] -> ""
    | x :: l' -> " (l" ^ x ^ " : cts.Sort) ->" ^ generate_up_prod l' in       
  let rec generate_up_abs l =
    match l with
    | [] -> ""
    | x :: l' -> " l" ^ x ^ " =>" ^ generate_up_abs l' in         
  let require = Str.regexp "#REQUIRE" in
  let def = Str.regexp ":=" in
  let decl = Str.regexp ":" in
  let s = ref (input_line fin) in        
  try (* removes #REQUIRE *)
    while true do
      let _ = search_forward require !s 0 in      
      s := input_line fin
    done; ()
  with
    _ ->
    (* prints (x1 : cts.Sort) -> ... *)
    let with_quantification = replace_first decl (": " ^ (generate_up_prod list_var)) !s in
    Printf.fprintf fout "%s\n" with_quantification;
    (* prints x1 => x2 => ... *)    
    try
      while true do
        s := input_line fin;
        try
          let _ = search_forward def !s 0 in 
          Printf.fprintf fout "%s%s\n" !s (generate_up_abs list_var)
        with _ ->
          Printf.fprintf fout "%s\n" !s
      done; ()
    with _ -> ()

            
let rec substitute_in_string (subst : (string * U.univ) list) (s : string) var_list =
  let reg = Str.regexp "\\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\)" in
  let reg_of file lvl = Str.regexp (file ^ ".\\?" ^ lvl) in  
  let s = ref s in
  try while true do
        let _ = search_forward reg !s 0 in
        let file_id = matched_group 1 !s in
        let lvl_id = matched_group 2 !s in
        let exp =
          match find_y subst ("?" ^ lvl_id) with
          | Some y -> print_lvl y
          | None -> var_list := ("?" ^ lvl_id) :: !var_list; ("l?" ^ lvl_id) in
        s := global_replace (reg_of file_id lvl_id) exp !s
        (*        Printf.printf "%s\n" !s        *)
      done; !s
  with _ -> !s

let rec substitute_in_file subst fin fout =
  let var_list = ref [] in
  try
    while true do
      let s = input_line fin in
      let s' = substitute_in_string subst s var_list in
      Printf.fprintf fout "%s\n" s' 
    done; raise E
  with
    _ -> !var_list

let to_dependencies fmt n name =
  let rec n_star n =
    if n = 0 then ""
    else " cts.star" ^ n_star (n-1)
  in
  Printf.fprintf fmt "(%s.%s %s)" name name (n_star n) 
       
exception NoSolution

let get_vars_in_line s varlist =
  let reg = Str.regexp "l\\?\\([A-Za-z0-9_\\?]+\\)" in
  let i = ref 0 in
  try while true do
        i := 1 + search_forward reg !s !i;
        let lvl_id = matched_group 1 !s in
        varlist := ("?" ^ lvl_id) :: !varlist
        (*        s := global_replace (Str.regexp ("l\\?" ^ lvl_id)) ("l?" ^ lvl_id) !s*)
      done with _ -> ()

exception No_such_y
                   
let rec substitute_in_string2 (subst : (string * U.univ) list) (s : string ref) =
  let reg = Str.regexp "l\\?\\([A-Za-z0-9_\\?]+\\)" in
  (*  let reg_of file lvl = Str.regexp (file ^ ".\\?" ^ lvl) in  *)
  let i = ref 0 in
  try while true do
        i := 1 + search_forward reg !s !i;
        let lvl_id = matched_group 1 !s in
        let exp =
          match find_y subst ("?" ^ lvl_id) with
          | Some y -> print_lvl y
          | None -> raise No_such_y in
        s := global_replace (Str.regexp ("l\\?" ^ lvl_id)) exp !s
        (*        Printf.printf "%s\n" !s        *)
      done
  with Not_found -> ()
  
  

                   
let get_lvl_vars_in_type allvar fin fout =
  let varlist = ref [] in
  let def = Str.regexp ":=" in  
  let break_if_end_of_type s =
    try
      let _ = search_forward def s 0 in
      raise E
      with Not_found -> ()
  in
  let s = ref "" in
  try
    while true do
      s := input_line fin;
      (* we stop when we find :=, the type is over *)
      break_if_end_of_type !s;
      get_vars_in_line s varlist;
      Printf.fprintf fout "%s\n" !s
    done; raise Not_found
  with
  | Not_found -> remove_dup !varlist
  | End_of_file -> remove_dup !varlist               
  | E ->
     let varlist = remove_dup !varlist in
     let subst = List.map
                   (fun x -> if List.mem x varlist
                             then (x, U.LVar x)
                             else (x, U.LZero)
                   ) 
                   allvar in
     try while true do
           substitute_in_string2 subst s;
           Printf.fprintf fout "%s\n" !s;
           s := input_line fin
         done; varlist
         with End_of_file -> varlist
     
let extract_name filename =
  let reg = Str.regexp "\\([A-Za-z0-9_\\?]+\\)/\\([A-Za-z0-9_\\?]+\\).dk" in
  let _ = search_forward reg filename 0 in
  matched_group 2 filename


let extra_cstr name =
  match name with
  | "True" | "False" -> C.equations := (U.LVar "?1", U.LZero) :: (!C.equations)
  | "Or" | "And" ->
     C.equations := (U.LVar "?4", U.LZero) ::
                      (U.LVar "?9", U.LZero) ::
                        (U.LVar "?11", U.LZero) :: (!C.equations)
  | "nat" -> C.equations := (U.LVar "?0", U.LSucc U.LZero) :: (!C.equations)
  | "match_And_prop" -> C.equations := (U.LVar "?23", U.LVar "?22") :: (!C.equations)
  | "match_Or_prop" -> C.equations := (U.LVar "?25", U.LVar "?20") :: (!C.equations)             
  | "le" -> C.equations := (U.LVar "?7", U.LZero) :: (!C.equations)           
  | "eq" -> C.equations := (U.LVar "?6", U.LVar "?12") :: (!C.equations)
  | "Not" -> C.equations := (U.LVar "?4", U.LZero) :: (U.LVar "?6", U.LVar "?4") :: (!C.equations) 
  | "equal" -> C.equations := (U.LVar "?6", U.LVar "?12") :: (!C.equations)          
  | "bool" -> C.equations := (U.LVar "?0", U.LSucc U.LZero) :: (!C.equations)
  (*  | "bool_discr" -> C.equations := (U.LVar "?11", U.LSucc (U.LSucc U.LZero)) :: (!C.equations)*)
  | _ -> ()       

let solve_and_subst file =
  let name = extract_name file in
  extra_cstr name;
  let input_file = open_in file in
  let temp_file = open_out "temp.dk" in
  let new_equations = List.map (fun (a, b) -> simplify a, simplify b) !C.equations in
  let subst =
    match unify [] new_equations with
    | Some x -> x
    | _ -> raise NoSolution in
  let all_var_list = substitute_in_file subst input_file temp_file in
  close_in input_file;
  close_out temp_file;
  let temp_file = open_in "temp.dk" in
  let temp2_file = open_out "temp2.dk" in  
  let varlist = get_lvl_vars_in_type all_var_list temp_file temp2_file in
  Printf.printf "N of free lvl var = %s\n" (string_of_int (List.length varlist));  
  close_in temp_file;
  close_out temp2_file;  
  let temp2_file = open_in "temp2.dk" in
  let output_file = open_out file in  
  (*  let var_list = get_var_list (List.map (fun (x,y) -> y) subst) in*)
  add_up temp2_file output_file varlist;
  let todep_file = open_out "todep" in
  to_dependencies todep_file (List.length varlist) name;
  close_out todep_file;
  close_out output_file;
  close_in temp2_file



  
(*        

let () =
  let name = Sys.argv.(1) in
  let input_file_name = name ^ ".dk" in
  let constraints_file_name = name ^ "_cstr.dk" in
  let input_file = open_in input_file_name in
  let constraints_file = open_in constraints_file_name in
  let temp_file = open_out "temp.dk" in
  let lines = read_lines constraints_file in
  let consts = read_constraints lines in
  let subst =
    match unify [] consts with
    | Some x -> x
    | _ -> raise NoSolution in
  let var_list = substitute_in_file subst input_file temp_file in
  close_out temp_file;
  let temp_file = open_in "temp.dk" in
  let output_file = open_out "out.dk" in  
  (*  let var_list = get_var_list (List.map (fun (x,y) -> y) subst) in*)
  add_up temp_file output_file var_list;
  to_dependencies (List.length var_list) name;
  close_in input_file;
  close_in constraints_file
 *)
          
