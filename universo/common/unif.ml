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
  | U.LVar s -> s
  | U.LMax (s1, s2) -> "(cts.max " ^ (print_lvl s1) ^ " " ^ (print_lvl s2) ^ ")"
  | U.LZero -> "(cts.enum cts.uzero)"
  | U.LSucc s -> "(cts.succ " ^ (print_lvl s) ^ ")"
(*                                                             
let str_to_constraint str =
  let match_equal = Str.regexp "\\[\\] \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\) --> \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\)." in
  let match_ax = Str.regexp "Axiom \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\) \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\)" in
  let match_rule = Str.regexp "Rule \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\) \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\) \\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\)" in
  try
    let _ = search_forward match_ax str 0 in
    let t1 = "l" ^ matched_group 2 str in
    let t2 = "l" ^ matched_group 4 str in
    Some (Lsucc (Var t1), Var t2)
  with
    _ -> try
      let _ = search_forward match_rule str 0 in
      let t1 = "l" ^ matched_group 2 str in
      let t2 = "l" ^ matched_group 4 str in
      let t3 = "l" ^ matched_group 6 str in
      Some (Max (Var t1, Var t2), Var t3)
    with
      _ -> try
        let _ = search_forward match_equal str 0 in
        let t1 = "l" ^ matched_group 2 str in
        let t2 = "l" ^ matched_group 4 str in
        Some (Var t1, Var t2)
      with _ -> None
           

let read_constraints line_list =
  List.fold_left
    (fun acc s ->
      match str_to_constraint s with
      | None -> acc
      | Some x -> x :: acc)
    []
    line_list

let read_lines fp =
  let lines = ref [] in
  try
    while true do
      lines := (input_line fp) :: !lines
    done; !lines
  with
    _ -> !lines


let rec appears_in (name : string) (i : lvl) =
  match i with
  | Var s -> name = s
  | Max (s,k) -> (appears_in name s) || (appears_in name k)
  | _ -> false

let rec substitute (t : lvl) (n : string) (u : lvl) =
  match t with
  | Var m -> if n = m then u else Var m
  | Lsucc t' -> Lsucc (substitute t' n u)
  | Max (t1, t2) -> Max (substitute t1 n u, substitute t2 n u)
  | _ -> t
       
let rec unify (subst : (string * lvl) list) (l : (lvl * lvl) list) : (string * lvl) list option =
  match l with
  | [] -> Some subst
  | (Var m, t) :: l' ->
     if Var m = t then unify subst l'
     else if appears_in m t then None
     else
       let new_subst = (m, t) :: (List.map (fun (n, s) -> n, substitute s m t) subst) in
       let new_l = List.map (fun (x,y) -> substitute x m t, substitute y m t) l in
       unify new_subst new_l
  | (t, Var m) :: l' -> unify subst ((Var m, t) :: l')
  | (Lsucc t1, Lsucc t2) :: l' -> unify subst ((t1, t2) :: l')
  | (Max (t1, s1), Max (t2, s2)) :: l' -> unify subst ((t1, t2) :: (s1, s2) :: l')
  | _ :: l -> None

exception E
            
let rec add_up fin fout list_var =
  let rec generate_up_prod l =
    match l with
    | [] -> ""
    | x :: l' -> " (" ^ x ^ " : cts.Sort) ->" ^ generate_up_prod l' in       
  let rec generate_up_abs l =
    match l with
    | [] -> ""
    | x :: l' -> " " ^ x ^ " =>" ^ generate_up_abs l' in         
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

            
let rec substitute_in_string (subst : (string * lvl) list) (s : string) var_list =
  let reg = Str.regexp "\\([A-Za-z0-9_\\?]+\\).\\?\\([A-Za-z0-9_\\?]+\\)" in
  let reg_of file lvl = Str.regexp (file ^ ".\\?" ^ lvl) in  
  let s = ref s in
  try while true do
        let _ = search_forward reg !s 0 in
        let file_id = matched_group 1 !s in
        let lvl_id = matched_group 2 !s in
        let exp =
          match find_y subst ("l" ^ lvl_id) with
          | Some y -> print_lvl y
          | None -> var_list := ("l" ^ lvl_id) :: !var_list; "l" ^ lvl_id in
        s := global_replace (reg_of file_id lvl_id) exp !s
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

let to_dependencies n name =
  let rec n_star n =
    if n = 0 then ""
    else " cts.star" ^ n_star (n-1)
  in Printf.printf "(%s.%s %s)" name name (n_star n) 
       
exception NoSolution
        
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
