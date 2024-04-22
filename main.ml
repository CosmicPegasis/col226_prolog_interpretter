let construct_db db =
  let (Ast.Ex d) = Lexer.p db in
  d
;;

open Ast

type ans =
  | True
  | False
  | Conditional of (string * atom) list

exception NoMatchingRule
exception UnhandledMGUCase

let rec find_match e db =
  match db with
  | Fact (Args (e', p)) :: tl ->
    if e = e' then Fact (Args (e', p)), tl else find_match e tl
  | Rule (Args (e', p), b) :: tl ->
    if e = e' then Rule (Args (e', p), b), tl else find_match e tl
  | _ -> raise NoMatchingRule
;;

exception UnhandledPrinterCase

let rec atom_printer arg =
  match arg with
  | Args (e, p) ->
    let () = print_string "Args(" in
    let () = print_string (e ^ " ") in
    let () = List.fold_left (fun acc elem -> atom_printer elem) () p in
    print_string ")"
  | Variable v -> print_string ("Variable: " ^ v ^ " ")
  | Constant c -> print_string ("Constant: " ^ c ^ " ")
  | Atom a -> atom_printer a
  | _ -> raise UnhandledPrinterCase
;;

let rec print_conditional l =
  match l with
  | (var_name, structure) :: tl ->
    let () =
      match structure with
      | Variable v -> Printf.printf "(Var %s, Var %s), " var_name v
      | Constant v -> Printf.printf "(Var %s Constant %s), " var_name v
      | Args (e, p) ->
        let _ = print_string (var_name ^ " ") in
        atom_printer (Args (e, p))
      | _ -> raise UnhandledMGUCase
    in
    print_conditional tl
  | [] -> print_string ""
;;

let rec print_mgu mgu =
  match mgu with
  | True :: tl ->
    let () = print_string "true\n" in
    print_mgu tl
  | False :: tl ->
    let () = print_string "false\n" in
    print_mgu tl
  | Conditional l :: tl ->
    let () = print_string "Conditional [" in
    let () = print_conditional l in
    let () = print_string "]\n" in
    print_mgu tl
  | [] -> print_endline ""
;;

let rec expr_printer expr =
  match expr with
  | Fact a ->
    let () = print_string "Fact(" in
    let _ = atom_printer a in
    print_string ")\n"
  | Const c -> print_string ("Constant " ^ c ^ "\n")
  | Rule (a, Body b) ->
    let _ = print_string "Rule(" in
    let () = atom_printer a in
    let _ = print_string "Body(" in
    let _ =
      List.map
        (fun x ->
          let _ = atom_printer x in
          print_string ",")
        b
    in
    let _ = print_string ")" in
    let _ = print_string ")\n" in
    ()
;;

exception CanSubstOnlyFacts

let rec subst_helper l p =
  match l with
  | [] -> p
  | (var_name, structure) :: tl ->
    subst_helper
      tl
      (let p =
         List.map
           (fun x ->
             match x with
             | Variable v -> if v = var_name then structure else Variable v
             | Args (e, p') ->
               (* let () = atom_printer (Args (e, p')) in *)
               Args (e, subst_helper [ var_name, structure ] p')
             | Constant a -> Constant a
             | Array l -> Array (subst_helper [ var_name, structure ] l)
             | _ -> raise UnhandledMGUCase)
           p
       in
       p)
;;

let rec subst tables expr =
  match tables, expr with
  | True, expr -> expr
  | False, expr -> expr
  | Conditional l, Fact (Args (e, p)) -> Fact (Args (e, subst_helper l p))
  | _, _ -> raise CanSubstOnlyFacts
;;

(* type atom =
   | Args of string * atom list
   | Variable of string
   | Constant of string
   | Atom of atom
   | Int of int
   | Array of atom list
   | Cut *)

exception MoreThanOneQuery
exception InvalidQuery
exception NotUnifiable
exception MGUOnlyWorksWithArgs

let rec find_mgu l1 l2 =
  let rec mgu_helper e1 e2 =
    match e1, e2 with
    | Variable a1, Variable a2 ->
      if a1 = a2 then True else Conditional [ a2, Variable a1 ]
    | Variable a1, structure -> Conditional [ a1, structure ]
    | structure, Variable a2 -> Conditional [ a2, structure ]
    | Constant a1, Constant a2 -> if a1 = a2 then True else False
    | Constant _, structure -> False
    | structure, Constant _ -> False
    | Args (e1, p1), Args (e2, p2) -> if e1 = e2 then find_mgu p1 p2 else False
    | Args ("|", [ a1; a2 ]), Array (hd :: tl) ->
      let x =
        match mgu_helper a1 hd with
        | True -> mgu_helper a2 (Array tl)
        | False -> False
        | Conditional l ->
          (match mgu_helper a2 (Array (subst_helper l tl)) with
           | True -> Conditional l
           | False -> False
           | Conditional l' -> Conditional (l' @ l))
      in
      x
    | Array (hd :: tl), Args ("|", p1) -> mgu_helper (Args ("|", p1)) (Array (hd :: tl))
    | a, Args (e1, p1) -> False
    | Args (e1, p1), a -> False
    | Array l1, Array l2 -> find_mgu l1 l2
    | _, _ -> raise UnhandledMGUCase
  in
  match l1, l2 with
  | hd1 :: tl1, hd2 :: tl2 ->
    let x =
      match mgu_helper hd1 hd2 with
      | Conditional l ->
        let x =
          match find_mgu (subst_helper l tl1) (subst_helper l tl2) with
          | True -> Conditional l
          | False -> False
          | Conditional l' -> Conditional (l @ l')
        in
        x
      | True -> find_mgu tl1 tl2
      | False -> False
    in
    (* let () = print_mgu [ x ] in *)
    x
  | [], [] -> True
  | _ -> False
;;

exception UnhandledRenameCase

let rec rename_variable i expr =
  match expr with
  | Variable v -> Variable (string_of_int i ^ " " ^ v)
  | Constant c -> Constant c
  | Args (e, p) -> Args (e, List.map (rename_variable i) p)
  | _ -> raise UnhandledRenameCase
;;

let rec consult_help expr cur_db db i =
  let e, p =
    match expr with
    | Fact (Args (e, p)) -> e, p
    | _ -> raise InvalidQuery
  in
  try
    let expr', rem = find_match e cur_db in
    match expr' with
    | Fact (Args (e, p')) ->
      let temp_mgu =
        find_mgu p (List.map (rename_variable i) p') :: consult_help expr rem db i
      in
      temp_mgu
    | Rule (Args (e, p'), Body b) ->
      let initial_mgu = find_mgu p (List.map (rename_variable i) p') in
      if initial_mgu = False
      then False :: consult_help expr rem db i
      else (
        let factual_body =
          List.map
            (fun x -> Fact x)
            (List.filter
               (fun x ->
                 match x with
                 | Args (f, g) -> true
                 | _ -> false)
               (List.map (rename_variable i) b))
        in
        let new_mgus =
          List.map
            (fun x ->
              match x, initial_mgu with
              | True, _ -> initial_mgu
              | False, _ -> False
              | Conditional l, True -> Conditional l
              | Conditional l, False -> False
              | Conditional l, Conditional l' -> Conditional (l' @ l))
            (rule_uni [ initial_mgu ] factual_body db (i + 1) @ consult_help expr rem db i)
        in
        new_mgus)
    | _ -> [ True ]
  with
  | NoMatchingRule -> [ False ]

and rule_uni mgus atoms db i =
  let get_new_mgu atom mgu =
    List.map
      (fun x ->
        match x with
        | True -> mgu
        | False -> False
        | Conditional l ->
          (match mgu with
           | True -> Conditional l
           | False -> False
           | Conditional l' -> Conditional (l' @ l)))
      (consult_help (subst mgu atom) db db i)
  in
  match atoms with
  | atom :: rem_atoms ->
    let new_mgus =
      List.filter (fun x -> x <> False)
      @@ List.fold_left (fun acc cur -> get_new_mgu atom cur) [] mgus
    in
    if new_mgus = [] then [ False ] else rule_uni new_mgus rem_atoms db i
  | [] -> mgus
;;

exception NotAVariable

let is_internal_var name = not (String.ends_with ~suffix:"@" name)

let rec subst_internal_variables l l' =
  let subst subst_var_name structure arr =
    List.filter
      (fun (var_name, str) -> var_name <> subst_var_name)
      (List.map
         (fun (var_name, structure') ->
           match structure' with
           | Variable name ->
             if name = subst_var_name then var_name, structure else var_name, structure'
           | _ -> var_name, structure')
         arr)
  in
  match l with
  | (var_name, structure) :: tl ->
    if is_internal_var var_name
    then (
      let l' = subst var_name structure l' in
      subst_internal_variables tl l')
    else subst_internal_variables tl l'
  | [] -> l'
;;

let rec cleanup ans =
  let rec trim_internal_variables l =
    match l with
    | Conditional l' :: tl ->
      let l' = subst_internal_variables l' l' in
      Conditional
        (List.filter (fun (var_name, structure) -> not (is_internal_var var_name)) l')
      :: trim_internal_variables tl
    | True :: tl -> True :: trim_internal_variables tl
    | False :: tl -> False :: trim_internal_variables tl
    | [] -> []
  in
  let trim_at_signs l =
    List.map
      (fun (var_name, structure) ->
        String.sub var_name 0 (String.length var_name - 1), structure)
      l
  in
  List.map
    (fun x ->
      match x with
      | Conditional [] -> True
      | Conditional l -> Conditional (trim_at_signs l)
      | True -> True
      | False -> False)
    (trim_internal_variables ans)
;;

exception ExpectedArgs
exception UnhandledFormatterCase

let consult expr db =
  let (Ex parsed_expr) = Lexer.p expr in
  let single_formatter parsed_expr =
    let rec format_args args =
      match args with
      | Args (e, p) -> Args (e, List.map general_formatter p)
      | _ -> raise ExpectedArgs
    and general_formatter x =
      match x with
      | Variable a -> Variable (a ^ "@")
      | Constant a -> Constant a
      | Args (e, p) -> format_args (Args (e, p))
      | Array l -> Array (List.map general_formatter l)
      | _ -> raise UnhandledFormatterCase
    in
    let parsed_expr =
      match parsed_expr with
      | Fact (Args (e, p)) -> Fact (format_args (Args (e, p)))
      | _ -> raise MGUOnlyWorksWithArgs
    in
    parsed_expr
  in
  let parsed_expr = List.map single_formatter parsed_expr in
  let answer_formatter ans =
    if List.mem True ans
    then [ True ]
    else if cleanup ans = []
    then [ False ]
    else cleanup ans
  in
  answer_formatter
  @@ List.filter (fun x -> False <> x) (rule_uni [ True ] parsed_expr db 0)
;;

(* in
   let ans = List.filter (fun x -> x <> False) (consult_help parsed_expr db) in *)

(*Test Cases*)

(* parent(john, mary).
   parent(john, peter).
   parent(jane, mary).
   parent(jane, peter).

   parent(mary, alice).
   parent(mary, bob).
   parent(peter, charlie).
   parent(peter, david).

   parent(alice, eve).
   parent(alice, frank).
   parent(bob, grace).
   parent(bob, henry).

   parent(charlie, ian).
   parent(charlie, jane).
   parent(david, kate).
   parent(david, lucy).

   child(X, Y) :- parent(Y, X).
*)
(* 1.
   consult "child(peter, john)." db
   - : ans list = [True] *)
(* 2.
   consult "child(X, Y)." db;;
   - : ans list =
     [Conditional [("Y", Constant "john"); ("X", Constant "mary")];
 Conditional [("Y", Constant "john"); ("X", Constant "peter")];
 Conditional [("Y", Constant "jane"); ("X", Constant "mary")];
 Conditional [("Y", Constant "jane"); ("X", Constant "peter")];
 Conditional [("Y", Constant "mary"); ("X", Constant "alice")];
 Conditional [("Y", Constant "mary"); ("X", Constant "bob")];
 Conditional [("Y", Constant "peter"); ("X", Constant "charlie")];
 Conditional [("Y", Constant "peter"); ("X", Constant "david")];
 Conditional [("Y", Constant "alice"); ("X", Constant "eve")];
 Conditional [("Y", Constant "alice"); ("X", Constant "frank")];
 Conditional [("Y", Constant "bob"); ("X", Constant "grace")];
 Conditional [("Y", Constant "bob"); ("X", Constant "henry")];
 Conditional [("Y", Constant "charlie"); ("X", Constant "ian")];
 Conditional [("Y", Constant "charlie"); ("X", Constant "jane")];
 Conditional [("Y", Constant "david"); ("X", Constant "kate")];
 Conditional [("Y", Constant "david"); ("X", Constant "lucy")]]*)

(* 3.
   consult "child(X, X)." db
   - : ans list = [False]*)

(*
   "mem(aviral, bhu).
   mem(singh,bhu).
   together(X, Y) :-
   mem(X, bhu),
   mem(Y, bhu)."
*)
(*
   4. together(aviral, bhu).
   false
   5. together(aviral, singh).
   true
   6. together(X, Y).
   [Conditional [("X", Constant "aviral"); ("Y", Constant "aviral")];
    Conditional [("X", Constant "aviral"); ("Y", Constant "singh")];
    Conditional [("X", Constant "singh"); ("Y", Constant "aviral")];
    Conditional [("X", Constant "singh"); ("Y", Constant "singh")]]
   7. mem(aviral, bhu).
   true
   8. mem(singh, bhu).
   true
   9. mem(X, bhu).
   [Conditional [("X", Constant "aviral")]; Conditional [("X", Constant "singh")]
*)

(*
   person(john).
   person(mary).
   person(bob).
   person(alice).

   course(cs101).
   course(math201).
   course(eng105).

   enrolled(john, cs101).
   enrolled(john, math201).
   enrolled(mary, cs101).
   enrolled(bob, eng105).
   enrolled(alice, math201).

   instructor(mary, cs101).
   instructor(bob, math201).

   takes(X, Y) :- enrolled(X, Y).
   teaches(X, Y) :- instructor(X, Y).

   10. takes(john, X).
   [Conditional [("X", Constant "cs101")];
    Conditional [("X", Constant "math201")]]
   11. teaches(X, Y).
   [Conditional [("X", Constant "mary"); ("Y", Constant "cs101")];
    Conditional [("X", Constant "bob"); ("Y", Constant "math201")]]
*)

let db =
  construct_db
    "mem(X,[X|T]).\n\
     mem(X,[H|R]) :- mem(X,R). \n\
     mem(X,inter(S1,S2)) :- mem(X,S1),mem(X,S2).\n"
;;

(*mem(X,union(S1,S2)) :- mem(X,S1).\n\
  mem(X,union(S1,S2)) :- mem(X,S2). \n*)

(* consult "mem(2, union([1], [2]))." db;;

   (*emulates prolog behavior for this test case*)
   consult "mem(X, union([1,2,3], [2,3,4]))." *)

(*- : ans list =
    [Conditional [("X", Constant "1")]; Conditional [("X", Constant "2")];
 Conditional [("X", Constant "3")]; Conditional [("X", Constant "2")];
 Conditional [("X", Constant "3")]; Conditional [("X", Constant "4")]]*)
consult "mem(1, inter([1], [2]))." db;;

(* - : ans list = [False] *)
consult "mem(1, inter([1,2], [2]))." db;;

(* - : ans list = [False] *)
consult "mem(2, inter([1,2], [2]))." db;;

(* - : ans list = [True] *)
consult "mem(2, inter([1,2], [2,3]))." db;;

(* - : ans list = [True] *)
consult "mem(3, inter([1,2], [2,3]))." db;;

(* - : ans list = [False] *)
consult "mem(3, inter([3,1,2], [2,3]))." db
(* - : ans list = [True] *)
