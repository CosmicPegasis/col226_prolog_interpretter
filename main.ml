let construct_db db =
  let (Ast.Ex d) = Lexer.p db in
  d
;;

open Ast

exception NoMatchingRule

let rec find_match e db =
  match db with
  | Fact (Args (e', p)) :: tl ->
    if e = e' then Fact (Args (e', p)), tl else find_match e tl
  | Rule (Args (e', p), b) :: tl ->
    if e = e' then Rule (Args (e', p), b), tl else find_match e tl
  | _ -> raise NoMatchingRule
;;

type ans =
  | True
  | False
  | Conditional of (string * atom) list

exception CanSubstOnlyFacts

let rec subst_helper l p =
  match l with
  | [] -> p
  | (var_name, structure) :: tl ->
    subst_helper
      tl
      (List.map
         (fun x ->
           match x with
           | Variable v -> if v = var_name then structure else Variable v
           | a -> a)
         p)
;;

let rec subst tables expr =
  match tables, expr with
  | True, expr -> expr
  | False, expr -> expr
  | Conditional l, Fact (Args (e, p)) -> Fact (Args (e, subst_helper l p))
  | _, _ -> raise CanSubstOnlyFacts
;;

exception MoreThanOneQuery
exception InvalidQuery
exception NotUnifiable
exception MGUOnlyWorksWithArgs
exception MGUOnlyHandlesVarsAndConsts

let rec find_mgu l1 l2 =
  let mgu_helper e1 e2 =
    match e1, e2 with
    | Variable a1, Variable a2 ->
      if a1 = a2 then True else Conditional [ a2, Variable a1 ]
    | Variable a1, Constant a2 -> Conditional [ a1, Constant a2 ]
    | Constant a1, Variable a2 -> Conditional [ a2, Constant a1 ]
    | Constant a1, Constant a2 -> if a1 = a2 then True else False
    | _, _ -> raise MGUOnlyHandlesVarsAndConsts
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
    x
  | [], [] -> True
  | _ -> False
;;

let rec print_conditional l =
  match l with
  | (var_name, structure) :: tl ->
    let () =
      match structure with
      | Variable v -> Printf.printf "(Var %s, Var %s), " var_name v
      | Constant v -> Printf.printf "(Var %s Constant %s), " var_name v
      | _ -> ()
    in
    print_conditional tl
  | [] -> print_string " "
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

let rec consult_help expr db =
  try
    let e, p =
      match expr with
      | Fact (Args (e, p)) -> e, p
      | _ -> raise InvalidQuery
    in
    let expr', rem = find_match e db in
    match expr' with
    (* | Fact(Args(e, p')) -> [find_mgu p p'] *)
    | Fact (Args (e, p')) -> find_mgu p p' :: consult_help expr rem
    (*We unify we the argument list as well as the children*)
    | Rule (Args (e, p'), Body b) ->
      let initial_mgu = find_mgu p p' in
      let factual_body =
        List.map
          (fun x -> Fact x)
          (List.filter
             (fun x ->
               match x with
               | Args (f, g) -> true
               | _ -> false)
             b)
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
          (rule_uni [ initial_mgu ] factual_body db)
      in
      (* let () = print_endline " " in
         let () = print_mgu (List.filter (fun x -> x <> False) new_mgus) in *)
      new_mgus
    | _ -> [ True ]
  with
  | NoMatchingRule -> [ False ]

and rule_uni mgus atoms db =
  (* let () = print_endline "called rule_uni" in *)
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
      (consult_help (subst mgu atom) db)
  in
  match atoms with
  | atom :: rem_atoms ->
    (* first we need to find all possible new mgus for this particular atom*)
    let new_mgus = List.fold_left (fun acc cur -> acc @ get_new_mgu atom cur) [] mgus in
    (* let () = print_mgu (List.filter (fun x -> x <> False) new_mgus) in *)
    rule_uni new_mgus rem_atoms db
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

let consult expr db =
  let (Ex parsed_expr) = Lexer.p expr in
  let single_formatter parsed_expr =
    let parsed_expr =
      match parsed_expr with
      | Fact (Args (e, p)) ->
        Fact
          (Args
             ( e
             , List.map
                 (fun x ->
                   match x with
                   | Variable a -> Variable (a ^ "@")
                   | Constant a -> Constant a
                   | _ -> raise MGUOnlyHandlesVarsAndConsts)
                 p ))
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
  answer_formatter @@ List.filter (fun x -> False <> x) (rule_uni [ True ] parsed_expr db)
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
