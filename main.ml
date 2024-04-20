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
  let rec iter key l =
    match l with
    | (k, v) :: tl -> if k = key then v else iter key tl
    | [] -> Variable key
  in
  match p with
  | Variable a :: tl -> iter a l :: subst_helper l tl
  | b :: tl -> b :: subst_helper l tl
  | [] -> []
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
      if a1 = a2 then True else Conditional [ a1, Variable a2 ]
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
          | Conditional l' -> Conditional (l' @ l)
        in
        x
      | True -> find_mgu tl1 tl2
      | False -> False
    in
    x
  | [], [] -> True
  | _ -> False
;;

let rec consult_help expr db =
  try
    let e, p =
      match expr with
      | Fact (Args (e, p)) -> e, p
      | _ -> raise InvalidQuery
    in
    let rec rule_uni mgus atoms =
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
               | Conditional l' -> Conditional (l @ l')))
          (consult_help (subst mgu atom) db)
      in
      match atoms with
      | atom :: rem_atoms ->
        (* first we need to find all possible new mgus for this particular atom*)
        let new_mgus =
          List.fold_left (fun acc cur -> acc @ get_new_mgu atom cur) [] mgus
        in
        let new_mgus = new_mgus in
        rule_uni new_mgus rem_atoms
      | [] -> mgus
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
            | Conditional l, Conditional l' -> Conditional (l @ l'))
          (rule_uni [ initial_mgu ] factual_body)
      in
      new_mgus
    | _ -> [ True ]
  with
  | NoMatchingRule -> [ False ]
;;

let rec cleanup ans =
  let rec trim l =
    match l with
    | Conditional l' :: tl ->
      Conditional
        (List.filter
           (fun (var_name, structure) -> String.ends_with ~suffix:"@" var_name)
           l')
      :: trim tl
    | True :: tl -> True :: trim tl
    | False :: tl -> False :: trim tl
    | [] -> []
  in
  List.map
    (fun x ->
      match x with
      | Conditional [] -> True
      | Conditional l -> Conditional l
      | True -> True
      | False -> False)
    (trim ans)
;;

let consult expr db =
  let parsed_expr =
    match Lexer.p expr with
    | Ast.Ex [ d ] -> d
    | _ -> raise MoreThanOneQuery
  in
  let ans = List.filter (fun x -> x != False) (consult_help parsed_expr db) in
  if List.mem True ans
  then [ True ]
  else if cleanup ans = []
  then [ False ]
  else cleanup ans
;;
