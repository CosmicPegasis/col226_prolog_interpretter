type atom =
  | Args of string * atom list
  | Variable of string
  | Constant of string
  | Array of atom list
  | Atom of atom

type body = Body of atom list

type expr =
  | Fact of atom
  | Const of string
  | Rule of atom * body

type program = Ex of expr list
