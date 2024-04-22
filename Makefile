run: parser.cmo lexer.cmo main.ml
	utop parser.cmo lexer.cmo -init main.ml

debug: parser.cmo lexer.cmo main.ml
	ocamlc -g parser.cmo lexer.cmo main.ml
	ocamldebug a.out

lexer.cmo: lexer.ml
	ocamlc -c -g lexer.ml

parser.cmo: parser.mli lexer.ml ast.ml
	ocamlc -c -g ast.ml parser.mli
	ocamlc -c -g parser.ml

parser.mli: parser.mly
	ocamlyacc parser.mly

lexer.ml: lexer.mll
	ocamllex lexer.mll

clean:
	rm *.mli *.cmi *.cmo
	rm *.out
	rm lexer.ml
	rm parser.ml

