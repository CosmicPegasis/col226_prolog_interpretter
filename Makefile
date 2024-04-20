run: parser.cmo lexer.cmo
	utop parser.cmo lexer.cmo -init main.ml

lexer.cmo: lexer.ml
	ocamlc -c lexer.ml

parser.cmo: parser.mli lexer.ml ast.ml
	ocamlc -c ast.ml parser.mli
	ocamlc -c parser.ml

parser.mli: parser.mly
	ocamlyacc parser.mly

lexer.ml: lexer.mll
	ocamllex lexer.mll

clean:
	rm *.mli *.cmi *.cmo
	rm lexer.ml
	rm parser.ml

