.PHONY: clean

tscalc_proofs.pdf: tscalc_simple.tex tscalc_proofs.tex
	latexmk -pdf tscalc_proofs.tex

tscalc_simple.tex: tscalc_simple.ott
	ott tscalc_simple.ott -o tscalc_simple.tex -tex_wrap false -tex_show_meta false

clean:
	latexmk -C
	rm -f tscalc_simple.tex
