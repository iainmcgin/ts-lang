.PHONY: clean

paper.pdf: paper.tex ts_defns.tex principal.pdf sm1.pdf simulation.pdf
	latexmk -pdf paper.tex

ts_proofs.pdf: ts_proofs.tex ts_defns.tex
	latexmk -pdf ts_proofs.tex

ts_defns.tex: ts.ott
	ott ts.ott -o ts_defns.tex -tex_wrap false -tex_show_meta false

clean:
	latexmk -C
	rm -f ts_defns.tex
