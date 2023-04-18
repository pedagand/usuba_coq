main.pdf : main.tex main.bib rules.tex
	latexmk -pdf main --shell-escape

main.tex : main.htex rules.ott
	ott -i rules.ott -tex_filter $< $@

rules.tex : rules.ott
	ott -i rules.ott -o rules.tex -picky_multiple_parses false -tex_show_meta false -tex_wrap false -tex_suppress_category S

all: main.pdf

cleans = main.tex rules.tex main.bbl main.run.xml

clean:
	latexmk -c
	rm -rf $(cleans)

.PHONY: all clean
