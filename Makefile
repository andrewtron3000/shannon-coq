all: proofs docs paper tex

proofs: computational.v
	coqc computational.v

docs: computational.v 
	coqdoc --no-preamble -s --latex -d documentation computational.v

paper: computational.v 
	cd documentation && \
	cat preamble.tex > paper.tex && \
	cat computational.tex >> paper.tex && \
	cat trailer.tex >> paper.tex 

tex: computational.v 
	cd documentation && \
	pdflatex paper.tex && \
	bibtex paper.aux && \
	pdflatex paper.tex && \
	pdflatex paper.tex

clean:
	rm -f *~ .*.aux *.glob *.vo documentation/*.aux documentation/*.log documentation/*.out documentation/*.pdf documentation/*.bbl documentation/*.blg documentation/computational.tex documentation/coqdoc.sty
