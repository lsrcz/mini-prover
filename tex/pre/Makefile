JOBNAME = pre
AUX = pre
SUF = log aux toc thm out blg bbl ps dvi tex~ vrb nav snm


make:
	xelatex -shell-escape $(JOBNAME).tex

clean:
	rm -rf $(foreach i, $(AUX),$(foreach j, $(SUF),$(i).$(j))) _minted-pre
