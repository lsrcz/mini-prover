JOBNAME = report
AUX = appendix conclusion introduction parser proofhandling reduction report safetycheck syntax tactic toplevel typing usage
SUF = log aux toc thm out blg bbl ps dvi tex~


make:
	xelatex $(JOBNAME).tex

clean:
	rm -rf $(foreach i, $(AUX),$(foreach j, $(SUF),$(i).$(j)))
