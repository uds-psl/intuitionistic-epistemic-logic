.PHONY : all coq html website clean

all: coq html website

html:
	$(MAKE) -C coq html

coq:
	$(MAKE) -C coq

website:
	$(MAKE) -C coq html
	mv coq/html/*html website
	rm -rf coq/html

clean:
	$(MAKE) -C coq clean
	rm -f website/*html

count:
	coqwc coq/BPCP_CND.v coq/BPCP_FOL.v coq/BPCP_IFOL.v coq/Deduction.v coq/FOL.v coq/Kripke.v coq/PCP.v coq/Semantics.v coq/Synthetic.v coq/Weakening.v

push: website
	rsync -v website/*.html forster@james.ps.uni-saarland.de:/srv/ps/httpd/html/extras/fol-undec/website/ 
