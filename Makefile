COQC=coqc -Q . AbstractInterpretation

check: clean
	$(COQC) Sigmas.v
	$(COQC) Ensembles.v
	$(COQC) Maps.v
	$(COQC) Order.v
	$(COQC) Graph.v
	$(COQC) Environment.v
	$(COQC) Expression.v
	$(COQC) ExpressionSemantics.v
	$(COQC) CFG.v
	$(COQC) CFGSemantics.v
	$(COQC) CompleteBoolDomain.v
	$(COQC) ValueDomain.v
	$(COQC) Domain.v
	$(COQC) NonRelationalDomain.v
	$(COQC) Iterator.v

clean:
	rm -f *.vo *.vok *.vos *.glob
