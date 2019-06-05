%: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean::
	$(RM) Makefile.coq

-include Makefile.coq
