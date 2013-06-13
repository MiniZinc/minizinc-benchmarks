include ../../../Mercury.options.common

.PHONY: runtests_cd
runtests_cd:
	./test_benchmarks -m $(INSTALL_PREFIX)/bin/mzn2fzn_cd -f $(INSTALL_PREFIX)/bin/flatzinc

.PHONY: runtests_mer
runtests_mer:
	./test_benchmarks -m $(INSTALL_PREFIX)/bin/mzn2fzn -f $(INSTALL_PREFIX)/bin/flatzinc

.PHONY: distclean
distclean:
	$(RM) -f FAILED_TESTS*
	$(RM) -f FLATTEN*
	$(RM) -f EVALUATION*
	$(RM) -f CD_MZN*
	$(RM) -f CD_FZN*
	$(RM) -f CHECK*
	$(RM) -f *.results *.results0
	find . -name "zm*.m"  | xargs $(RM) -f
	find . -name "zm*.mh" | xargs $(RM) -f
	find . -name "*.out" | xargs $(RM) -f
	find . -name "*.check" | xargs $(RM) -f
	find . -name "*.fzn" | xargs $(RM) -f
	find . -name "*.err" | xargs $(RM) -f
	find . -name "*.cdo" | xargs $(RM) -f
	find . -name "*.cds" | xargs $(RM) -f
	find . -name "Cadmium" | xargs $(RM) -rf
	find . -name "Mercury" | xargs $(RM) -rf
