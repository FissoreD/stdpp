# Default target
all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all
.PHONY: all

# Permit local customization
-include Makefile.local

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.coq $@
phony: ;
.PHONY: phony

clean: Makefile.coq
	+@$(MAKE) -f Makefile.coq clean
	@# Make sure not to enter the `_opam` folder.
	cd stdpp && find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache builddep/*
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq $(EXTRA_COQFILES)


##############################################################################
# BENCH
all_bench: Makefile.coq_bench
	+@$(MAKE) -f Makefile.coq_bench all
.PHONY: all_bench

# Permit local customization
-include Makefile.local

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq_bench phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.coq_bench $@

clean_bench: Makefile.coq_bench
	+@$(MAKE) -f Makefile.coq_bench clean
	@# Make sure not to enter the `_opam` folder.
	cd stdpp_bench && find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq_bench .lia.cache builddep/*
.PHONY: clean

# Create Coq Makefile.
Makefile.coq_bench: _CoqProject_bench Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject_bench -o Makefile.coq_bench $(EXTRA_COQFILES)

# END BENCH
##############################################################################

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep

# Backwards compatibility target
build-dep: builddep
.PHONY: build-dep

# Some files that do *not* need to be forwarded to Makefile.coq.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local _CoqProject $(OPAMFILES):: ;
