############################################################################
#
#  Primary targets:
#    all           - builds .vo files
#    coq           - synonym for 'all'
#    clean         - removes all generated files
#    documentation - builds HTML documentation
#    quickdoc      - builds HTML documentation w/o cross references
#    zip           - builds zip file for distribution
#    publish       - rsync's documentation to PL Club website
#                    (requires access to plclub@eniac account)
#
############################################################################

ZIPDIR = coq-tutorial
DOCDIR = doc/coqdoc

## Paths to executables. Do not include options here.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc
INCDIR = ../declarative/

## The files in the Metatheory library.

METATHEORY = \
	AdditionalTactics \
	ListFacts \
	FiniteSets \
	FSetDecide \
	FSetNotin \
	Atom \
	Environment \
	Metatheory \

## Other files used only by folks developing the tutorial.
## These are not intended for distribution.

DECL_FILES = \
	LinearF_Definitions \
	LinearF_Infrastructure \
	LinearF_Lemmas
#	LinearF_Soundness

ALGO_FILES = \
        ALinearF_Definitions \
	      ALinearF_Infrastructure \
        ALinearF_Lemmas \
        ALinearF_Soundness \
        ALinearF_NLemmas \
        ALinearF_NSoundness

## Lists calculated from the above.

ALLVFILES = \
	$(foreach i, $(METATHEORY), $(INCDIR)/$(i).v) \
	$(foreach i, $(DECL_FILES), $(INCDIR)/$(i).v) \
	$(foreach i, $(ALGO_FILES), $(i).v)

GLOBS = \
	$(foreach i, $(METATHEORY), -glob-from $(i).glob) \
	$(foreach i, $(DECL_FILES), -glob-from $(i).glob) \
	$(foreach i, $(ALGO_FILES), -glob-from $(i).glob)

VOFILES = \
	$(foreach i, $(METATHEORY), $(INCDIR)/$(i).vo) \
	$(foreach i, $(DECL_FILES), $(INCDIR)/$(i).vo) \
	$(foreach i, $(ALGO_FILES), $(i).vo)


############################################################################

.PHONY: all clean coq documentation publish quickdoc zip
.SECONDARY: $(GLOBS)
.SUFFIXES: .v .vo

all : coq

coq : $(VOFILES)

clean :
	rm -f *.vo *.glob
	rm -f $(INCDIR)/*.vo $(INCDIR)/*.glob


############################################################################

$(DOCDIR) :
	mkdir -p $(DOCDIR)

%.vo : %.v
	$(COQC) -q -I . -I $(INCDIR) -dump-glob $*.glob $<

############################################################################

.depend : $(ALLVFILES)
	$(COQDEP) -I . -I $(INCDIR) $(ALLVFILES) > .depend

include .depend
