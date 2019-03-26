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

DOCDIR = doc/coqdoc

## Paths to executables. Do not include options here.

COQC = /usr/local/bin/coqc
COQDEP = /usr/local/bin/coqdep
COQDOC = /usr/local/bin/coqdoc

## The files in the Metatheory library.

METATHEORY = \
	AdditionalTactics \
	Atom \
	Environment \
	FiniteSets \
	FSetDecide \
	FSetNotin \
	ListFacts \
	Metatheory \

## Tutorial files that should compile.

LINEAR = \
	LinearF_Definitions \
	LinearF_Infrastructure \
	LinearF_Lemmas \
	LinearF_Soundness \

ALLVFILES = \
	$(foreach i, $(METATHEORY), $(i).v) \
	$(foreach i, $(LINEAR), $(i).v) \

GLOBS = \
	$(foreach i, $(METATHEORY), -glob-from $(i).glob) \
	$(foreach i, $(LINEAR), -glob-from $(i).glob) \

VOGLOBS = \
	$(foreach i, $(METATHEORY), $(i).vo) \
	$(foreach i, $(TUTORIAL), $(i).vo) \

VOFILES = \
	$(foreach i, $(METATHEORY), $(i).vo) \
	$(foreach i, $(LINEAR), $(i).vo) \


############################################################################

.PHONY: all clean coq documentation 
.SECONDARY: $(GLOBS)
.SUFFIXES: .v .vo

all : coq

coq : $(VOFILES)

documentation : $(VOGLOBS) $(DOCDIR)
	$(COQDOC) --quiet --utf8 --html -d $(DOCDIR) $(GLOBS) $(ZIPVFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

quickdoc: $(ZIPVFILES) $(DOCDIR)
	$(COQDOC) -g --quiet --utf8 --html -d $(DOCDIR) $(ZIPVFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean :
	rm -f *.vo *.glob
	rm -rf $(DOCDIR)


############################################################################

$(DOCDIR) :
	mkdir -p $(DOCDIR)

%.vo : %.v
	$(COQC) -q -I . -dump-glob $*.glob $<

%.v : Master_%.v cpp.py
	./cpp.py core $< > $@

############################################################################

.depend : $(ALLVFILES)
	$(COQDEP) -I . $(ALLVFILES) > .depend

include .depend
