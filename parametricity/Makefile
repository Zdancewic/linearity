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

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc
METADIR = ../../../metatheory/
LINDIR = ../linf/

## The files in the Metatheory library.

## Other files used only by folks developing the tutorial.
## These are not intended for distribution.

LINEAR = \
	LinF_Definitions \
	LinF_Infrastructure \
	Extra \
	LinF_Lemmas \
	LinF_Soundness \
	LinF_ExtraLemmas

PARAMETRICITY = \
  ExtraMetalib \
	LinF_PreLib \
	LinF_Renaming \
	LinF_Parametricity_Pre \
	LinF_Parametricity_Interface\
	LinF_Parametricity \
	LinF_Parametricity_Macro \
	LinF_Parametricity_App \
	LinF_ContextualEq_Def \
	LinF_ContextualEq_Lemmas \
	LinF_ContextualEq_Sound \
	LinF_ContextualEq_Prop \
	LinF_ContextualEq_Complete \
	LinF_OParametricity_Pre \
	LinF_OParametricity_Interface\
	LinF_OParametricity \
	LinF_OParametricity_Macro \
	LinF_OParametricity_App \
	LinF_OContextualEq_Lemmas \
	LinF_OContextualEq_Sound \
  
## Lists calculated from the above.

ALLVFILES = \
	$(foreach i, $(METATHEORY), $(METADIR)/$(i).v) \
	$(foreach i, $(LINEAR), $(LINDIR)/$(i).v) \
	$(foreach i, $(PARAMETRICITY), $(i).v)

GLOBS = \
	$(foreach i, $(METATHEORY), -glob-from $(i).glob) \
	$(foreach i, $(LINEAR), -glob-from $(i).glob) \
	$(foreach i, $(PARAMETRICITY), -glob-from $(i).glob)

VFILES = \
	$(foreach i, $(PARAMETRICITY), $(i).v)

VOFILES = \
	$(foreach i, $(METATHEORY), $(METADIR)/$(i).vo) \
	$(foreach i, $(LINEAR), $(LINDIR)/$(i).vo) \
	$(foreach i, $(PARAMETRICITY), $(i).vo)


############################################################################

.PHONY: all clean coq documentation publish quickdoc zip
.SECONDARY: $(GLOBS)
.SUFFIXES: .v .vo

all : 
	+make -C $(METADIR)$  Metatheory.vo
	+make -C $(LINDIR)$ 
	+make coq

coq : $(VOFILES)

doc:
	make documentation

documentation: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

clean :
	rm -f *.vo *.glob


############################################################################

$(DOCDIR) :
	mkdir -p $(DOCDIR)

%.vo : %.v
	$(COQC) -q -I . -I $(METADIR) -I $(LINDIR) -dump-glob $*.glob $<

############################################################################

.depend : $(ALLVFILES)
	$(COQDEP) -I . -I $(METADIR) -I $(LINDIR) $(ALLVFILES) > .depend

include .depend
