############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

## Include directories, one per line.

INCDIRS = \
	. \
	../../../metatheory \

## Directory where generated HTML documentation should go.

DOCDIR = html

## List of files to be compiled and documented.

FILES = \
	Bang_Definitions \
	Bang_Infrastructure \
	Extra \
	Bang_Lemmas \
	Bang_Soundness \
	Bang_ExtraLemmas \
  	ExtraMetalib \
	Bang_PreLib \
	Bang_Renaming \
	Bang_Parametricity_Pre \
	Bang_Parametricity_Interface\
	Bang_Parametricity \
	Bang_Parametricity_Macro \
	Bang_Parametricity_App \
	Bang_OParametricity_Pre \
	Bang_OParametricity_Interface\
	Bang_OParametricity \
	Bang_OParametricity_Macro \
	Bang_OParametricity_App \
	Bang_OParametricity_App2 \
	Bang_ContextualEq_Def \
	Bang_ContextualEq_Infrastructure \
	Bang_ContextualEq_Lemmas \
	Bang_ContextualEq_Sound \
	Bang_ContextualEq_Prop \
	Bang_ContextualEq_Complete \
	Bang_OContextualEq_Lemmas \
	Bang_OContextualEq_Sound \
	Bang_OContextualEq_Complete

## Lists calculated from the above.

VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation gens
.SUFFIXES: .v .vo

all:
	+make -C ../../../metatheory Metatheory.vo
	+make coq

coq: $(VOFILES)

doc:
	make documentation

documentation: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

ottdoc:	bang-top.pdf

bang-top.tex: bang.ott bang.mng
	ott -tex bang.tex \
                    -tex_wrap false \
                    -tex_show_meta false \
                    -tex_filter bang.mng bang-top.tex \
                    bang.ott

%-top.pdf : %-top.tex
	pdflatex $<

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

ottclean:
	rm bang.tex bang-top.tex *.log *~ *.aux bang-top.pdf 

############################################################################

%.vo: %.v
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES)
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend



