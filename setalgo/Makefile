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
        ../linf \

## Directory where generated HTML documentation should go.

DOCDIR = html

## List of files to be compiled and documented.

FILES = \
	ALinearF_Dmap \
	ALinearF_Definitions \
	ALinearF_Infrastructure \
	ALinearF_Denv \
	ALinearF_Lemmas \
	ALinearF_Soundness

## Lists calculated from the above.

VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation gens
.SUFFIXES: .v .vo

all:
	+make -C ../../../metatheory Metatheory.vo
	+make -C ../linf
	+make coq

coq: $(VOFILES)

doc:
	make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -g --quiet --noindex --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

############################################################################

%.vo: %.v Makefile
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
