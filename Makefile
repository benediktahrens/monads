#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.3pl5     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

# 
# This Makefile may take 3 arguments passed as environment variables:
#   - COQBIN to specify the directory where Coq binaries resides;
#   - CAMLBIN and CAMLP4BIN to give the path for the OCaml and Camlp4/5 binaries.
COQLIB:=$(shell $(COQBIN)coqtop -where | sed -e 's/\\/\\\\/g')
CAMLP4:="$(shell $(COQBIN)coqtop -config | awk -F = '/CAMLP4=/{print $$2}')"
ifndef CAMLP4BIN
  CAMLP4BIN:=$(CAMLBIN)
endif

CAMLP4LIB:=$(shell $(CAMLP4BIN)$(CAMLP4) -where)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

OCAMLLIBS:=
COQSRCLIBS:=-I $(COQLIB)/kernel -I $(COQLIB)/lib \
  -I $(COQLIB)/library -I $(COQLIB)/parsing \
  -I $(COQLIB)/pretyping -I $(COQLIB)/interp \
  -I $(COQLIB)/proofs -I $(COQLIB)/tactics \
  -I $(COQLIB)/toplevel \
  -I $(COQLIB)/plugins/cc \
  -I $(COQLIB)/plugins/dp \
  -I $(COQLIB)/plugins/extraction \
  -I $(COQLIB)/plugins/field \
  -I $(COQLIB)/plugins/firstorder \
  -I $(COQLIB)/plugins/fourier \
  -I $(COQLIB)/plugins/funind \
  -I $(COQLIB)/plugins/groebner \
  -I $(COQLIB)/plugins/interface \
  -I $(COQLIB)/plugins/micromega \
  -I $(COQLIB)/plugins/nsatz \
  -I $(COQLIB)/plugins/omega \
  -I $(COQLIB)/plugins/quote \
  -I $(COQLIB)/plugins/ring \
  -I $(COQLIB)/plugins/romega \
  -I $(COQLIB)/plugins/rtauto \
  -I $(COQLIB)/plugins/setoid_ring \
  -I $(COQLIB)/plugins/subtac \
  -I $(COQLIB)/plugins/subtac/test \
  -I $(COQLIB)/plugins/syntax \
  -I $(COQLIB)/plugins/xml
COQLIBS:= -R . CatSem
COQDOCLIBS:=-R . CatSem

##########################
#                        #
# Variables definitions. #
#                        #
##########################

ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)
OPT:=
COQFLAGS:=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
ifdef CAMLBIN
  COQMKTOPFLAGS:=-camlbin $(CAMLBIN) -camlp4bin $(CAMLP4BIN)
endif
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
COQMKTOP:=$(COQBIN)coqmktop
CAMLLIB:=$(shell $(CAMLBIN)ocamlc.opt -where)
CAMLC:=$(CAMLBIN)ocamlc.opt -c -rectypes
CAMLOPTC:=$(CAMLBIN)ocamlopt.opt -c -rectypes
CAMLLINK:=$(CAMLBIN)ocamlc.opt -rectypes
CAMLOPTLINK:=$(CAMLBIN)ocamlopt.opt -rectypes
GRAMMARS:=grammar.cma
CAMLP4EXTEND:=pa_extend.cmo pa_macro.cmo q_MLast.cmo
CAMLP4OPTIONS:=
PP:=-pp "$(CAMLP4BIN)$(CAMLP4)o -I $(CAMLLIB) -I . $(COQSRCLIBS) $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl"

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES:=AXIOMS/functional_extensionality.v\
  CAT/SO.v\
  CAT/het_rewrite.v\
  CAT/cat_TYPE_option.v\
  CAT/limits.v\
  CAT/IO.v\
  CAT/functor_leibniz_eq.v\
  CAT/small_cat.v\
  CAT/ind_potype.v\
  CAT/mon_cats.v\
  CAT/CatFunct.v\
  CAT/nat_iso.v\
  CAT/monad_h_morphism_gen.v\
  CAT/eq_fibre.v\
  CAT/cat_INDEXED_TYPE.v\
  CAT/monad_morphism.v\
  CAT/my_lib.v\
  CAT/orders_bis.v\
  CAT/initial_terminal.v\
  CAT/enriched_cat.v\
  CAT/cat_TYPE.v\
  CAT/order_classes.v\
  CAT/Misc.v\
  CAT/prods.v\
  CAT/smon_cats.v\
  CAT/coproduct.v\
  CAT/horcomp.v\
  CAT/unit_type_rmonad.v\
  CAT/unit_type_monad.v\
  CAT/retype_functor_po.v\
  CAT/preorder_top.v\
  CAT/rmodule_TYPE.v\
  CAT/category_hom_transport.v\
  CAT/free_cats.v\
  CAT/orders.v\
  CAT/orders_lemmas.v\
  CAT/subcategories.v\
  CAT/rmonad_gen_type_po.v\
  CAT/rmonad_gen.v\
  CAT/rmonad_gen_comp.v\
  CAT/monad_def.v\
  CAT/cat_DISCRETE.v\
  CAT/functor.v\
  CAT/rmonad.v\
  CAT/monic_epi.v\
  CAT/monad_h_module.v\
  CAT/bifunctor.v\
  CAT/NT.v\
  CAT/retype_functor.v\
  CAT/type_unit.v\
  CAT/monad_h_morphism.v\
  CAT/monad_monad_h.v\
  CAT/product.v\
  CAT/category.v\
  CAT/functor_properties.v\
  CAT/pts.v\
  CAT/monad_haskell.v\
  CAT/cat_SET.v\
  CAT/rmonad_hom.v\
  CAT/rmodule_pb_rmonad_hom.v\
  CAT/ipo_modules.v\
  CAT/het_rewrite.v\
  CAT/module_postcomp_functor.v\
  CAT/unit_mod.v\
  CAT/cat_gen_monad.v\
  CAT/equiv_Monad_MonaD.v\
  STS/STS_arities.v\
  STS/STS_representations.v\
  STS/STS_initial.v\
  TLC/TLC_types.v\
  TLC/TLC_syntax.v\
  TLC/TLC_semantics.v\
  TLC/TLC_RMonad.v\
  TLC/TLC_Monad.v\
  ULC/ULC_syntax.v\
  ULC/ULC_semantics.v\
  ULC/ULC_RMonad.v\
  ULC/ULC_Monad.v\
  ULC/ULC_terms.v\
  PCF/PCF_types.v\
  PCF/PCF_syntax.v\
  PCF/PCF_semantics.v\
  PCF/PCF_RMonad.v\
  PCF/PCF_Monad.v\
  RPCF/RPCF_rep.v\
  RPCF/RPCF_rep_hom.v\
  RPCF/RPCF_rep_eq.v\
  RPCF/RPCF_rep_id.v\
  RPCF/RPCF_rep_comp.v\
  RPCF/RPCF_rep_cat.v\
  RPCF/RPCF_syntax_rep.v\
  RPCF/RPCF_syntax_init.v\
  RPCF/RPCF_INIT.v\
  RPCF/RPCF_ULC_nounit.v\
  PROP_untyped/arities.v\
  PROP_untyped/representations.v\
  PROP_untyped/initial.v\
  PROP_untyped/prop_arities_initial.v\
  PROP_untyped/prop_arities_initial_variant.v\
  PROP_untyped/ex_ulcbeta.v
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)

all: $(VOFILES) 
spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all.pdf: $(VFILES)
	$(COQDOC) -toc -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

install:
	mkdir -p $(COQLIB)/user-contrib
	(for i in $(VOFILES); do \
	 install -d `dirname $(COQLIB)/user-contrib/CatSem/$$i`; \
	 install $$i $(COQLIB)/user-contrib/CatSem/$$i; \
	 done)

clean:
	rm -f $(CMOFILES) $(CMIFILES) $(CMXFILES) $(CMXSFILES) $(OFILES) $(VOFILES) $(VIFILES) $(GFILES) $(MLFILES:.ml=.cmo) $(MLFILES:.ml=.cmx) *~
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(HTMLFILES) $(GHTMLFILES) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) $(VFILES:.v=.v.d)
	- rm -rf html

archclean:
	rm -f *.cmx *.o


printenv: 
	@echo CAMLC =	$(CAMLC)
	@echo CAMLOPTC =	$(CAMLOPTC)
	@echo CAMLP4LIB =	$(CAMLP4LIB)

Makefile: Make
	mv -f Makefile Makefile.bak
	$(COQBIN)coq_makefile -f Make -o Makefile


-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

