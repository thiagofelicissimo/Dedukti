
# PLEASE EDIT THE FOLLOWING LINES TO FIT YOUR SYSTEM CONFIGURATION

ifeq ($(INSTALL_DIR),)
INSTALL_DIR=/usr/bin
endif

# DO NOT EDIT AFTER THIS LINE

MENHIR = -menhir "menhir --external-tokens Tokens"
SRC_DIRS = kernel,utils,parser

BINARIES=dkcheck dktop dkdep dkindent

all: lib $(BINARIES) doc

dkcheck:
	ocamlbuild -Is $(SRC_DIRS),dkcheck $(MENHIR) -lib unix dkcheck.native

dktop:
	ocamlbuild -Is $(SRC_DIRS),dktop $(MENHIR) -lib unix dktop.native

dkdep:
	ocamlbuild -Is $(SRC_DIRS),dkdep $(MENHIR) -lib unix dkdep.native

dkindent:
	ocamlbuild -Is $(SRC_DIRS),dkindent $(MENHIR) -lib unix dkindent.native

doc:
	ocamlbuild -Is kernel kernel/dedukti.docdir/index.html

lib:
	ocamlbuild -Is kernel $(OPTIONS) dedukti.cmxa

install:
	for i in $(BINARIES) ; do \
	    install "_build/$$i/$$i.native" "${INSTALL_DIR}/$$i" ; \
	done

uninstall:
	for i in $(BINARIES) ; do \
	    rm -f "${INSTALL_DIR}/$$i" ; \
	done

clean:
	ocamlbuild -clean

tests:
	tests/tests.sh

upload-redirect:
	scp web/index.html scm.gforge.inria.fr:/home/groups/dedukti/htdocs/index.html

.PHONY: $(BINARIES) tests clean doc uninstall
