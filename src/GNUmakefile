include Makefile.common

.SECONDEXPANSION:

VS_BACKSLASH := $(TARGETS:%.vo=%.v)
VS := $(subst \,/,$(VS_BACKSLASH))

PWD := $(shell pwd)
COMMA := ,

COQLIBS := -R . $(LIBNAME)

OTHERFLAGS ?= -dont-load-proofs

V = 0

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

SILENCE_COQMAKEFILE_0 = @echo "COQMAKEFILE $<"; #
SILENCE_COQMAKEFILE_1 =
SILENCE_COQMAKEFILE = $(SILENCE_COQMAKEFILE_$(V))

COQDOCFLAGS=-interpolate -utf8

TIMED=
TIMECMD=
# we should use %U for compatibility with Coq trunk, but that's broken on Windows cygwin with a non-cygwin-compilied program, it seems.  %M is also broken, but whatever
ifneq ("$(wildcard /usr/bin/time)","")
STDTIME=/usr/bin/time -f \"\$$* (user: %e mem: %M ko)\"
else
STDTIME=
endif
TIMER=\$$(if \$$(TIMED), $(STDTIME), $(TIMECMD))

.PHONY: default all

%.dll %.exe: %.v
	./buildexe.sh $< $@ $(COQLIBS)

default: all .dir-locals.el

Makefile.coq: GNUmakefile Makefile.common
	@(which time >/dev/null 2>&1) || echo "WARNING: Timing will be unavailable; please install /usr/bin/time."
	$(SILENCE_COQMAKEFILE)coq_makefile COQC = "\$$(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP) \"\$$(COQBIN)coqdep\" -c" $(COQLIBS) $(VS) -o Makefile.coq

.dir-locals.el: .dir-locals.el.in
	$(VECHO) "SED $< > $@"
	$(Q)sed s'/@LIBNAME@/$(LIBNAME)/g' "$<" > "$@"

include Makefile.coq
