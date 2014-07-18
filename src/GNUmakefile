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

SILENCE_COQMAKEFILE_0 = @echo "COQMAKEFILE"; #
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

.PHONY: all check-Makefile.common

%.dll %.exe %.bin: %.v
	./buildexe.sh $< $@ $(COQLIBS)

all: .dir-locals.el check-Makefile.common

Makefile.coq: GNUmakefile Makefile.common
	@(which time >/dev/null 2>&1) || echo "WARNING: Timing will be unavailable; please install /usr/bin/time."
	$(SILENCE_COQMAKEFILE)coq_makefile COQC = "\$$(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP) \"\$$(COQBIN)coqdep\" -c" $(COQLIBS) $(VS) -o Makefile.coq

.dir-locals.el: .dir-locals.el.in
	$(VECHO) "SED $< > $@"
	$(Q)sed s'/@LIBNAME@/$(LIBNAME)/g' "$<" > "$@"

# Find any suspicious comments in Makefile.common
# TODO(t-jagro): Find a better way to do color than 'grep --color=auto '\*''
check-Makefile.common:
	$(VECHO) "CHECK Makefile.common"
	$(Q)FILES="$$(grep -A 1 '^\s*#.*\\[\s#]\?.*$$' Makefile.common | grep -v -- '^--$$' | grep -v '^\s*$$' | grep -B 1 '^\s*[^#].*')"; \
	if [ ! -z "$$FILES" ]; then \
	  echo '***************************************************************************' | grep --color=auto '\*'; \
	  echo '***************************************************************************' | grep --color=auto '\*'; \
	  echo '** ERROR: GNU Make treats line-continuation characters (\) in comments   **' | grep --color=auto '\*\|ERROR:'; \
	  echo '**        as comment continuations.  You have the following suspicious   **' | grep --color=auto '\*'; \
	  echo '**        lines involving comment continuations:                         **' | grep --color=auto '\*'; \
	  echo ''; \
	  grep -A 1 '^\s*#.*\\[\s#]\?.*$$' Makefile.common | grep -v -- '^--$$' | grep -v '^\s*$$' | grep --color=auto -B 1 '^\s*[^#].*'; \
	  echo ''; \
	  echo '** Please comment out the lines after comment continuations to continue. **' | grep --color=auto '\*'; \
	  echo '** If these lines should not be commented out, move the comments to the  **' | grep --color=auto '\*'; \
	  echo '** End of whatever variable declaration list you have them in.           **' | grep --color=auto '\*'; \
	  echo '***************************************************************************' | grep --color=auto '\*'; \
	  echo '***************************************************************************' | grep --color=auto '\*'; \
	  exit 1; \
	fi

include Makefile.coq
