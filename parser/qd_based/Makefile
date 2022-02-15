DONTVERIFY?=t
DONTEXTRACT?=t
DONTPRINTSKIP?=t
include ../../scripts/Makefile.ver

BOLD:="\033[1m"
RESET:="\033[0m"
RED:="\033[31m"
GREEN:="\033[32m"
RUNNING:=$(BOLD)"[+]"$(RESET)
DONE:=$(GREEN)$(BOLD)"[+]"$(RESET)

AWK:=$(shell command -v gawk 2>/dev/null)
AWK:=$(if $(AWK),$(AWK),awk)
SED:=$(shell command -v gsed 2>/dev/null)
SED:=$(if $(SED),$(SED),sed)

QD_TARGET:=Wasm.Parse.Module_.fst

all: fstgen

fstgen: .gen $(QD_TARGET)

$(VERs) $(VERIs): .gen

.gen: wasm.rfc
	@echo $(RUNNING) "Compiling $<"
	@qd -high -prefix Wasm.Parse. wasm.rfc >/dev/null
	@touch $@
	@for i in *.fst; do $(SED) -i 's/^      ()$$//' $$i; done # Workaround for qd issue
	@echo $(DONE) "Done!"

%.rfc: %.prerfc
	@echo $(RUNNING) "Pre-processing $< to $@"
	@$(AWK) '/XXX|WARN|TODO/{print "\t'$(RED)Warning$(RESET)' Line " NR ": \t" $$0}' $<
	@$(AWK) 'BEGIN{RS="";FS="\n" }/#define/{gsub(/\\/, "NEWLINE \\");}{print $$0 "\n"}' $< | \
		cpp -C | \
		$(SED) 's/NEWLINE/\n/g' | \
		$(SED) 's/[ \t]*$$//' | \
		$(SED) -n '/INIT WASM/,$$p' | \
		egrep -v 'INIT|#' | \
		cat -s > $@
	@echo $(DONE) "Done!"
# Works by changing all #defines to have "NEWLINE"s across
#   their definitions, after which it runs the C
#   pre-processor. Following this, it changes the "NEWLINE"s
#   back to actual newlines, and strips out following
#   whitespace. Then, it strips away the random comments that
#   show up due to the pre-processor, and finally squeezes
#   multiple empty lines into a single empty line, for nicer
#   looking output.

clean-more:
	@echo $(RUNNING) "Cleaning up"
	@rm -f *~ *.fst *.fsti *.rfc .depend *.checked *.hints *.ml .gen
	@echo $(DONE) "Done!"
