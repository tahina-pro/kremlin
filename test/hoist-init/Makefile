include ../../Makefile.common

FSTAR_EXE ?= fstar.exe

TEST_OPTS	= -warn-error @4 -skip-makefiles
KRML_BIN	= ../../_build/default/src/Karamel.exe
KRML		= $(KRML_BIN) -fstar $(FSTAR_EXE) $(KOPTS) $(TEST_OPTS)

CACHE_DIR	= .cache
OUTPUT_DIR	= .output

FSTAR		= $(FSTAR_EXE) \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include ../../krmllib/compat --include ../../krmllib/obj \
  --include ../../krmllib --include ../../runtime \
  --already_cached 'Prims FStar C TestLib LowStar' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi --warn_error -274

FILES		= $(patsubst %.fst,%.test,$(wildcard *.fst))

CUSTOM		= check-hoist-ifdef \
  check-init-hoist check-init-hoist-c99 check-init-hoist-c89 \
  check-merge-decl-init

all: $(FILES) $(CUSTOM)

.PRECIOUS: %.krml

comma := ,

ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	$(call run-with-log, \
	  $(FSTAR) --dep full $(subst .test,.fst,$(FILES)) \
	    --extract 'krml:*$(comma)-Prims' -o $@ \
	  ,[DEPEND],\
	  .depend)

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(call run-with-log,$(FSTAR) $(OTHERFLAGS) -c $< -o $@ && touch $@,[VERIFY] $*,$(CACHE_DIR)/$*)

$(OUTPUT_DIR)/%.krml: | .depend
	$(call run-with-log, \
	  $(FSTAR) $(OTHERFLAGS) --codegen krml \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    -o $@ \
	    $< \
	 ,[EXTRACT] $*,\
	  $(OUTPUT_DIR)/$*)

#################
# Build targets #
#################

$(OUTPUT_DIR)/HoistLocals.exe: EXTRA = -fhoist-locals -fno-shadow
$(OUTPUT_DIR)/HoistLocalsInline.exe: EXTRA = -fhoist-locals -fno-shadow
$(OUTPUT_DIR)/HoistIfDef.exe: EXTRA = -fhoist-locals -fno-shadow -ccopt -DUSE_FEATURE
$(OUTPUT_DIR)/InitLocals.exe: EXTRA = -finitialize-locals c23
$(OUTPUT_DIR)/MergeDeclInit.exe: EXTRA = -fhoist-locals -fno-shadow

.PRECIOUS: $(OUTPUT_DIR)/%.exe
$(OUTPUT_DIR)/%.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(call run-with-log, \
	  $(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=WindowsHack$(comma)\* \
	,[KRML] $*,$(OUTPUT_DIR)/$*)

.SECONDEXPANSION:
%.test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).exe
	@($^) && echo -e "\033[01;32m✔\033[00m [TEST,$*]" || (echo -e "\033[01;31m✘\033[00m [TEST,$*]" && false)

##################
# Custom targets #
##################

check-hoist-ifdef: $(OUTPUT_DIR)/HoistIfDef.exe
	[ `grep -c 'KRML_MAYBE_UNUSED_VAR(a)' $(OUTPUT_DIR)/HoistIfDef.out/HoistIfDef.c` = 1 ]
	[ `grep -c 'KRML_MAYBE_UNUSED_VAR(b)' $(OUTPUT_DIR)/HoistIfDef.out/HoistIfDef.c` = 1 ]
	! grep -q 'KRML_MAYBE_UNUSED_VAR(c)' $(OUTPUT_DIR)/HoistIfDef.out/HoistIfDef.c
	cc -Wunused-variable -Werror -std=c11 -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE \
	  -I ../../include -I ../../krmllib/dist/minimal -I $(OUTPUT_DIR)/HoistIfDef.out \
	  -c $(OUTPUT_DIR)/HoistIfDef.out/HoistIfDef.c -o /dev/null

# -finitialize-locals + -fhoist-locals with C23 mode
.PRECIOUS: $(OUTPUT_DIR)/InitLocals_hoist.exe
$(OUTPUT_DIR)/InitLocals_hoist.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c23 -fhoist-locals -fno-shadow -tmpdir $(subst .exe,.out,$@) -no-prefix InitLocals \
	    -o $@ $(filter %.krml,$^) -bundle InitLocals=WindowsHack$(comma)\* \
	,[KRML] InitLocals_hoist,$(OUTPUT_DIR)/InitLocals_hoist)

check-init-hoist: $(OUTPUT_DIR)/InitLocals_hoist.exe
	grep -q '= {  }' $(OUTPUT_DIR)/InitLocals_hoist.out/InitLocals.c
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST,check-init-hoist]") || (echo -e "\033[01;31m✘\033[00m [TEST,check-init-hoist]" && false)

# -finitialize-locals c99 + -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/InitLocals_hoist_c99.exe
$(OUTPUT_DIR)/InitLocals_hoist_c99.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c99 -fhoist-locals -fno-shadow -ccopt -std=c99 -ccopt -Werror \
	    -tmpdir $(subst .exe,.out,$@) -no-prefix InitLocals \
	    -o $@ $(filter %.krml,$^) -bundle InitLocals=WindowsHack$(comma)\* \
	,[KRML] InitLocals_hoist_c99,$(OUTPUT_DIR)/InitLocals_hoist_c99)

check-init-hoist-c99: $(OUTPUT_DIR)/InitLocals_hoist_c99.exe
	grep -q '\.fst = 3U' $(OUTPUT_DIR)/InitLocals_hoist_c99.out/InitLocals.c
	grep -q '= 0U' $(OUTPUT_DIR)/InitLocals_hoist_c99.out/InitLocals.c
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST,check-init-hoist-c99]") || (echo -e "\033[01;31m✘\033[00m [TEST,check-init-hoist-c99]" && false)

# -finitialize-locals c89 + -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/InitLocals_hoist_c89.exe
$(OUTPUT_DIR)/InitLocals_hoist_c89.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c89 -fhoist-locals -fno-shadow -fc89 \
	    -tmpdir $(subst .exe,.out,$@) -no-prefix InitLocals \
	    -o $@ $(filter %.krml,$^) -bundle InitLocals=WindowsHack$(comma)\* \
	,[KRML] InitLocals_hoist_c89,$(OUTPUT_DIR)/InitLocals_hoist_c89)

check-init-hoist-c89: $(OUTPUT_DIR)/InitLocals_hoist_c89.exe
	! grep -q '\.fst = 0' $(OUTPUT_DIR)/InitLocals_hoist_c89.out/InitLocals.c
	grep -q '{ 0U, 0U }' $(OUTPUT_DIR)/InitLocals_hoist_c89.out/InitLocals.c
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST,check-init-hoist-c89]") || (echo -e "\033[01;31m✘\033[00m [TEST,check-init-hoist-c89]" && false)

# MergeDeclInit: verify that declarations are merged back with initializers
check-merge-decl-init: $(OUTPUT_DIR)/MergeDeclInit.exe
	# test_all_merge: all declarations have initializers
	grep -q 'uint32_t a = 1U' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t b = a + a' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t c = b + a' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_chain: chain of 4 declarations all merged
	grep -q 'uint32_t w = 1U' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t x = w + w' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t y = x + w' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t z = y + x' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_partial: x and y merged, r0 and r not merged (assigned inside branches)
	grep -q 'uint32_t r0;' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t r;' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t x = 1U' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t y = x + x' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_comment_between: comment preserved, declarations merged
	grep -q 'standalone comment between a and b' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t b = a + a' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_multi_comment: all three comments preserved, declarations merged
	grep -q 'comment at start' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'comment after a' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'comment after b' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_unused_param: KRML_MAYBE_UNUSED_VAR preserved, declarations merged
	grep -q 'KRML_MAYBE_UNUSED_VAR(unused)' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	grep -q 'uint32_t a = arg + 1U' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	# test_two_unused: both KRML_MAYBE_UNUSED_VAR preserved, declarations merged
	[ `grep -c 'KRML_MAYBE_UNUSED_VAR' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c` -ge 4 ]
	# test_unused_and_comment: mixed skippables preserved, declarations merged
	grep -q 'comment after ignore' $(OUTPUT_DIR)/MergeDeclInit.out/MergeDeclInit.c
	@echo -e "\033[01;32m✔\033[00m [TEST,check-merge-decl-init]"

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) .depend
