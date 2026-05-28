include ../../Makefile.common

# Standalone test suite for -fhoist-locals (HoistLocals pass).
# For each test, we compile with and without -fhoist-locals, run both,
# and compare their stdout to ensure identical output.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

FSTAR_EXE ?= fstar.exe
KRML_BIN = ../../_build/default/src/Karamel.exe
TEST_OPTS = -warn-error @4 -skip-makefiles

CACHE_DIR = .cache
OUTPUT_DIR = .output

FSTAR = $(FSTAR_EXE) \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include ../../krmllib/compat --include ../../krmllib/obj \
  --include ../../krmllib --include ../../runtime \
  --already_cached 'Prims FStar C TestLib LowStar WasmSupport' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi --warn_error -274

KRML = $(KRML_BIN) -fstar $(FSTAR_EXE) $(TEST_OPTS)

comma := ,

# Tests where output must be identical with and without -fhoist-locals
TESTS = HoistInt HoistArray HoistScope HoistVlaNoWarn HoistComment HoistMalloc

# Tests that exercise the VLA warning (compiled with -warn-error -29)
WARN_TESTS = HoistVlaWarn

# Tests that verify comment/declaration ordering in the generated C source
ORDER_TESTS = HoistComment

# Tests that verify the Option B decl/init split for non-Stack EBufCreate
# (uninitialised pointer decl hoisted, allocation call left at original site)
MALLOC_TESTS = HoistMalloc

ALL_TESTS = $(TESTS) $(WARN_TESTS)

all: $(addsuffix .compare,$(TESTS)) $(addsuffix .warn-test,$(WARN_TESTS)) \
     $(addsuffix .order-test,$(ORDER_TESTS)) \
     $(addsuffix .malloc-test,$(MALLOC_TESTS))

.PRECIOUS: %.krml $(OUTPUT_DIR)/%.krml

# Dependency analysis
ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	@mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(FSTAR) --dep full $(addsuffix .fst,$(ALL_TESTS)) \
	    --extract 'krml:*' -o $@ \
	  ,[DEPEND],\
	  .depend)

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

$(CACHE_DIR)/%.checked: | .depend
	@mkdir -p $(CACHE_DIR)
	$(call run-with-log,$(FSTAR) $(OTHERFLAGS) -c $< -o $@ && touch $@,[VERIFY] $*,$(CACHE_DIR)/$*)

$(OUTPUT_DIR)/%.krml: | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(FSTAR) $(OTHERFLAGS) --codegen krml \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    -o $@ \
	    $< \
	 ,[EXTRACT] $*,\
	  $(OUTPUT_DIR)/$*)

# Build WITHOUT -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/%.nohoist.exe
$(OUTPUT_DIR)/%.nohoist.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-nohoist] $*,$(OUTPUT_DIR)/$*.nohoist)

# Build WITH -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/%.hoist.exe
$(OUTPUT_DIR)/%.hoist.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) $(EXTRA) -fhoist-locals -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-hoist] $*,$(OUTPUT_DIR)/$*.hoist)

# Run both versions and compare output
.SECONDEXPANSION:
%.compare: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Running $* without -fhoist-locals..."
	@$(word 1,$^) > $(OUTPUT_DIR)/$*.nohoist.stdout 2>&1
	@echo "Running $* with -fhoist-locals..."
	@$(word 2,$^) > $(OUTPUT_DIR)/$*.hoist.stdout 2>&1
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [COMPARE,$*] outputs identical"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [COMPARE,$*] outputs differ:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout; \
	  false; \
	fi

# VLA warning tests: compile with -warn-error -29 to make the warning non-fatal,
# then run and compare
$(OUTPUT_DIR)/HoistVlaWarn.nohoist.exe: EXTRA = -warn-error -6
$(OUTPUT_DIR)/HoistVlaWarn.hoist.exe: EXTRA = -warn-error -6-29

%.warn-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Running $* without -fhoist-locals..."
	@$(word 1,$^) > $(OUTPUT_DIR)/$*.nohoist.stdout 2>&1
	@echo "Running $* with -fhoist-locals..."
	@$(word 2,$^) > $(OUTPUT_DIR)/$*.hoist.stdout 2>&1
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [WARN-TEST,$*] outputs identical"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [WARN-TEST,$*] outputs differ:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout; \
	  false; \
	fi

# VLA no-warn tests: verify that -fhoist-locals does NOT produce warning 29
$(OUTPUT_DIR)/HoistVlaNoWarn.nohoist.exe: EXTRA = -warn-error -6
$(OUTPUT_DIR)/HoistVlaNoWarn.hoist.exe: EXTRA = -warn-error -6

# Order test: verify that comments and initialisers/assignments appear in the
# same relative order with and without -fhoist-locals.  We normalise the
# generated C by stripping the type prefix from declarations (so that
# "int32_t x = 1;" and "x = 1;" both become "x = 1;") and compare.
%.order-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Checking comment/init order for $*..."
	@grep -E 'MARKER|int32_t [a-z_][a-z0-9_]* = |^ +[a-z_][a-z0-9_]* = ' \
	  $(subst .exe,.out,$(word 1,$^))/$*.c \
	  | sed 's/int32_t //; s/^ *//' > $(OUTPUT_DIR)/$*.nohoist.order
	@grep -E 'MARKER|int32_t [a-z_][a-z0-9_]* = |^ +[a-z_][a-z0-9_]* = ' \
	  $(subst .exe,.out,$(word 2,$^))/$*.c \
	  | sed 's/int32_t //; s/^ *//' > $(OUTPUT_DIR)/$*.hoist.order
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.order $(OUTPUT_DIR)/$*.hoist.order > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [ORDER,$*] comment/init order preserved"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [ORDER,$*] comment/init order differs:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.order $(OUTPUT_DIR)/$*.hoist.order; \
	  false; \
	fi

# Malloc test: verify the Option B decl/init split for non-Stack EBufCreate.
# Under -fhoist-locals, pointer declarations are hoisted as `T *buf = NULL;`
# and the allocation call (KRML_HOST_CALLOC/MALLOC) is left at the original
# site as `buf = KRML_HOST_CALLOC(...);`. Without -fhoist-locals, the same
# declarations remain in their combined `T *buf = KRML_HOST_CALLOC(...);`
# form.  We check:
#   - The -fhoist-locals C contains at least one `*name = NULL;` line.
#   - The -fhoist-locals C contains at least one `name = KRML_HOST_CALLOC`
#     line where the `*` (declaration marker) is absent (i.e., a pure
#     assignment, separated from the declaration).
#   - The no-flag C contains zero `*name = NULL;` lines produced by the
#     hoist pass.
%.malloc-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Checking Option B split for $*..."
	@n_null_nohoist=$$(grep -cE '\*[a-zA-Z_][a-zA-Z0-9_]* = NULL;' \
	  $(subst .exe,.out,$(word 1,$^))/$*.c || true); \
	 n_null_hoist=$$(grep -cE '\*[a-zA-Z_][a-zA-Z0-9_]* = NULL;' \
	  $(subst .exe,.out,$(word 2,$^))/$*.c || true); \
	 n_assign_hoist=$$(grep -cE '^[[:space:]]*[a-zA-Z_][a-zA-Z0-9_]* = KRML_HOST_(CALLOC|MALLOC)' \
	  $(subst .exe,.out,$(word 2,$^))/$*.c || true); \
	 n_assign_nohoist=$$(grep -cE '^[[:space:]]*[a-zA-Z_][a-zA-Z0-9_]* = KRML_HOST_(CALLOC|MALLOC)' \
	  $(subst .exe,.out,$(word 1,$^))/$*.c || true); \
	 if [ "$$n_null_nohoist" -eq 0 ] && \
	    [ "$$n_null_hoist" -gt 0 ] && \
	    [ "$$n_assign_hoist" -gt 0 ] && \
	    [ "$$n_assign_hoist" -gt "$$n_assign_nohoist" ]; then \
	  echo -e "\033[01;32m✔\033[00m [MALLOC,$*] Option B split confirmed: $$n_null_hoist hoisted NULL decls, $$n_assign_hoist post-decl alloc calls (vs $$n_assign_nohoist without)"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [MALLOC,$*] Option B split NOT confirmed:"; \
	  echo "  *name = NULL; count   nohoist=$$n_null_nohoist hoist=$$n_null_hoist (expect nohoist=0, hoist>0)"; \
	  echo "  name = KRML_HOST_*  count   nohoist=$$n_assign_nohoist hoist=$$n_assign_hoist (expect hoist > nohoist)"; \
	  false; \
	fi

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) .depend *.cmd *.output *.err *.time *~

.PHONY: all clean
