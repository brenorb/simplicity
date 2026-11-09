# Standalone benchmark of candidate C sketches against existing libsimplicity jets.
#
# The in-tree C sources are compiled read-only into build/ (ignored by git);
# nothing is written into ../../C.  Candidate sketches live in
# ../candidates/<name>/sketch.c and are never linked into libsimplicity.
#
#   make                  build build/bench
#   make verify           check every sketch against the Haskell reference vectors
#   make bench            time sketches and the calibration panel (see README.md)

C       := ../../C
BUILD   := build
CC      ?= cc
# -O2 matches the optimisation the nix C wrapper applies to the upstream build.
OPT     ?= -O2
CFLAGS  := $(OPT) -std=c11 -I$(C) -I$(C)/include -I. -DPRODUCTION
WARN    := -Wall -Wextra -Wno-unused-parameter
VECTORS ?= ../reports/data/candidate-c-vectors.tsv

LIB_SRCS := frame.c jets.c jets-secp256k1.c sha256.c
LIB_OBJS := $(addprefix $(BUILD)/lib/,$(LIB_SRCS:.c=.o))
SKETCHES := $(sort $(wildcard ../candidates/*/sketch.c))
SK_OBJS  := $(patsubst ../candidates/%/sketch.c,$(BUILD)/sk/%.o,$(SKETCHES))

all: $(BUILD)/bench

$(BUILD)/lib/%.o: $(C)/%.c
	@mkdir -p $(dir $@)
	$(CC) -c $(CFLAGS) -Wno-conversion -o $@ $<

$(BUILD)/sk/%.o: ../candidates/%/sketch.c sketch.h limbs.h
	@mkdir -p $(dir $@)
	$(CC) -c $(CFLAGS) $(WARN) -o $@ $<

$(BUILD)/registry.c: $(SKETCHES) gen_registry.sh
	@mkdir -p $(dir $@)
	sh gen_registry.sh $(SKETCHES) > $@

$(BUILD)/bench: harness.c panel.c $(BUILD)/registry.c $(SK_OBJS) $(LIB_OBJS) sketch.h
	$(CC) $(CFLAGS) $(WARN) -o $@ harness.c panel.c $(BUILD)/registry.c $(SK_OBJS) $(LIB_OBJS)

verify: $(BUILD)/bench
	$(BUILD)/bench verify $(VECTORS)

bench: $(BUILD)/bench
	$(BUILD)/bench bench $(VECTORS)

clean:
	rm -rf $(BUILD)

.PHONY: all verify bench clean
