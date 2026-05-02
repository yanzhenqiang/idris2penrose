CC = cc
CFLAGS = -O2 -Wall

# Default: build the VM.
all: vm

# Build the C VM (the only external dependency).
vm: vm.c
	$(CC) $(CFLAGS) -o vm vm.c

# Run the combinator engine tests (built into vm.c).
test: vm
	cp vm /tmp/vm_test && chmod 755 /tmp/vm_test && /tmp/vm_test test

# Generate singularity.boot from singularity using bootsingularity.sh.
# If bootsingularity.sh is unavailable, the RPG chain can still be
# bootstrapped by placing a pre-generated singularity.boot here.
singularity.boot: singularity bootsingularity.sh
	bash bootsingularity.sh > $@

# Run the full RPG bootstrapping chain.
# This loads singularity, semantically, stringy, binary, algebraically,
# then parity.x through barely.x, outputting a raw combinator dump.
bootstrap: vm singularity.boot
	cp vm /tmp/vm_bootstrap && chmod 755 /tmp/vm_bootstrap && /tmp/vm_bootstrap

# Compile a .x file with the current compiler via the VM's untyped mode.
# Outputs C code to be concatenated with rts.c.
compile-%: vm %.x
	cp vm /tmp/vm_compile && chmod 755 /tmp/vm_compile && cd /mnt/agents/output/x-compiler && /tmp/vm_compile untyped $*.x > $*.c
	cat rts.c $*.c | $(CC) $(CFLAGS) -o $* -x c -

# Run a .x file (compile then execute).
run-%: compile-%
	./$*

# Modern compiler: concatenate inn/ modules and compile with the VM.
# This produces the Precisely compiler executable.
modern: vm
	cat inn/Base.x inn/Ast.x inn/Parser.x inn/Typer.x inn/Kiselyov.x inn/RTS.x inn/Precisely.x > precisely.x
	cp vm /tmp/vm_modern && chmod 755 /tmp/vm_modern && /tmp/vm_modern untyped precisely.x > precisely.c
	cat rts.c precisely.c | $(CC) $(CFLAGS) -o precisely -x c -

# Web IDE: the web/ directory is a static site ready for deployment.
web:
	@echo "Web IDE is in web/index.html"
	@echo "Deploy with: make deploy"

# Deploy web IDE (requires a static hosting tool or manual upload).
deploy:
	@echo "Copy web/ to your static hosting server."
	@echo "Or open web/index.html directly in a browser."

# Clean build artifacts.
clean:
	rm -f vm *.o *.c *.raw barely effectively lonely virtually precisely
	rm -f test-*.c test-* singularity.boot

.PHONY: all test bootstrap modern web deploy clean
