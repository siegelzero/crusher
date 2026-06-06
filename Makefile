# Crusher CSP Solver Makefile
# ============================

.PHONY: help test fzcrusher fzcrusher-profile mztest docker-image docker-test

# Docker image tag for the MiniZinc Challenge 2026 entry (override on the
# command line, e.g. `make docker-image DOCKER_IMAGE=myrepo/crusher:latest`).
DOCKER_IMAGE ?= crusher:mznc2026

# Default target
help:
	@echo "Crusher CSP Solver Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  help              - Show this help message"
	@echo "  test              - Auto-discover and run all test_*.nim files in tests/"
	@echo "  fzcrusher         - Build the FlatZinc solver binary"
	@echo "  fzcrusher-profile - Build fzcrusher with iteration/moveDelta profiling enabled"
	@echo "                       (run with -v to see [Profile] lines)"
	@echo "  mztest            - Run MiniZinc integration tests"
	@echo "  docker-image      - Build the MiniZinc Challenge Docker image ($(DOCKER_IMAGE))"
	@echo "  docker-test       - Build the image and smoke-test the toy instance"
	@echo ""

test:
	@echo "🚀 Running all tests (combined binary)..."
	@echo "==========================================="
	nim c -r --threads:on --mm:arc --deepcopy:on -d:release tests/test_all.nim
	@echo "✅ All tests completed successfully!"

# Build the FlatZinc solver binary
fzcrusher:
	nim c --threads:on --mm:arc --deepcopy:on -d:release -o:fzcrusher src/fzcrusher.nim

# Build with neighborhood-exploration profiling enabled. Adds per-phase timing,
# per-constraint-type neighbor update counts/time, and moveDelta call profiling.
# Profiling output is printed by logExitStats at the end of each Tabu run.
fzcrusher-profile:
	nim c --threads:on --mm:arc --deepcopy:on -d:release -d:profileIteration -o:fzcrusher-profile src/fzcrusher.nim

mztest: fzcrusher
	@bash tests/mztest.sh

# Build the MiniZinc Challenge 2026 image. Builds natively on x86_64 Linux; on
# Apple Silicon you must emulate amd64 via Rosetta (see README "Docker" section)
# — qemu's TCG software emulation hits a gcc ICE while compiling the solver.
docker-image:
	docker build -t $(DOCKER_IMAGE) .

# Smoke-test the built image: run the exact challenge invocation against the
# toy instance baked into the image. Should print a solution and exit 0.
docker-test: docker-image
	docker run --rm $(DOCKER_IMAGE) \
	    minizinc -i --output-mode dzn --output-objective -f /crusher/test.mzn
