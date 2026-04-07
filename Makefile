# Crusher CSP Solver Makefile
# ============================

.PHONY: help test fzcrusher fzcrusher-profile mztest

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
