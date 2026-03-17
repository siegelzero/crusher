# Crusher CSP Solver Makefile
# ============================

.PHONY: help test fzcrusher mztest

# Default target
help:
	@echo "Crusher CSP Solver Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  help         - Show this help message"
	@echo "  test         - Auto-discover and run all test_*.nim files in tests/"
	@echo "  fzcrusher    - Build the FlatZinc solver binary"
	@echo "  mztest       - Run MiniZinc integration tests"
	@echo ""

test:
	@echo "🚀 Running all tests (combined binary)..."
	@echo "==========================================="
	nim c -r --threads:on --mm:arc --deepcopy:on -d:release tests/test_all.nim
	@echo "✅ All tests completed successfully!"

# Build the FlatZinc solver binary
fzcrusher:
	nim c --threads:on --mm:arc --deepcopy:on -d:release -o:fzcrusher src/fzcrusher.nim

mztest: fzcrusher
	@bash tests/mztest.sh
