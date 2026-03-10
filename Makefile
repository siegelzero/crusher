# Crusher CSP Solver Makefile
# ============================

.PHONY: help test test-parallel csplib clean all format fzcrusher

# Default target
help:
	@echo "Crusher CSP Solver Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  help         - Show this help message"
	@echo "  test         - Auto-discover and run all test_*.nim files in tests/"
	@echo "  test-parallel- Run all tests with threading support enabled"
	@echo "  csplib       - Run CSPLib benchmark tests (csplib/)"
	@echo "  clean        - Clean all compiled executables"
	@echo "  format       - Strip trailing whitespace from all *.nim files"
	@echo "  fzcrusher    - Build the FlatZinc solver binary"
	@echo "  all          - Run all targets (currently just test)"
	@echo ""

test:
	@echo "🚀 Running all tests (combined binary)..."
	@echo "==========================================="
	nim c -r --threads:on --mm:arc --deepcopy:on -d:release tests/test_all.nim
	@echo "✅ All tests completed successfully!"

test-parallel: clean
	@echo "🚀 Auto-discovering and running all test files with threading..."
	@echo "============================================================="
	@for test_file in $$(find tests -name 'test_*.nim' | sort); do \
		echo "Running $$test_file with threading..."; \
		nim c -r --threads:on --mm:arc --deepcopy:on -d:release $$test_file || exit 1; \
		echo ""; \
	done
	@echo "✅ All parallel tests completed successfully!"

# Format code by stripping trailing whitespace
format:
	@echo "🎨 Stripping trailing whitespace from *.nim files..."
	@find . -name "*.nim" -type f -exec sed -i '' 's/[[:space:]]*$$//' {} \;
	@echo "✅ Formatting complete"

# Build the FlatZinc solver binary
fzcrusher:
	nim c --threads:on --mm:arc --deepcopy:on -d:release -o:fzcrusher src/fzcrusher.nim

# Run all targets
all: test

