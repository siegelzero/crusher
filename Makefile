# Crusher CSP Solver Makefile
# ============================

.PHONY: help test test-parallel clean all format

# Default target
help:
	@echo "Crusher CSP Solver Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  help         - Show this help message"
	@echo "  test         - Auto-discover and run all test_*.nim files in tests/"
	@echo "  test-parallel- Run all tests with threading support enabled"
	@echo "  clean        - Clean all compiled executables"
	@echo "  format       - Strip trailing whitespace from all *.nim files"
	@echo "  all          - Run all targets (currently just test)"
	@echo ""

test: clean
	@echo "🚀 Auto-discovering and running all test files..."
	@echo "================================================"
	@for test_file in $$(find tests -name 'test_*.nim' | sort); do \
		echo "Running $$test_file..."; \
		nim c -r --threads:on --mm:arc --deepcopy:on -d:release $$test_file || exit 1; \
		echo ""; \
	done
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

# Clean all compiled executables
clean:
	@echo "🧹 Cleaning all compiled executables and backup files..."
	@find . -type f -perm +111 -not -path "./.git/*" -delete 2>/dev/null || true
	@find . -name "*~" -type f -delete 2>/dev/null || true
	@echo "✅ Cleanup complete"

# Format code by stripping trailing whitespace
format:
	@echo "🎨 Stripping trailing whitespace from *.nim files..."
	@find . -name "*.nim" -type f -exec sed -i '' 's/[[:space:]]*$$//' {} \;
	@echo "✅ Formatting complete"

# Run all targets
all: test

