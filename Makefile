# Crusher CSP Solver Makefile
# ============================

.PHONY: help test clean all

# Default target
help:
	@echo "Crusher CSP Solver Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  help     - Show this help message"
	@echo "  test     - Auto-discover and run all test_*.nim files in tests/"
	@echo "  clean    - Clean all compiled executables"
	@echo "  all      - Run all targets (currently just test)"
	@echo ""

test:
	@echo "🚀 Auto-discovering and running all test files..."
	@echo "================================================"
	@for test_file in $$(find tests -name 'test_*.nim' | sort); do \
		echo "Running $$test_file..."; \
		nim c -r --path:./src $$test_file || exit 1; \
		echo ""; \
	done
	@echo "✅ All tests completed successfully!"

# Clean all compiled executables
clean:
	@echo "🧹 Cleaning all compiled executables..."
	find . -type f -perm +111 -not -path "./.git/*" -delete 2>/dev/null || true
	@echo "✅ Cleanup complete"

# Run all targets
all: test