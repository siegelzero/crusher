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
	@echo "  test     - Compile and run all tests"
	@echo "  clean    - Clean all compiled executables"
	@echo "  all      - Run all targets (currently just test)"
	@echo ""

# Main test target - runs all tests
test:
	@echo "🚀 Compiling and running all Crusher tests..."
	@echo "=============================================="
	@echo ""
	@echo "📋 Test 1/2: Latin Square (4x4)"
	nim c --path:./src tests/test_latin_square.nim
	./tests/test_latin_square
	@echo ""
	@echo "📋 Test 2/2: Magic Square (both constraint types)"
	nim c --path:./src tests/test_magic_square.nim
	./tests/test_magic_square
	@echo ""
	@echo "🎉 All tests completed successfully!"

# Clean all compiled executables
clean:
	@echo "🧹 Cleaning all compiled executables..."
	find . -type f -perm +111 -not -path "./.git/*" -delete 2>/dev/null || true
	@echo "✅ Cleanup complete"

# Run all targets
all: test