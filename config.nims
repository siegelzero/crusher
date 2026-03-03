# Find the actual project root (directory containing this config.nims)
import std/os

proc findProjectRoot(): string =
  # Start from the current projectDir and walk up to find config.nims
  var current = projectDir()
  while current != "/" and current != "":
    if fileExists(current / "config.nims"):
      return current
    current = parentDir(current)
  return projectDir() # fallback

let projectRoot = findProjectRoot()
switch("path", projectRoot & "/src")

# Use system malloc instead of Nim's built-in allocator.
# Nim's thread-local heap allocator has a race condition in cross-thread
# deallocation (alloc.nim listRemove) that causes SIGSEGV when objects
# allocated on init worker threads are freed on tabu search worker threads.
switch("define", "useMalloc")
