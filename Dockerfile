# Crusher — MiniZinc Challenge 2026 entry (Local Search class)
#
# Multi-stage build on the official challenge base image. The builder stage
# installs Nim and compiles the FlatZinc solver; the runtime stage carries only
# the binary, the MiniZinc library overrides, and the solver config, registering
# Crusher as the default MiniZinc solver.
#
# Build:  docker build -t crusher:mznc2026 .
# Test:   docker run --rm crusher:mznc2026 \
#           minizinc -i --output-mode dzn --output-objective -f /crusher/test.mzn

# ---------------------------------------------------------------------------
# Builder
# ---------------------------------------------------------------------------
FROM minizinc/mznc2026:latest AS builder

ARG NIM_VERSION=2.2.6

# build-essential provides gcc + make (Nim shells out to the C compiler).
RUN apt-get update -y \
    && apt-get install -y --no-install-recommends \
        build-essential curl xz-utils ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Install the official prebuilt Nim toolchain (the distro's apt Nim is too old;
# Crusher needs >= 2.2).
RUN curl -fsSL "https://nim-lang.org/download/nim-${NIM_VERSION}-linux_x64.tar.xz" \
        -o /tmp/nim.tar.xz \
    && mkdir -p /opt/nim \
    && tar -xJf /tmp/nim.tar.xz -C /opt/nim --strip-components=1 \
    && rm /tmp/nim.tar.xz
ENV PATH="/opt/nim/bin:${PATH}"

WORKDIR /src
COPY . /src

# Compile the solver (flags come from the Makefile + config.nims, which also
# forces --define:useMalloc to avoid a Nim allocator race on cross-thread free).
RUN make fzcrusher

# Assemble the install tree the runtime stage will carry.
RUN mkdir -p /install/crusher/mznlib \
    && cp /src/fzcrusher /install/crusher/fzcrusher \
    && cp -r /src/minizinc/mznlib/. /install/crusher/mznlib/ \
    && cp /src/minizinc/crusher.docker.msc /install/crusher/crusher.msc

# ---------------------------------------------------------------------------
# Runtime
# ---------------------------------------------------------------------------
FROM minizinc/mznc2026:latest

COPY --from=builder /install/crusher /crusher

# A tiny toy instance for smoke-testing the image.
RUN printf 'array[1..4] of var 1..4: x;\ninclude "alldifferent.mzn";\nconstraint alldifferent(x);\nsolve satisfy;\n' \
        > /crusher/test.mzn

# Register Crusher as the default MiniZinc solver: add /crusher to the solver
# search path and make it the default for the empty tag.
RUN mkdir -p "$HOME/.minizinc" \
    && printf '{"mzn_solver_path": ["/crusher"], "tagDefaults": [["", "org.crusher.crusher"]]}\n' \
        > "$HOME/.minizinc/Preferences.json"

# Sanity check at build time: Crusher must be resolvable as the default solver.
RUN minizinc --solvers | grep -qi crusher
