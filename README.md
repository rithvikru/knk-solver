## lean-knk

Generate a large dataset (50M) of Knights & Knaves puzzles with deterministic Lean 4 solver outputs.

### Prerequisites

- Lean 4 toolchain (managed by `lean-toolchain`)
- Lake build tool

### Build

```bash
lake build
```

### Generate dataset

```bash
lake exe knk --out /tmp/knk-data --count 200000 --seed 42
```

This writes a JSONL manifest containing pairs of Lean problem representations and solutions.

### Structure

- `KNK/Logic.lean` — puzzle DSL and semantics
- `KNK/Solver.lean` — deterministic solver via exhaustive search
- `KNK/Generator.lean` — randomized puzzle generation with difficulty controls
- `Main.lean` — CLI to generate dataset

### License

MIT
