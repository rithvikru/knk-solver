# lean-knk

Knights & Knaves puzzle generator with Lean 4 solver.

## Build
```bash
lake build
```

## Usage
```bash
# Generate n=6 puzzles
lake exe knk --n 6 --count 1000 --out n6_puzzles

# Generate with saturation
lake exe knk --saturate --nmin 2 --nmax 8 --out all_puzzles
```

Outputs to `data/NAME.jsonl` in format:
```json
{"puzzle": "says 0 (isKnave 1), ...", "solution": "KNK"}
```