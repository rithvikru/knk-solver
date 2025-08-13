import KNK.Logic
import KNK.Solver
import KNK.Generator
import Std.Data.HashSet
import Lean.Data.Json

open KNK

structure Args where
  outName : String := "output"
  count  : Nat := 1000
  seed   : Nat := 0
  offset : Nat := 0
  nPersons : Option Nat := none
  maxClauses : Nat := 8
  saturate : Bool := false
  nMin : Nat := 2
  nMax : Nat := 8
  plateauWindow : Nat := 10000
  plateauBps : Nat := 0
  maxPerN : Nat := 0
  deriving Inhabited

def parseArgs (xs : List String) : Args :=
  let rec go (a : Args) : List String → Args
    | [] => a
    | "--out" :: d :: rest => go { a with outName := d } rest
    | "--count" :: c :: rest => go { a with count := c.toNat! } rest
    | "--seed" :: s :: rest => go { a with seed := s.toNat! } rest
    | "--offset" :: o :: rest => go { a with offset := o.toNat! } rest
    | "--n" :: n :: rest => go { a with nPersons := some (n.toNat!) } rest
    | "--max-clauses" :: m :: rest => go { a with maxClauses := m.toNat! } rest
    | "--saturate" :: rest => go { a with saturate := true } rest
    | "--nmin" :: n :: rest => go { a with nMin := n.toNat! } rest
    | "--nmax" :: n :: rest => go { a with nMax := n.toNat! } rest
    | "--plateau-window" :: w :: rest => go { a with plateauWindow := w.toNat! } rest
    | "--plateau-bps" :: b :: rest => go { a with plateauBps := b.toNat! } rest
    | "--max-per-n" :: m :: rest => go { a with maxPerN := m.toNat! } rest
    | _ :: rest => go a rest
  go {} xs

def ensureDir (path : System.FilePath) : IO Unit := do
  unless (← System.FilePath.pathExists path) do
    IO.FS.createDirAll path

def mkManifestLine (_id : Nat) (p : Puzzle) (s : Solution) : String :=
  let puzzleStr := KNK.axiomsString p
  let solStr := KNK.solutionToString s
  let puzzleJson := toString (Lean.Json.str puzzleStr)
  let solJson := toString (Lean.Json.str solStr)
  "{" ++
    "\"puzzle\":" ++ puzzleJson ++ "," ++
    "\"solution\":" ++ solJson ++
  "}\n"

open PropF in
def clauseKey : PropF → String
  | .tt => "tt"
  | .ff => "ff"
  | .isKnight p => s!"K {p}"
  | .isKnave p => s!"N {p}"
  | .says p φ => s!"S {p} (" ++ clauseKey φ ++ ")"
  | .not φ => s!"¬(" ++ clauseKey φ ++ ")"
  | .and a b => s!"(& " ++ clauseKey a ++ ", " ++ clauseKey b ++ ")"
  | .or a b  => s!"(| " ++ clauseKey a ++ ", " ++ clauseKey b ++ ")"
  | .imp a b => s!"(-> " ++ clauseKey a ++ ", " ++ clauseKey b ++ ")"
  | .iff a b => s!"(<-> " ++ clauseKey a ++ ", " ++ clauseKey b ++ ")"

def puzzleKey (P : Puzzle) : String :=
  let ks := P.axioms.map clauseKey
  let sorted := ks.toArray.qsort (·<·) |>.toList
  let rec dedup : List String → List String
    | [] => []
    | [x] => [x]
    | x :: y :: xs => if x == y then dedup (y :: xs) else x :: dedup (y :: xs)
  let deduped := dedup sorted
  "n=" ++ toString P.numPersons ++ "|" ++ String.intercalate ";" deduped

def saturateForN (h : IO.FS.Handle) (idStart : Nat) (n : Nat) (maxClauses : Nat)
    (seed : Nat) (window : Nat) (bps : Nat) (maxPerN : Nat) : IO (Nat × RNG) := do
  let cfg : GenConfig := { minPersons := n, maxPersons := n, maxClauses := maxClauses, seed := (USize.ofNat seed) }
  let mut rng := RNG.ofSeed cfg.seed
  let mut seenKey : Std.HashSet String := Std.HashSet.emptyWithCapacity (if maxPerN = 0 then 1024 else maxPerN)
  let mut produced := 0
  let mut windowTries := 0
  let mut windowNew := 0
  let target := if maxPerN = 0 then Nat.pow 2 31 else maxPerN
  while produced < target do
    let (p, r1) := KNK.genUniq cfg rng
    rng := r1
    match KNK.solveUnique p with
    | some sol =>
        let key := puzzleKey p
        if seenKey.contains key then
          pure ()
        else
          seenKey := seenKey.insert key
          let line := mkManifestLine (idStart + produced) p sol
          h.putStr line
          produced := produced + 1
          windowNew := windowNew + 1
          if produced % 10000 == 0 then
            IO.println s!"{produced} puzzles generated"
    | none => pure ()
    windowTries := windowTries + 1
    if windowTries ≥ window then
      if bps > 0 then
        if windowNew * 10000 ≤ windowTries * bps then
          break
        else
          windowTries := 0
          windowNew := 0
  pure (produced, rng)

def generateForN (h : IO.FS.Handle) (idStart : Nat) (n : Nat) (k : Nat) (maxClauses : Nat) (seed : Nat) : IO (Nat × RNG) := do
  let cfg : GenConfig := { minPersons := n, maxPersons := n, maxClauses := maxClauses, seed := (USize.ofNat seed) }
  let mut rng := RNG.ofSeed cfg.seed
  let mut seenKey : Std.HashSet String := Std.HashSet.emptyWithCapacity k
  let mut produced := 0
  while produced < k do
    let (p, r1) := KNK.genUniq cfg rng
    rng := r1
    match KNK.solveUnique p with
    | some sol =>
        let key := puzzleKey p
        if seenKey.contains key then
          pure ()
        else
          seenKey := seenKey.insert key
          let line := mkManifestLine (idStart + produced) p sol
          h.putStr line
          produced := produced + 1
          if produced % 10000 == 0 then
            IO.println s!"  Generated {produced} unique puzzles for n={n}..."
    | none => pure ()
  pure (produced, rng)

def main (argv : List String) : IO Unit := do
  let a := parseArgs argv
  let dataDir := System.FilePath.mk "data"
  ensureDir dataDir
  let manifest := dataDir / s!"{a.outName}.jsonl"
  let h ← IO.FS.Handle.mk manifest IO.FS.Mode.write
  if a.saturate then
    let mut idBase := a.offset
    let mut total := 0
    for n in List.range (a.nMax + 1) do
      if n < a.nMin || n < 2 then
        pure ()
      else
        let seedN := a.seed + idBase + n*1000003
        let (producedN, _) ← saturateForN h idBase n a.maxClauses seedN a.plateauWindow a.plateauBps a.maxPerN
        idBase := idBase + producedN
        total := total + producedN
    IO.FS.Handle.flush h
    IO.println s!"Wrote {total} entries to {manifest}"
  else if a.nPersons.isSome then
    let n := a.nPersons.get!
    let (produced, _) ← generateForN h a.offset n a.count a.maxClauses (a.seed + a.offset + n*1000003)
    IO.FS.Handle.flush h
    IO.println s!"Wrote {produced} entries to {manifest}"
  else
    let cfg : GenConfig := { minPersons := 2, maxPersons := 8, maxClauses := a.maxClauses, seed := (USize.ofNat (a.seed + a.offset)) }
    let mut rng := RNG.ofSeed cfg.seed
    let mut seenKey : Std.HashSet String := Std.HashSet.emptyWithCapacity a.count
    let mut produced := 0
    while produced < a.count do
      let (p, r1) := KNK.genUniq cfg rng
      rng := r1
      match KNK.solveUnique p with
      | some sol =>
          let key := puzzleKey p
          if seenKey.contains key then
            pure ()
          else
            seenKey := seenKey.insert key
            let line := mkManifestLine (a.offset + produced) p sol
            h.putStr line
            produced := produced + 1
            if produced % 10000 == 0 then
              IO.println s!"  Generated {produced} unique puzzles..."
      | none => pure ()
    IO.FS.Handle.flush h
    IO.println s!"Wrote {produced} entries to {manifest}"
