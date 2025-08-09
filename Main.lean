import KNK.Logic
import KNK.Solver
import KNK.Generator
import Std
import Std.Data.HashSet
import Lean.Data.Json

open KNK

structure Args where
  outDir : String := "."
  count  : Nat := 1000
  seed   : Nat := 0
  offset : Nat := 0
  nPersons : Option Nat := none
  maxClauses : Nat := 8
  dist : String := ""
  deriving Inhabited

def parseArgs (xs : List String) : Args :=
  let rec go (a : Args) : List String → Args
    | [] => a
    | "--out" :: d :: rest => go { a with outDir := d } rest
    | "--count" :: c :: rest => go { a with count := c.toNat! } rest
    | "--seed" :: s :: rest => go { a with seed := s.toNat! } rest
    | "--offset" :: o :: rest => go { a with offset := o.toNat! } rest
    | "--n" :: n :: rest => go { a with nPersons := some (n.toNat!) } rest
    | "--max-clauses" :: m :: rest => go { a with maxClauses := m.toNat! } rest
    | "--dist" :: d :: rest => go { a with dist := d } rest
    | _ :: rest => go a rest
  go {} xs

def ensureDir (path : System.FilePath) : IO Unit := do
  unless (← System.FilePath.pathExists path) do
    IO.FS.createDirAll path

def writeFile (path : System.FilePath) (content : String) : IO Unit := do
  IO.FS.writeFile path content

def mkManifestLine (id : Nat) (p : Puzzle) (s : Solution) : String :=
  let puzzleStr := KNK.leanPuzzleString p
  let solStr := KNK.solutionToString s
  let leanJson := toString (Lean.Json.str puzzleStr)
  let solJson := toString (Lean.Json.str solStr)
  "{" ++
    "\"id\":" ++ toString id ++ "," ++
    "\"n\":" ++ toString p.numPersons ++ "," ++
    "\"lean\":" ++ leanJson ++ "," ++
    "\"solution\":" ++ solJson ++
  "}\n"

/-! Canonical keys to deduplicate puzzles by set of axioms (ignoring order and duplicate clauses). -/
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

def insertSorted (s : String) : List String → List String
  | [] => [s]
  | x :: xs => if s ≤ x then s :: x :: xs else x :: insertSorted s xs

def sortStrings (xs : List String) : List String :=
  xs.foldl (fun acc s => insertSorted s acc) []

def dedupSorted (xs : List String) : List String :=
  let rec go : List String → Option String → List String → List String
    | [], _, acc => acc.reverse
    | x :: xs, none, acc => go xs (some x) (x :: acc)
    | x :: xs, some prev, acc => if x = prev then go xs (some prev) acc else go xs (some x) (x :: acc)
  go xs none []

def puzzleKey (P : Puzzle) : String :=
  let ks := P.axioms.map clauseKey
  let ks := dedupSorted (sortStrings ks)
  "n=" ++ toString P.numPersons ++ "|" ++ String.intercalate ";" ks

/-- Compute target counts per N for a uniform distribution across N=2..8. -/
def countsUniform (total : Nat) : List (Nat × Nat) :=
  let base := total / 7
  let rem := total % 7
  let ns := [2,3,4,5,6,7,8]
  let rec assign (i : Nat) (r : Nat) (acc : List (Nat × Nat)) (rest : List Nat) : List (Nat × Nat) :=
    match rest with
    | [] => acc.reverse
    | n :: rest' =>
      let extra := if r > 0 then 1 else 0
      let r' := if r > 0 then r - 1 else r
      assign (i+1) r' ((n, base + extra) :: acc) rest'
  assign 0 rem [] ns

/-- Compute target counts per N for the skew distribution. -/
def countsSkew (total : Nat) : List (Nat × Nat) :=
  let ps : List (Nat × Nat) := [(2,10),(3,12),(4,14),(5,16),(6,18),(7,16),(8,14)]
  let base : List (Nat × Nat) := ps.map (fun (n,p) => (n, total * p / 100))
  let assigned := base.foldl (fun s (_,k) => s + k) 0
  let rem := total - assigned
  -- distribute remainder round-robin from lowest N upward
  let ns := [2,3,4,5,6,7,8]
  -- simple list-based remainder distribution
  let rec distribute (r : Nat) (acc : List (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
    if r = 0 then acc
    else
      let idx := ns.getD (i % ns.length) 2
      let acc' := acc.map (fun (n,k) => if n = idx then (n, k+1) else (n,k))
      distribute (r-1) acc' (i+1)
  distribute rem base 0

def countsByDist (total : Nat) (dist : String) : List (Nat × Nat) :=
  if dist = "uniform" then countsUniform total
  else if dist = "skew" then countsSkew total
  else countsUniform total

def generateForN (h : IO.FS.Handle) (idStart : Nat) (n : Nat) (k : Nat) (maxClauses : Nat) (seed : Nat) : IO (Nat × RNG) := do
  let cfg : GenConfig := { minPersons := n, maxPersons := n, maxClauses := maxClauses, seed := (USize.ofNat seed) }
  let mut rng := RNG.ofSeed cfg.seed
  let mut seenKey : Std.HashSet String := (Std.HashSet.emptyWithCapacity k)
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
    | none => pure ()
  pure (produced, rng)

def main (argv : List String) : IO Unit := do
  let a := parseArgs argv
  let out := System.FilePath.mk a.outDir
  ensureDir out
  let manifest := out / "manifest.jsonl"
  let h ← IO.FS.Handle.mk manifest IO.FS.Mode.write
  if a.nPersons.isSome then
    -- single-N mode (backward compatible)
    let n := a.nPersons.get!
    let (produced, _) ← generateForN h a.offset n a.count a.maxClauses (a.seed + a.offset + n*1000003)
    IO.FS.Handle.flush h
    IO.println s!"Wrote {produced} entries to {manifest}"
  else if a.dist ≠ "" then
    -- distribution mode
    let targets := countsByDist a.count a.dist
    let mut idBase := a.offset
    let mut total := 0
    for (n,k) in targets do
      let seedN := a.seed + idBase + n*1000003
      let (producedN, _) ← generateForN h idBase n k a.maxClauses seedN
      idBase := idBase + producedN
      total := total + producedN
    IO.FS.Handle.flush h
    IO.println s!"Wrote {total} entries to {manifest}"
  else
    -- legacy random-N mode within [2,8]
    let cfg : GenConfig := { minPersons := 2, maxPersons := 8, maxClauses := a.maxClauses, seed := (USize.ofNat (a.seed + a.offset)) }
    let mut rng := RNG.ofSeed cfg.seed
    let mut seenKey : Std.HashSet String := (Std.HashSet.emptyWithCapacity a.count)
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
      | none => pure ()
    IO.FS.Handle.flush h
    IO.println s!"Wrote {produced} entries to {manifest}"
