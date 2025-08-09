import KNK.Logic

namespace KNK

open PropF

structure GenConfig where
  minPersons : Nat := 2
  maxPersons : Nat := 5
  maxClauses : Nat := 6
  seed       : USize := 0
  deriving Inhabited, Repr

structure RNG where
  state : USize

namespace RNG
  def ofSeed (seed : USize) : RNG := { state := seed }
  def step (x : USize) : USize :=
    let y1 := x ^^^ (x >>> (USize.ofNat 12))
    let y2 := y1 ^^^ (y1 <<< (USize.ofNat 25))
    let y3 := y2 ^^^ (y2 >>> (USize.ofNat 27))
    y3 * 0x2545F4914F6CDD1d

  def next (r : RNG) : USize := step r.state

  def split (r : RNG) : RNG × RNG :=
    let n := next r
    (⟨n⟩, ⟨n ^^^ 0x9E3779B97F4A7C15⟩)

  def randNat (r : RNG) (lo hi : Nat) : Nat × RNG :=
    let (r1, r2) := split r
    let span := if hi <= lo then 1 else hi - lo + 1
    let n := (r1.state.toNat % span) + lo
    (n, r2)

  def choose {α} (r : RNG) (xs : List α) (default : α) : α × RNG :=
    match xs with
    | [] => (default, r)
    | _  =>
      let (i, r') := r.randNat 0 (xs.length - 1)
      (xs.getD i default, r')
end RNG

/- Ensure in-puzzle uniqueness: build up to `m` distinct clauses by resampling duplicates. -/
private def genUniqueClauses (n m : Nat) (r : RNG) : (List PropF) × RNG :=
  let rec fill (need : Nat) (acc : List PropF) (r : RNG) (fuel : Nat) : (List PropF) × RNG :=
    match need with
    | 0 => (acc, r)
    | need'+1 =>
      match fuel with
      | 0 => (acc, r)
      | fuel'+1 =>
        let (a, r) := r.randNat 0 (n - 1)
        let (b, r) := r.randNat 0 (n - 1)
        let (c, r) := r.randNat 0 (n - 1)
        let choices : List PropF :=
          [ KNK.accusation a b
          , KNK.affirmation a b
          , KNK.sameType a b
          , KNK.differentType a b
          , KNK.knaveConjunction a b c
          ]
        let (cl, r) := RNG.choose r choices PropF.tt
        if acc.contains cl then
          fill (need'+1) acc r fuel'
        else
          fill need' (cl :: acc) r fuel'
  fill m [] r (m * 64)

def genPuzzle (cfg : GenConfig) (r : RNG) : Puzzle × RNG :=
  let lo := Nat.max 2 cfg.minPersons
  let hi := Nat.max lo cfg.maxPersons
  let (n, r) := r.randNat lo hi
  let (m, r) := r.randNat 1 (Nat.max 1 cfg.maxClauses)
  let (clauses, r) := genUniqueClauses n m r
  ({ numPersons := n, axioms := clauses.reverse }, r)

/-- Try up to `fuel` attempts to get a uniquely solvable puzzle; return first found. -/
partial def genUniqAux (cfg : GenConfig) (r : RNG) (fuel : Nat) : Option (Puzzle × RNG) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let (p, r1) := genPuzzle cfg r
    let sols := solutions p
    match sols with
    | [ _ ] => some (p, r1)
    | _     => genUniqAux cfg r1 fuel'

def genUniq (cfg : GenConfig) (r : RNG) : Puzzle × RNG :=
  match genUniqAux cfg r 10000 with
  | some pr => pr
  | none => genPuzzle cfg r

end KNK
