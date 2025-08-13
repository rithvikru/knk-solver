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

private def genFormula (n : Nat) (depth : Nat) (r : RNG) : PropF × RNG :=
  match depth with
  | 0 =>
    let (choice, r) := r.randNat 0 3
    let (person, r) := r.randNat 0 (n - 1)
    match choice with
    | 0 => (PropF.isKnight person, r)
    | 1 => (PropF.isKnave person, r)
    | 2 => (PropF.tt, r)
    | _ => (PropF.ff, r)
  | depth' + 1 =>
    let (choice, r) := r.randNat 0 4
    match choice with
    | 0 =>
      let (subformula, r) := genFormula n depth' r
      (PropF.not subformula, r)
    | 1 =>
      let (left, r) := genFormula n depth' r
      let (right, r) := genFormula n depth' r
      (PropF.and left right, r)
    | 2 =>
      let (left, r) := genFormula n depth' r
      let (right, r) := genFormula n depth' r
      (PropF.or left right, r)
    | 3 =>
      let (left, r) := genFormula n depth' r
      let (right, r) := genFormula n depth' r
      (PropF.imp left right, r)
    | _ =>
      let (left, r) := genFormula n depth' r
      let (right, r) := genFormula n depth' r
      (PropF.iff left right, r)

private def genStatement (n : Nat) (maxDepth : Nat) (r : RNG) : PropF × RNG :=
  let (speaker, r) := r.randNat 0 (n - 1)
  let (depth, r) := r.randNat 0 maxDepth
  let (nestedSays, r) := r.randNat 0 10

  if nestedSays = 0 && depth > 0 then
    let (innerSpeaker, r) := r.randNat 0 (n - 1)
    let (innerFormula, r) := genFormula n (depth - 1) r
    (PropF.says speaker (PropF.says innerSpeaker innerFormula), r)
  else
    let (formula, r) := genFormula n depth r
    (PropF.says speaker formula, r)

private def genUniqueClauses (n m : Nat) (r : RNG) : (List PropF) × RNG :=
  let rec fill (need : Nat) (acc : List PropF) (r : RNG) (fuel : Nat) : (List PropF) × RNG :=
    match need with
    | 0 => (acc, r)
    | need'+1 =>
      match fuel with
      | 0 => (acc, r)
      | fuel'+1 =>
        let maxDepth := 3
        let (statement, r) := genStatement n maxDepth r
        if acc.contains statement then
          fill (need'+1) acc r fuel'
        else
          fill need' (statement :: acc) r fuel'
  fill m [] r (m * 64)

def genPuzzle (cfg : GenConfig) (r : RNG) : Puzzle × RNG :=
  let lo := Nat.max 2 cfg.minPersons
  let hi := Nat.max lo cfg.maxPersons
  let (n, r) := r.randNat lo hi
  let (m, r) := r.randNat 1 (Nat.max 1 cfg.maxClauses)
  let (clauses, r) := genUniqueClauses n m r
  ({ numPersons := n, axioms := clauses.reverse }, r)

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
