import Std

namespace KNK

/--
Basic domain for Knights & Knaves puzzles.
Each inhabitant either always tells the truth (Knight) or always lies (Knave).
Statements are propositional formulas over inhabitants and logical connectives.
-/

inductive Role where
  | knight
  | knave
  deriving Repr, DecidableEq

abbrev PersonId := Nat

structure World where
  numPersons : Nat
  roleOf : PersonId → Role

namespace World
  def isKnight (w : World) (p : PersonId) : Bool :=
    match w.roleOf p with
    | .knight => true
    | .knave => false

  def isKnave (w : World) (p : PersonId) : Bool := !(w.isKnight p)
end World

/-! Propositional language over persons. -/
inductive PropF where
  | tt
  | ff
  | isKnight (p : PersonId)
  | isKnave (p : PersonId)
  | says (p : PersonId) (φ : PropF)
  | not (φ : PropF)
  | and (φ ψ : PropF)
  | or  (φ ψ : PropF)
  | imp (φ ψ : PropF)
  | iff (φ ψ : PropF)
  deriving Repr, DecidableEq

namespace PropF
  notation:max "¬" φ => PropF.not φ
  infixr:40 " ∧ " => PropF.and
  infixr:35 " ∨ " => PropF.or
  infixr:30 " → " => PropF.imp
  infixr:25 " ↔ " => PropF.iff
end PropF

/-! Semantics: evaluate a formula in a world. -/
partial def eval (w : World) : PropF → Bool
  | .tt => true
  | .ff => false
  | .isKnight p => w.isKnight p
  | .isKnave p => w.isKnave p
  | .says p φ =>
      let truthful := w.isKnight p
      let val := eval w φ
      if truthful then val else !val
  | .not φ => !(eval w φ)
  | .and φ ψ => (eval w φ) && (eval w ψ)
  | .or  φ ψ => (eval w φ) || (eval w ψ)
  | .imp φ ψ => (! (eval w φ)) || (eval w ψ)
  | .iff φ ψ => (eval w φ) == (eval w ψ)

/-- A puzzle is a finite set of inhabitants and a list of statements (formulas) that are asserted to be true. -/
structure Puzzle where
  numPersons : Nat
  axioms : List PropF
  deriving Repr

def Puzzle.satisfied (w : World) (P : Puzzle) : Bool :=
  (P.axioms.all (fun φ => eval w φ))

/-- Enumerate all possible worlds for `n` persons. -/
def allWorlds (n : Nat) : List World :=
  let rec roleLists (k : Nat) : List (List Role) :=
    if k = 0 then [ [] ]
    else
      let prev := roleLists (k - 1)
      List.foldr (fun xs acc => (Role.knight :: xs) :: (Role.knave :: xs) :: acc) [] prev
  let rs := roleLists n
  rs.map (fun roles =>
    { numPersons := n
    , roleOf := fun i => roles.getD i Role.knight
    })

/-- Solutions are the worlds that satisfy all axioms. -/
def solutions (P : Puzzle) : List World :=
  (allWorlds P.numPersons).filter (fun w => Puzzle.satisfied w P)

/- Convenience constructors for common statement patterns. -/
open PropF

def accusation (a b : PersonId) : PropF :=
  -- a says: b is a knave
  .says a (.isKnave b)

def affirmation (a b : PersonId) : PropF :=
  -- a says: b is a knight
  .says a (.isKnight b)

def sameType (a b : PersonId) : PropF :=
  .says a ((.isKnight a) ↔ (.isKnight b))

def differentType (a b : PersonId) : PropF :=
  .says a ((.isKnight a) ↔ (.isKnave b))

def knaveConjunction (a b c : PersonId) : PropF :=
  .says a ((.isKnave b) ∧ (.isKnave c))

end KNK


