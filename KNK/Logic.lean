import Std

namespace KNK

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
end World

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

partial def eval (w : World) : PropF → Bool
  | .tt => true
  | .ff => false
  | .isKnight p => w.isKnight p
  | .isKnave p => !w.isKnight p
  | .says p φ =>
      let truthful := w.isKnight p
      let val := eval w φ
      if truthful then val else !val
  | .not φ => !(eval w φ)
  | .and φ ψ => (eval w φ) && (eval w ψ)
  | .or  φ ψ => (eval w φ) || (eval w ψ)
  | .imp φ ψ => (! (eval w φ)) || (eval w ψ)
  | .iff φ ψ => (eval w φ) == (eval w ψ)

structure Puzzle where
  numPersons : Nat
  axioms : List PropF
  deriving Repr

def Puzzle.satisfied (w : World) (P : Puzzle) : Bool :=
  P.axioms.all (fun φ => eval w φ)

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

def solutions (P : Puzzle) : List World :=
  (allWorlds P.numPersons).filter (fun w => Puzzle.satisfied w P)

end KNK
