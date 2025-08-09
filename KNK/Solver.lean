import KNK.Logic

namespace KNK

open PropF

structure Solution where
  roles : List Role
  deriving Repr

namespace Solution
  def toWorld (s : Solution) : World :=
    { numPersons := s.roles.length
    , roleOf := fun i => s.roles.getD i Role.knight
    }

  def pretty (s : Solution) : String :=
    let chars := s.roles.zipIdx.map (fun (r, i) =>
      s!"{i}:{match r with | Role.knight => "K" | Role.knave => "N"}")
    String.intercalate "," chars
end Solution

/-- Deterministic exhaustive search solver. Returns the unique solution if exactly one exists. -/
def solveUnique (P : Puzzle) : Option Solution :=
  let sols := solutions P
  match sols with
  | [w] =>
      let roles := List.range P.numPersons |>.map (fun i => w.roleOf i)
      some { roles }
  | _ => none

/-- Return all satisfying assignments, as solutions. -/
def solveAll (P : Puzzle) : List Solution :=
  solutions P |>.map (fun w =>
    let roles := List.range P.numPersons |>.map (fun i => w.roleOf i)
    { roles })

/-! Serialize puzzles and solutions for dataset. -/
@[inline]
def roleToString : Role → String
  | .knight => "K"
  | .knave => "N"

@[inline]
def solutionToString (s : Solution) : String :=
  s.roles.map roleToString |>.foldl (· ++ ·) ""

/-! Pretty-print a Lean snippet that constructs this puzzle. -/
@[inline]
def leanPuzzleString (P : Puzzle) : String :=
  let header := "open KNK PropF\n"
  let rec pp (φ : PropF) : String :=
    match φ with
    | .tt => "PropF.tt"
    | .ff => "PropF.ff"
    | .isKnight p => s!"PropF.isKnight {p}"
    | .isKnave p => s!"PropF.isKnave {p}"
    | .says p ψ => s!"PropF.says {p} (" ++ pp ψ ++ ")"
    | .not ψ => s!"PropF.not (" ++ pp ψ ++ ")"
    | .and a b => s!"PropF.and (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .or a b => s!"PropF.or (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .imp a b => s!"PropF.imp (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .iff a b => s!"PropF.iff (" ++ pp a ++ ") (" ++ pp b ++ ")"
  let rec insertSorted' (s : String) : List String → List String
    | [] => [s]
    | x :: xs => if s ≤ x then s :: x :: xs else x :: insertSorted' s xs
  let sortStrings (xs : List String) : List String :=
    xs.foldl (fun acc s => insertSorted' s acc) []
  let dedupSorted (xs : List String) : List String :=
    let rec go : List String → Option String → List String → List String
      | [], _, acc => acc.reverse
      | x :: xs, none, acc => go xs (some x) (x :: acc)
      | x :: xs, some prev, acc => if x = prev then go xs (some prev) acc else go xs (some x) (x :: acc)
    go xs none []
  let axList := dedupSorted (sortStrings (P.axioms.map pp))
  let axioms := axList.intersperse ", " |>.foldl (· ++ ·) ""
  header ++ "def puzzle : KNK.Puzzle := { numPersons := " ++ toString P.numPersons
    ++ ", axioms := [ " ++ axioms ++ " ] }\n"

end KNK
