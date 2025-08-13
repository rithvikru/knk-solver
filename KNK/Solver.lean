import KNK.Logic

namespace KNK

open PropF

structure Solution where
  roles : List Role
  deriving Repr

def solveUnique (P : Puzzle) : Option Solution :=
  let sols := solutions P
  match sols with
  | [w] =>
      let roles := List.range P.numPersons |>.map (fun i => w.roleOf i)
      some { roles }
  | _ => none

@[inline]
def roleToString : Role → String
  | .knight => "K"
  | .knave => "N"

@[inline]
def solutionToString (s : Solution) : String :=
  s.roles.map roleToString |>.foldl (· ++ ·) ""

@[inline]
def axiomsString (P : Puzzle) : String :=
  let rec pp (φ : PropF) : String :=
    match φ with
    | .tt => "tt"
    | .ff => "ff"
    | .isKnight p => s!"isKnight {p}"
    | .isKnave p => s!"isKnave {p}"
    | .says p ψ => s!"says {p} (" ++ pp ψ ++ ")"
    | .not ψ => s!"not (" ++ pp ψ ++ ")"
    | .and a b => s!"and (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .or a b => s!"or (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .imp a b => s!"imp (" ++ pp a ++ ") (" ++ pp b ++ ")"
    | .iff a b => s!"iff (" ++ pp a ++ ") (" ++ pp b ++ ")"
  P.axioms.map pp |>.intersperse ", " |>.foldl (· ++ ·) ""

end KNK
