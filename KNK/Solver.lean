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
  P.axioms.map pp |>.intersperse ", " |>.foldl (· ++ ·) ""

end KNK
