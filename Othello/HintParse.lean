import Othello.Search

/-!
# Reading hints

Hints are produced by an untrusted external solver (`tools/gen.cpp`) and are
stored as strings.  A hint node is written `(` child … child `)`, where a
child is a move — the character with code `48 + bit number` — optionally
followed by the hint node for the position after that move.  Braces `{` … `}`
instead of parentheses mark a node whose moves are to be examined in parallel.

Nothing has to be proved about this parser: the soundness theorem of the
search (`sec_sound`) holds for all hints.
-/

namespace Othello

/-- Parse the children of a hint node; returns them with the rest of the input. -/
def parseChildren : Nat → List Char → List (UInt64 × Hint) × List Char
  | 0, cs => ([], cs)
  | _ + 1, [] => ([], [])
  | fuel + 1, c :: cs =>
    if c = ')' || c = '}' then ([], cs)
    else
      let i : UInt64 := (c.toNat - 48).toUInt64
      match cs with
      | '(' :: cs' =>
        let (sub, rest) := parseChildren fuel cs'
        let (sibs, rest') := parseChildren fuel rest
        ((i, Hint.node sub) :: sibs, rest')
      | '{' :: cs' =>
        let (sub, rest) := parseChildren fuel cs'
        let (sibs, rest') := parseChildren fuel rest
        ((i, Hint.par sub) :: sibs, rest')
      | _ =>
        let (sibs, rest') := parseChildren fuel cs
        ((i, Hint.none) :: sibs, rest')

/-- Parse a hint string. -/
def parseHint (s : String) : Hint :=
  match s.toList with
  | '(' :: cs => Hint.node (parseChildren s.length cs).1
  | '{' :: cs => Hint.par (parseChildren s.length cs).1
  | _ => Hint.none

end Othello
