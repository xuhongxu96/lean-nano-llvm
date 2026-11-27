import LeanNanoLlvm.AST.AST

/-!
# Lexer for LLVM IR text

`tokenizeWithLines` splits a `.ll` source into `Tok`s, recording the source line of each token
(used for `llubi`'s `<stdin>:LINE` locations). `;` comments and whitespace are dropped.
-/

namespace LeanNanoLlvm.AST.Parser

/-- Lexer tokens for LLVM IR text. -/
inductive Tok where
  | ident   (s : String)
  | localId (id : RawId)
  | globalId (id : RawId)
  | metaId  (s : String)      -- `!foo` or `!0` (without leading `!`)
  | attrGrp (n : Nat)         -- `#0`
  | intLit  (n : Int)
  | hexLit  (tag : Char) (val : Nat) -- `0x...` (`tag = 'd'`), `0xH...`, `0xR...`, `0xK...`
  | fltLit  (neg : Bool) (mantissa : Nat) (exp10 : Int)
  | strLit  (s : String)
  | eq | comma | colon | lparen | rparen | lbrack | rbrack | lbrace | rbrace
  | langle | rangle | lpacked | rpacked | ellipsis | bang | star
  | eof
deriving Repr, DecidableEq, Inhabited

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '.' || c == '$'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '$' || c == '-'

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then 10 + (c.toNat - 'A'.toNat)
  else 0

def parseNatStr (s : String) : Option Nat :=
  if s.isEmpty then none
  else
    s.toList.foldl (init := some 0) fun acc c =>
      match acc with
      | none => none
      | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none

def parseHexNat (cs : List Char) : Nat :=
  cs.foldl (init := 0) fun acc c => acc * 16 + hexVal c

private def mkRawId (s : String) : RawId :=
  match parseNatStr s with
  | some n => .anonymous n
  | none => .name s

/-- Token accumulator that also records the (0-based) source line of every token. -/
structure LexAcc where
  toks  : Array Tok := #[]
  lines : Array Nat := #[]
  line  : Nat := 0

namespace LexAcc
@[inline] def push (a : LexAcc) (t : Tok) : LexAcc :=
  { a with toks := a.toks.push t, lines := a.lines.push a.line }
@[inline] def nl (a : LexAcc) : LexAcc := { a with line := a.line + 1 }
end LexAcc

/-- Lex an LLVM IR source string into a token array plus per-token 0-based line numbers
(total via structural recursion on `List Char`). -/
def tokenizeWithLines (input : String) : Array Tok × Array Nat :=
  let rec skipComment : List Char → List Char
    | [] => []
    | '\n' :: cs => cs
    | _ :: cs => skipComment cs
  let rec readQuoted (acc : List Char) : List Char → String × List Char
    | [] => (String.ofList acc.reverse, [])
    | '"' :: cs => (String.ofList acc.reverse, cs)
    | '\\' :: c :: cs => readQuoted (c :: '\\' :: acc) cs
    | c :: cs => readQuoted (c :: acc) cs
  let rec readIdent (acc : List Char) : List Char → String × List Char
    | c :: cs =>
      if isIdentCont c then readIdent (c :: acc) cs
      else (String.ofList acc.reverse, c :: cs)
    | [] => (String.ofList acc.reverse, [])
  let rec readDigits (acc : List Char) : List Char → List Char × List Char
    | c :: cs =>
      if c.isDigit then readDigits (c :: acc) cs
      else (acc.reverse, c :: cs)
    | [] => (acc.reverse, [])
  let rec readHex (acc : List Char) : List Char → List Char × List Char
    | c :: cs =>
      if isHexDigit c then readHex (c :: acc) cs
      else (acc.reverse, c :: cs)
    | [] => (acc.reverse, [])
  let rec readIdAfterSigil : List Char → RawId × List Char
    | '"' :: cs =>
      let (s, rest) := readQuoted [] cs
      (.name s, rest)
    | cs =>
      let (s, rest) := readIdent [] cs
      (mkRawId s, rest)
  let rec go (fuel : Nat) (acc : LexAcc) : List Char → LexAcc
    | [] => acc.push .eof
    | cs =>
      match fuel with
      | 0 => acc.push .eof
      | fuel' + 1 =>
        match cs with
        | [] => acc.push .eof
        | c :: rest =>
          if c.isWhitespace then go fuel' (if c == '\n' then acc.nl else acc) rest
          else if c == ';' then go fuel' acc.nl (skipComment rest)
          else if c == '=' then go fuel' (acc.push .eq) rest
          else if c == ',' then go fuel' (acc.push .comma) rest
          else if c == ':' then go fuel' (acc.push .colon) rest
          else if c == '(' then go fuel' (acc.push .lparen) rest
          else if c == ')' then go fuel' (acc.push .rparen) rest
          else if c == '[' then go fuel' (acc.push .lbrack) rest
          else if c == ']' then go fuel' (acc.push .rbrack) rest
          else if c == '{' then go fuel' (acc.push .lbrace) rest
          else if c == '}' then
            match rest with
            | '>' :: rest2 => go fuel' (acc.push .rpacked) rest2
            | _ => go fuel' (acc.push .rbrace) rest
          else if c == '<' then
            match rest with
            | '{' :: rest2 => go fuel' (acc.push .lpacked) rest2
            | _ => go fuel' (acc.push .langle) rest
          else if c == '>' then go fuel' (acc.push .rangle) rest
          else if c == '*' then go fuel' (acc.push .star) rest
          else if c == '.' then
            match rest with
            | '.' :: '.' :: rest2 => go fuel' (acc.push .ellipsis) rest2
            | _ =>
              let (s, rest2) := readIdent ['.'] rest
              go fuel' (acc.push (.ident s)) rest2
          else if c == '%' then
            let (rid, rest2) := readIdAfterSigil rest
            go fuel' (acc.push (.localId rid)) rest2
          else if c == '@' then
            let (rid, rest2) := readIdAfterSigil rest
            go fuel' (acc.push (.globalId rid)) rest2
          else if c == '!' then
            match rest with
            | c2 :: _ =>
              if c2.isAlphanum || c2 == '_' || c2 == '.' then
                let (s, rest2) := readIdent [] rest
                go fuel' (acc.push (.metaId s)) rest2
              else
                go fuel' (acc.push .bang) rest
            | [] => go fuel' (acc.push .bang) rest
          else if c == '#' then
            let (ds, rest2) := readDigits [] rest
            let n := (parseNatStr (String.ofList ds)).getD 0
            go fuel' (acc.push (.attrGrp n)) rest2
          else if c == '"' then
            let (s, rest2) := readQuoted [] rest
            go fuel' (acc.push (.strLit s)) rest2
          else if c == '0' then
            match rest with
            | 'x' :: tag :: rest2 =>
              if tag == 'H' || tag == 'R' || tag == 'K' || tag == 'L' || tag == 'M' then
                let (hs, rest3) := readHex [] rest2
                go fuel' (acc.push (.hexLit tag (parseHexNat hs))) rest3
              else
                let (hs, rest3) := readHex [] (tag :: rest2)
                go fuel' (acc.push (.hexLit 'd' (parseHexNat hs))) rest3
            | _ =>
              -- Decimal int or float starting with 0
              let (intDs, rest1) := readDigits ['0'] rest
              match rest1 with
              | '.' :: rest2 =>
                let (fracDs, rest3) := readDigits [] rest2
                let allDs := intDs ++ fracDs
                let mant := (parseNatStr (String.ofList allDs)).getD 0
                let baseExp : Int := - (Int.ofNat fracDs.length)
                let (exp10, rest4) :=
                  match rest3 with
                  | 'e' :: '+' :: r | 'E' :: '+' :: r =>
                    let (eds, r') := readDigits [] r
                    (baseExp + Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                  | 'e' :: '-' :: r | 'E' :: '-' :: r =>
                    let (eds, r') := readDigits [] r
                    (baseExp - Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                  | 'e' :: r | 'E' :: r =>
                    let (eds, r') := readDigits [] r
                    (baseExp + Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                  | _ => (baseExp, rest3)
                go fuel' (acc.push (.fltLit false mant exp10)) rest4
              | _ =>
                let n := (parseNatStr (String.ofList intDs)).getD 0
                go fuel' (acc.push (.intLit (Int.ofNat n))) rest1
          else if c.isDigit || (c == '-' && match rest with | d :: _ => d.isDigit | [] => false) then
            let (neg, startRest) := if c == '-' then (true, rest) else (false, c :: rest)
            let (intDs, rest1) := readDigits [] startRest
            match rest1 with
            | '.' :: rest2 =>
              let (fracDs, rest3) := readDigits [] rest2
              let allDs := intDs ++ fracDs
              let mant := (parseNatStr (String.ofList allDs)).getD 0
              let baseExp : Int := - (Int.ofNat fracDs.length)
              let (exp10, rest4) :=
                match rest3 with
                | 'e' :: '+' :: r | 'E' :: '+' :: r =>
                  let (eds, r') := readDigits [] r
                  (baseExp + Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                | 'e' :: '-' :: r | 'E' :: '-' :: r =>
                  let (eds, r') := readDigits [] r
                  (baseExp - Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                | 'e' :: r | 'E' :: r =>
                  let (eds, r') := readDigits [] r
                  (baseExp + Int.ofNat ((parseNatStr (String.ofList eds)).getD 0), r')
                | _ => (baseExp, rest3)
              go fuel' (acc.push (.fltLit neg mant exp10)) rest4
            | _ =>
              let n := (parseNatStr (String.ofList intDs)).getD 0
              let v : Int := if neg then - (Int.ofNat n) else Int.ofNat n
              go fuel' (acc.push (.intLit v)) rest1
          else if isIdentStart c || ((c == '+' || c == '-') && match rest with | d :: _ => d.isAlpha | [] => false) then
            let (s, rest2) := readIdent [c] rest
            go fuel' (acc.push (.ident s)) rest2
          else
            -- Skip unrecognized single punctuation character
            go fuel' acc rest
  let cs := input.toList
  let acc := go (cs.length + 1) {} cs
  (acc.toks, acc.lines)

end LeanNanoLlvm.AST.Parser
