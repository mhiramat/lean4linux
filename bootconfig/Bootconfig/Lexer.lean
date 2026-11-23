import Bootconfig.Types

namespace Bootconfig

/-- C `isspace`: space, \t (9), \n (10), \v (11), \f (12), \r (13) -/
def cIsSpace (b : UInt8) : Bool :=
  b == 32 || (b >= 9 && b <= 13)

/-- C `isprint`: ASCII 0x20 .. 0x7e -/
def cIsPrint (b : UInt8) : Bool :=
  b >= 0x20 && b <= 0x7e

/-- C `isalnum`: 0-9, A-Z, a-z -/
def cIsAlnum (b : UInt8) : Bool :=
  (b >= 48 && b <= 57) || (b >= 65 && b <= 90) || (b >= 97 && b <= 122)

/-- Read byte at `p` from buffer (returns 0 if out of bounds) -/
def bufGet (buf : Array UInt8) (p : Nat) : UInt8 :=
  if h : p < buf.size then buf[p] else 0

/-- Write byte at `p` in buffer -/
def bufSet (buf : Array UInt8) (p : Nat) (v : UInt8) : Array UInt8 :=
  if h : p < buf.size then buf.set p v else buf

/-- `strlen(p)` on null-terminated buffer starting at `p` -/
def cStrlen (buf : Array UInt8) (p : Nat) : Nat :=
  let rec loop (i : Nat) (fuel : Nat) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if bufGet buf i == 0 then acc
      else loop (i + 1) fuel' (acc + 1)
  loop p (buf.size - p) 0

/-- `strchr(p, c)` on null-terminated buffer starting at `p` -/
def cStrchr (buf : Array UInt8) (p : Nat) (c : UInt8) : Option Nat :=
  let rec loop (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let b := bufGet buf i
      if b == c then some i
      else if b == 0 then none
      else loop (i + 1) fuel'
  loop p (buf.size - p)

/-- Check if byte `c` is in ASCII string `chars` (like `strchr(chars, c) != NULL`, including `\0` if `c == 0`) -/
def inCharSet (chars : List UInt8) (c : UInt8) : Bool :=
  c == 0 || chars.contains c

/-- `strpbrk(p, accept)` on null-terminated buffer starting at `p` -/
def cStrpbrk (buf : Array UInt8) (p : Nat) (accept : List UInt8) : Option Nat :=
  let rec loop (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let b := bufGet buf i
      if b == 0 then none
      else if accept.contains b then some i
      else loop (i + 1) fuel'
  loop p (buf.size - p)

/-- `skip_spaces(str)` -/
def skipSpaces (buf : Array UInt8) (p : Nat) : Nat :=
  let rec loop (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel' + 1 =>
      let b := bufGet buf i
      if cIsSpace b then loop (i + 1) fuel' else i
  loop p (buf.size - p)

/-- `skip_spaces_until_newline(p)` -/
def skipSpacesUntilNewline (buf : Array UInt8) (p : Nat) : Nat :=
  let rec loop (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel' + 1 =>
      let b := bufGet buf i
      if cIsSpace b && b != 10 then loop (i + 1) fuel' else i
  loop p (buf.size - p)

/-- `skip_comment(p)` -/
def skipComment (buf : Array UInt8) (p : Nat) : Nat :=
  match cStrchr buf p 10 with -- '\n' == 10
  | none => p + cStrlen buf p
  | some nl => nl + 1

/--
`strim(s)` in-place: trims trailing spaces by writing `\0`, and returns pointer past leading spaces.
Matches `tools/bootconfig/include/linux/bootconfig.h`:
```c
size = strlen(s);
if (!size) return s;
end = s + size - 1;
while (end >= s && isspace(*end)) end--;
*(end + 1) = '\0';
return skip_spaces(s);
```
-/
def cStrim (buf : Array UInt8) (s : Nat) : Array UInt8 × Nat :=
  let size := cStrlen buf s
  if size == 0 then
    (buf, s)
  else
    let rec trimBack (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => s
      | fuel' + 1 =>
        if cIsSpace (bufGet buf i) then
          if i == s then s
          else trimBack (i - 1) fuel'
        else
          i + 1
    let termPos := trimBack (s + size - 1) size
    let buf' := bufSet buf termPos 0
    let startPos := skipSpaces buf' s
    (buf', startPos)

/-- `xbc_valid_keyword(key)` -/
def xbcValidKeyword (buf : Array UInt8) (key : Nat) : Bool :=
  if bufGet buf key == 0 then
    false
  else
    let rec loop (i : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        let b := bufGet buf i
        if b == 0 then true
        else if cIsAlnum b || b == 45 || b == 95 then -- '-' == 45, '_' == 95
          loop (i + 1) fuel'
        else
          false
    loop key (buf.size - key)

end Bootconfig
