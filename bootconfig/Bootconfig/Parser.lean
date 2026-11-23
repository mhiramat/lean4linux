import Bootconfig.Types
import Bootconfig.Lexer

namespace Bootconfig

/-- `xbc_parse_error(msg, p)` -/
def xbcParseError (st : XbcState) (msg : String) (p : Nat) : XbcState × Int :=
  ({ st with errMsg := msg, errPos := Int.ofNat p }, EINVAL)

/-- `xbc_init_node(node, data, flag)` -/
def xbcInitNode (data : Nat) (flag : Nat) : Option XbcNode :=
  if data >= XBC_DATA_MAX then
    none
  else
    -- Since data < 32767 < 32768 (1 <<< 15) and flag is either 0 or 32768,
    -- `data + flag` is bitwise identical to `data | flag` and cleaner for arithmetic proofs.
    some { data := data + flag, child := 0, next := 0, parent := 0 }

/-- `xbc_add_node(data, flag)` -/
def xbcAddNode (st : XbcState) (data : Nat) (flag : Nat) : XbcState × Option Nat :=
  if st.nodes.size == XBC_NODE_MAX then
    (st, none)
  else
    match xbcInitNode data flag with
    | none => (st, none)
    | some node =>
      let idx := st.nodes.size
      ({ st with nodes := st.nodes.push node }, some idx)

/-- `xbc_last_sibling(node)` -/
def xbcLastSibling (st : XbcState) (idx : Nat) : Nat :=
  let rec loop (curr : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => curr
    | fuel' + 1 =>
      if h : curr < st.nodes.size then
        let nxt := st.nodes[curr].next
        if nxt != 0 && nxt < st.nodes.size then
          loop nxt fuel'
        else
          curr
      else
        curr
  loop idx st.nodes.size

/-- `xbc_last_child(node)` -/
def xbcLastChild (st : XbcState) (idx : Nat) : Nat :=
  let rec loop (curr : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => curr
    | fuel' + 1 =>
      if h : curr < st.nodes.size then
        let ch := st.nodes[curr].child
        if ch != 0 && ch < st.nodes.size then
          loop ch fuel'
        else
          curr
      else
        curr
  loop idx st.nodes.size

/-- Helper to update a node at `idx` in `st.nodes` -/
def updateNode (st : XbcState) (idx : Nat) (f : XbcNode → XbcNode) : XbcState :=
  if h : idx < st.nodes.size then
    { st with nodes := st.nodes.set idx (f st.nodes[idx]) }
  else
    st

/-- `__xbc_add_sibling(data, flag, head)` -/
def xbcAddSiblingCore (st : XbcState) (data : Nat) (flag : Nat) (head : Bool) : XbcState × Option Nat :=
  let (st, mNodeIdx) := xbcAddNode st data flag
  match mNodeIdx with
  | none =>
    let (st, _) := xbcParseError st "Too many nodes" data
    (st, none)
  | some nodeIdx =>
    match st.lastParent with
    | none =>
      let st := updateNode st nodeIdx (fun n => { n with parent := XBC_NODE_MAX })
      let sib := xbcLastSibling st 0
      let st := updateNode st sib (fun n => { n with next := nodeIdx })
      (st, some nodeIdx)
    | some lpIdx =>
      let st := updateNode st nodeIdx (fun n => { n with parent := lpIdx })
      let lpChild := if h : lpIdx < st.nodes.size then st.nodes[lpIdx].child else 0
      if lpChild == 0 || head then
        let st := updateNode st nodeIdx (fun n => { n with next := lpChild })
        let st := updateNode st lpIdx (fun n => { n with child := nodeIdx })
        (st, some nodeIdx)
      else
        let sib := xbcLastSibling st lpChild
        let st := updateNode st sib (fun n => { n with next := nodeIdx })
        (st, some nodeIdx)

def xbcAddSibling (st : XbcState) (data : Nat) (flag : Nat) : XbcState × Option Nat :=
  xbcAddSiblingCore st data flag false

def xbcAddHeadSibling (st : XbcState) (data : Nat) (flag : Nat) : XbcState × Option Nat :=
  xbcAddSiblingCore st data flag true

def xbcAddChild (st : XbcState) (data : Nat) (flag : Nat) : XbcState × Option Nat :=
  let (st, mIdx) := xbcAddSibling st data flag
  match mIdx with
  | some idx => ({ st with lastParent := some idx }, some idx)
  | none => (st, none)

/--
`__xbc_open_brace(p)` (Linux v7.4-rc3):
Checks `brace_index >= XBC_DEPTH_MAX` BEFORE writing `open_brace[brace_index++]`,
allowing up to `XBC_DEPTH_MAX` (16) nested braces.
-/
def xbcOpenBraceCore (st : XbcState) (p : Nat) : XbcState × Int :=
  if st.braceIndex >= XBC_DEPTH_MAX then
    xbcParseError st "Exceed max depth of braces" p
  else
    let lpIdx := st.lastParent.getD 0
    let ob := if h : st.braceIndex < st.openBrace.size then
                st.openBrace.set st.braceIndex lpIdx
              else
                st.openBrace
    ({ st with openBrace := ob, braceIndex := st.braceIndex + 1 }, 0)

/-- `__xbc_close_brace(p)` -/
def xbcCloseBraceCore (st : XbcState) (p : Nat) : XbcState × Int :=
  if st.braceIndex == 0 then
    xbcParseError st "Unexpected closing brace" p
  else
    let bi' := st.braceIndex - 1
    let st := { st with braceIndex := bi' }
    match st.lastParent with
    | none => xbcParseError st "Unexpected closing brace" p
    | some lpIdx =>
      let expected := if h : bi' < st.openBrace.size then st.openBrace[bi'] else 0
      if expected != lpIdx then
        xbcParseError st "Unexpected closing brace" p
      else
        let newLp := if bi' == 0 then none
                     else if h : (bi' - 1) < st.openBrace.size then some st.openBrace[bi' - 1]
                     else none
        ({ st with lastParent := newLp }, 0)

/--
`__xbc_parse_value(&v, &next)` (Linux v7.4-rc3):
Caller must ensure `vIn` points to the real value string (no leading spaces).
Trims unquoted values even at EOF (commit 381b391bfaa3).
-/
def xbcParseValue (st : XbcState) (vIn : Nat) : XbcState × Nat × Nat × Int :=
  let firstChar := bufGet st.buf vIn
  let (quotes, vStart) :=
    if firstChar == 34 || firstChar == 39 then -- '"' == 34, '\'' == 39
      (firstChar, vIn + 1)
    else
      (0, vIn)
  let delims : List UInt8 := [44, 59, 10, 35, 125] -- ",;\n#}"
  -- Returns (st, vOut, pOut, cOut, qRem, skipTrim, mErr)
  let rec scanLoop (st : XbcState) (p : Nat) (q : UInt8) (vCurr : Nat) (fuel : Nat)
      : XbcState × Nat × Nat × UInt8 × UInt8 × Bool × Option Int :=
    match fuel with
    | 0 => (st, vCurr, p, 0, q, false, none)
    | fuel' + 1 =>
      let c := bufGet st.buf p
      if c == 0 then
        (st, vCurr, p, 0, q, false, none)
      else if !cIsPrint c && !cIsSpace c then
        let (st, err) := xbcParseError st "Non printable value" p
        (st, vCurr, p, c, q, false, some err)
      else if q != 0 then
        if c != q then
          scanLoop st (p + 1) q vCurr fuel'
        else
          let buf' := bufSet st.buf p 0
          let st := { st with buf := buf' }
          let p' := skipSpacesUntilNewline st.buf (p + 1)
          let c' := bufGet st.buf p'
          if c' != 0 && !delims.contains c' then
            let (st, err) := xbcParseError st "No value delimiter" p'
            (st, vCurr, p', c', 0, true, some err)
          else
            let p'' := if bufGet st.buf p' != 0 then p' + 1 else p'
            (st, vCurr, p'', c', 0, true, none)
      else
        if delims.contains c then
          let buf' := bufSet st.buf p 0
          let st := { st with buf := buf' }
          (st, vCurr, p + 1, c, 0, false, none)
        else
          scanLoop st (p + 1) q vCurr fuel'
  let (st, vOut0, pOut, cOut, qRem, skipTrim, mErr) :=
    scanLoop st vStart quotes vStart (st.buf.size - vStart + 1)
  match mErr with
  | some err => (st, vOut0, pOut, err)
  | none =>
    if qRem != 0 then
      let (st, err) := xbcParseError st "No closing quotes" pOut
      (st, vOut0, pOut, err)
    else
      let (st, vOut) :=
        if skipTrim then
          (st, vOut0)
        else
          let (buf'', vTrimmed) := cStrim st.buf vOut0
          ({ st with buf := buf'' }, vTrimmed)
      let (pFinal, cFinal) :=
        if cOut == 35 then -- '#'
          (skipComment st.buf pOut, (10 : UInt8)) -- '\n'
        else
          (pOut, cOut)
      (st, vOut, pFinal, Int.ofNat cFinal.toNat)

/-- `xbc_parse_array(&__v)` (Linux v7.4-rc3) -/
def xbcParseArray (st : XbcState) (vIn : Nat) : XbcState × Nat × Int :=
  let st :=
    match st.lastParent with
    | none => st
    | some lpIdx =>
      if h : lpIdx < st.nodes.size then
        let ch := st.nodes[lpIdx].child
        if ch != 0 then { st with lastParent := some ch } else st
      else st
  let rec skipCommentsLoop (buf : Array UInt8) (v : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      if bufGet buf v == 35 then -- '#'
        let v' := skipComment buf v
        let v'' := skipSpaces buf v'
        skipCommentsLoop buf v'' fuel'
      else
        v
  let rec loop (st : XbcState) (v : Nat) (fuel : Nat) : XbcState × Nat × Int :=
    match fuel with
    | 0 => (st, v, 0)
    | fuel' + 1 =>
      let v0 := skipSpaces st.buf v
      let v1 := skipCommentsLoop st.buf v0 (st.buf.size - v0 + 1)
      let (st, vParsed, next, c) := xbcParseValue st v1
      if c < 0 then
        (st, vParsed, c)
      else
        let (st, mNodeIdx) := xbcAddChild st vParsed XbcValBit
        match mNodeIdx with
        | none => (st, next, ENOMEM)
        | some _ =>
          if c == 44 then -- ','
            loop st next fuel'
          else
            (st, next, c)
  loop st vIn (st.buf.size - vIn + 1)

/-- `find_match_node(node, k)` -/
def findMatchNode (st : XbcState) (startIdxOpt : Option Nat) (k : Nat) : Option Nat :=
  let kStr := st.getStringAt k
  let rec loop (currOpt : Option Nat) (fuel : Nat) : Option Nat :=
    match fuel, currOpt with
    | 0, _ => none
    | _, none => none
    | fuel' + 1, some curr =>
      if h : curr < st.nodes.size then
        let node := st.nodes[curr]
        let nodeStr := st.getStringAt node.dataOffset
        if nodeStr == kStr then
          some curr
        else
          loop (st.nodeGetNext node) fuel'
      else
        none
  loop startIdxOpt st.nodes.size

/-- `__xbc_add_key(k)` -/
def xbcAddKey (st : XbcState) (k : Nat) : XbcState × Int :=
  if !xbcValidKeyword st.buf k then
    xbcParseError st "Invalid keyword" k
  else if st.nodes.size == 0 then
    let (st, mIdx) := xbcAddChild st k 0
    match mIdx with
    | some _ => (st, 0)
    | none => (st, ENOMEM)
  else
    let startOpt : Option Nat :=
      match st.lastParent with
      | none => some 0
      | some lpIdx =>
        if h : lpIdx < st.nodes.size then
          st.nodeGetSubkey st.nodes[lpIdx]
        else
          none
    match findMatchNode st startOpt k with
    | some matchedIdx =>
      ({ st with lastParent := some matchedIdx }, 0)
    | none =>
      let (st, mIdx) := xbcAddChild st k 0
      match mIdx with
      | some _ => (st, 0)
      | none => (st, ENOMEM)

/-- `__xbc_parse_keys(k)` -/
def xbcParseKeys (st : XbcState) (kIn : Nat) : XbcState × Int :=
  let (buf', k0) := cStrim st.buf kIn
  let st := { st with buf := buf' }
  let rec loop (st : XbcState) (k : Nat) (fuel : Nat) : XbcState × Int :=
    match fuel with
    | 0 => xbcAddKey st k
    | fuel' + 1 =>
      match cStrchr st.buf k 46 with -- '.' == 46
      | none => xbcAddKey st k
      | some dotPos =>
        let buf' := bufSet st.buf dotPos 0
        let st := { st with buf := buf' }
        let (st, ret) := xbcAddKey st k
        if ret != 0 then
          (st, ret)
        else
          loop st (dotPos + 1) fuel'
  loop st k0 (st.buf.size - k0 + 1)

/-- `xbc_parse_kv(&k, v, op)` (Linux v7.4-rc3) -/
def xbcParseKv (st : XbcState) (kIn : Nat) (vIn : Nat) (op : UInt8) : XbcState × Nat × Int :=
  let prevParent := st.lastParent
  let (st, ret) := xbcParseKeys st kIn
  if ret != 0 then
    (st, kIn, ret)
  else
    let v0 := skipSpacesUntilNewline st.buf vIn
    let (st, v, next, c) :=
      if bufGet st.buf v0 == 35 then -- '#'
        let next := skipComment st.buf v0
        let buf' := bufSet st.buf v0 0
        ({ st with buf := buf' }, v0, next, Int.ofNat 10) -- '\n'
      else
        xbcParseValue st v0
    if c < 0 then
      (st, kIn, c)
    else
      let childOpt : Option (Nat × XbcNode) :=
        match st.lastParent with
        | none => none
        | some lpIdx =>
          if h : lpIdx < st.nodes.size then
            match st.nodeGetChild st.nodes[lpIdx] with
            | none => none
            | some cidx =>
              if h2 : cidx < st.nodes.size then
                some (cidx, st.nodes[cidx])
              else none
          else none
      let (st, skipAddHead, errOpt) : XbcState × Bool × Option Int :=
        match childOpt with
        | some (cidx, childNode) =>
          if childNode.isValue then
            if op == 61 then -- '='
              let (st, err) := xbcParseError st "Value is redefined" v
              (st, false, some err)
            else if op == 58 then -- ':'
              let nidx := childNode.next
              match xbcInitNode v XbcValBit with
              | none =>
                let (st, err) := xbcParseError st "Failed to override value" v
                (st, true, some err)
              | some newNode =>
                let st := updateNode st cidx (fun n => { newNode with next := nidx, parent := n.parent })
                (st, true, none)
            else -- op == '+' (43)
              let lastCh := xbcLastChild st cidx
              ({ st with lastParent := some lastCh }, false, none)
          else
            (st, false, none)
        | none => (st, false, none)
      match errOpt with
      | some err => (st, kIn, err)
      | none =>
        let (st, headErrOpt) : XbcState × Option Int :=
          if skipAddHead then
            (st, none)
          else
            let (st, mNode) := xbcAddHeadSibling st v XbcValBit
            match mNode with
            | some _ => (st, none)
            | none => (st, some ENOMEM)
        match headErrOpt with
        | some err => (st, kIn, err)
        | none =>
          let (st, next, c) :=
            if c == 44 then -- ','
              xbcParseArray st next
            else
              (st, next, c)
          if c < 0 then
            (st, kIn, c)
          else
            let st := { st with lastParent := prevParent }
            if c == 125 then -- '}'
              let (st, ret) := xbcCloseBraceCore st (next - 1)
              if ret < 0 then
                (st, kIn, ret)
              else
                (st, next, 0)
            else
              (st, next, 0)

/-- `xbc_parse_key(&k, n)` -/
def xbcParseKey (st : XbcState) (kIn : Nat) (n : Nat) : XbcState × Nat × Int :=
  let prevParent := st.lastParent
  let (buf', kTrim) := cStrim st.buf kIn
  let st := { st with buf := buf' }
  if bufGet st.buf kTrim != 0 then
    let (st, ret) := xbcParseKeys st kTrim
    if ret != 0 then
      (st, kTrim, ret)
    else
      ({ st with lastParent := prevParent }, n, 0)
  else
    (st, n, 0)

/-- `xbc_open_brace(&k, n)` -/
def xbcOpenBrace (st : XbcState) (kIn : Nat) (n : Nat) : XbcState × Nat × Int :=
  let (st, ret) := xbcParseKeys st kIn
  if ret != 0 then
    (st, kIn, ret)
  else
    let (st, ret2) := xbcOpenBraceCore st (n - 1)
    (st, n, ret2)

/-- `xbc_close_brace(&k, n)` -/
def xbcCloseBrace (st : XbcState) (kIn : Nat) (n : Nat) : XbcState × Nat × Int :=
  let (st, kOut, ret) := xbcParseKey st kIn n
  if ret != 0 then
    (st, kOut, ret)
  else
    let (st, ret2) := xbcCloseBraceCore st (n - 1)
    (st, kOut, ret2)

/-- `xbc_parse_tree()` (Linux v7.4-rc3, including post-NUL data check) -/
def xbcParseTree (st : XbcState) : XbcState × Int :=
  let st := { st with lastParent := none }
  let delims : List UInt8 := [123, 125, 61, 43, 59, 58, 10, 35] -- "{}=+;:\n#"
  let rec loop (st : XbcState) (p : Nat) (fuel : Nat) : XbcState × Nat × Int :=
    match fuel with
    | 0 => (st, p, 0)
    | fuel' + 1 =>
      match cStrpbrk st.buf p delims with
      | none =>
        let p' := skipSpaces st.buf p
        if bufGet st.buf p' != 0 then
          let (st, err) := xbcParseError st "No delimiter" p'
          (st, p', err)
        else
          (st, p', 0)
      | some q0 =>
        let c := bufGet st.buf q0
        let buf' := bufSet st.buf q0 0
        let st := { st with buf := buf' }
        let q := q0 + 1
        if c == 58 || c == 43 then -- ':' or '+'
          if bufGet st.buf q != 61 then -- '='
            let msg := if c == 43 then "Wrong '+' operator" else "Wrong ':' operator"
            let (st, err) := xbcParseError st msg ((q + 1) - 2)
            (st, p, err)
          else
            let (st, p', ret) := xbcParseKv st p (q + 1) c
            if ret != 0 then (st, p', ret) else loop st p' fuel'
        else if c == 61 then -- '='
          let (st, p', ret) := xbcParseKv st p q c
          if ret != 0 then (st, p', ret) else loop st p' fuel'
        else if c == 123 then -- '{'
          let (st, p', ret) := xbcOpenBrace st p q
          if ret != 0 then (st, p', ret) else loop st p' fuel'
        else if c == 35 then -- '#'
          let q' := skipComment st.buf q
          let (st, p', ret) := xbcParseKey st p q'
          if ret != 0 then (st, p', ret) else loop st p' fuel'
        else if c == 59 || c == 10 then -- ';' or '\n'
          let (st, p', ret) := xbcParseKey st p q
          if ret != 0 then (st, p', ret) else loop st p' fuel'
        else if c == 125 then -- '}'
          let (st, p', ret) := xbcCloseBrace st p q
          if ret != 0 then (st, p', ret) else loop st p' fuel'
        else
          (st, p, 0)
  let (st, pEnd, ret) := loop st 0 (st.buf.size + 1)
  if ret != 0 then
    (st, ret)
  else
    -- Commit fac634087ad8: Reject unexpected data after null character
    let limit := st.dataSize - 1
    let rec skipNulls (p : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => p
      | fuel' + 1 =>
        if p < limit && bufGet st.buf p == 0 then
          skipNulls (p + 1) fuel'
        else
          p
    let pFinal := skipNulls pEnd (limit - pEnd + 1)
    if pFinal < limit then
      xbcParseError st "Unexpected data after null character" pFinal
    else
      (st, 0)

/-- `xbc_sanity_check_tree()` (#ifndef __KERNEL__) -/
def xbcSanityCheckTree (st : XbcState) : XbcState × Int :=
  let rec loop (i : Nat) (fuel : Nat) : XbcState × Int :=
    match fuel with
    | 0 => (st, 0)
    | fuel' + 1 =>
      if h : i < st.nodes.size then
        let node := st.nodes[i]
        if node.next >= st.nodes.size then
          xbcParseError st "No closing brace" node.dataOffset
        else if node.child >= st.nodes.size then
          xbcParseError st "Broken child node" node.dataOffset
        else
          loop (i + 1) fuel'
      else
        (st, 0)
  loop 0 (st.nodes.size + 1)

/--
`xbc_verify_tree()` (Linux v7.4-rc3):
- Unclosed brace index is already fixed in upstream (`open_brace[brace_index - 1]`).
- `ParserMode.v7_4Original` models the remaining upstream bug where `xbc_node_get_child(n)`
  is used instead of `xbc_node_get_subkey(n)`, skipping subkeys of valued keys.
- `ParserMode.fixed` uses `xbc_node_get_subkey(n)`.
-/
def xbcVerifyTree (st : XbcState) : XbcState × Int :=
  -- 1. Brace closing check (fixed in v7.4-rc3: `open_brace[brace_index - 1]`)
  if st.braceIndex != 0 then
    let obIdx := st.braceIndex - 1
    let nodeIdx := if h : obIdx < st.openBrace.size then st.openBrace[obIdx] else 0
    let dataPos := if h : nodeIdx < st.nodes.size then st.nodes[nodeIdx].dataOffset else 0
    xbcParseError st "Brace is not closed" dataPos
  -- 2. Empty tree check
  else if st.nodes.size == 0 then
    let (st, _) := xbcParseError st "Empty config" 0
    (st, ENOENT)
  else
    -- 3. Key tree limitation check
    let rec walkUp (curr : Nat) (len : Nat) (depth : Nat) (fuel : Nat)
        : Option Nat × Nat × Nat :=
      match fuel with
      | 0 => (none, len, depth)
      | fuel' + 1 =>
        if h : curr < st.nodes.size then
          let node := st.nodes[curr]
          match st.nodeGetNext node with
          | some nxt => (some nxt, len, depth)
          | none =>
            match st.nodeGetParent node with
            | none => (none, len, depth)
            | some pIdx =>
              if hp : pIdx < st.nodes.size then
                let pNode := st.nodes[pIdx]
                let pWlen := cStrlen st.buf pNode.dataOffset + 1
                walkUp pIdx (len - pWlen) (depth - 1) fuel'
              else
                (none, len, depth)
        else
          (none, len, depth)

    let rec verifyLoop (nOpt : Option Nat) (depth : Nat) (len : Nat) (fuel : Nat)
        : XbcState × Int :=
      match fuel, nOpt with
      | 0, _ => (st, 0)
      | _, none => (st, 0)
      | fuel' + 1, some nIdx =>
        if h : nIdx < st.nodes.size then
          let nNode := st.nodes[nIdx]
          let wlen := cStrlen st.buf nNode.dataOffset + 1
          let len' := len + wlen
          if len' > XBC_KEYLEN_MAX then
            xbcParseError st "Too long key length" nNode.dataOffset
          else
            let subkeyOpt : Option Nat :=
              match st.mode with
              | .v7_4Original =>
                match st.nodeGetChild nNode with
                | some cIdx =>
                  if hc : cIdx < st.nodes.size then
                    if st.nodes[cIdx].isKey then some cIdx else none
                  else none
                | none => none
              | .fixed =>
                st.nodeGetSubkey nNode
            match subkeyOpt with
            | some mIdx =>
              let depth' := depth + 1
              if depth' > XBC_DEPTH_MAX then
                let mPos := if hm : mIdx < st.nodes.size then st.nodes[mIdx].dataOffset else 0
                xbcParseError st "Too many key words" mPos
              else
                verifyLoop (some mIdx) depth' len' fuel'
            | none =>
              let lenRestored := len' - wlen
              let (nextOpt, lenNext, depthNext) := walkUp nIdx lenRestored depth st.nodes.size
              verifyLoop nextOpt depthNext lenNext fuel'
        else
          (st, 0)
    verifyLoop (some 0) 1 0 (st.nodes.size * 4 + 1)

/--
`xbc_init(data, size, &emsg, &epos)` (Linux v7.4-rc3)
-/
def xbcInit (rawBytes : Array UInt8) (mode : ParserMode := .v7_4Original) : XbcState × Int :=
  let size := rawBytes.size
  let initSt : XbcState := { mode := mode, errPos := -1 }
  if size > XBC_DATA_MAX || size == 0 then
    let msg := if size != 0 then "Config data is too big" else "Config data is empty"
    ({ initSt with errMsg := msg, errPos := -1 }, ERANGE)
  else
    let buf : Array UInt8 := rawBytes.push 0
    let st : XbcState := {
      initSt with
      buf := buf,
      dataSize := size + 1,
      nodes := #[]
    }
    let (st, ret) := xbcParseTree st
    let (st, ret) := if ret == 0 then xbcVerifyTree st else (st, ret)
    let (st, ret) := if ret == 0 then xbcSanityCheckTree st else (st, ret)
    if ret < 0 then
      (st, ret)
    else
      (st, Int.ofNat st.nodes.size)

/-- Convert an ASCII string to `Array UInt8` purely in the kernel -/
def stringToAsciiBytes (s : String) : Array UInt8 :=
  (s.toList.map (fun c => UInt8.ofNat c.toNat)).toArray

/-- Helper to initialize from a Lean `String` -/
def xbcInitString (s : String) (includeTrailingNullInSize : Bool := false) (mode : ParserMode := .v7_4Original) : XbcState × Int :=
  let ba := stringToAsciiBytes s
  let ba := if includeTrailingNullInSize then ba.push 0 else ba
  xbcInit ba mode

end Bootconfig
