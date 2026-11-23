import Bootconfig.Types
import Bootconfig.Lexer

namespace Bootconfig

/-- Helper to check prefix purely on `List Char` -/
def listStartsWith (s pre : List Char) : Option (List Char) :=
  match pre, s with
  | [], rest => some rest
  | p :: ps, c :: cs => if p == c then listStartsWith cs ps else none
  | _ :: _, [] => none

/-- Pure kernel-reducible string intercalate -/
def pureIntercalate (sep : String) (parts : List String) : String :=
  match parts with
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ pureIntercalate sep xs

/-- `xbc_node_match_prefix(node, &prefix)` -/
def xbcNodeMatchPrefix (st : XbcState) (node : XbcNode) (prefixStr : String) : Option String :=
  match st.nodeGetData node with
  | none => none
  | some nodeStr =>
    match listStartsWith prefixStr.toList nodeStr.toList with
    | none => none
    | some [] => some ""
    | some ('.' :: rest) => some (String.ofList rest)
    | some _ => none

/-- `xbc_node_find_subkey(parent, key)` -/
def xbcNodeFindSubkey (st : XbcState) (parentOpt : Option Nat) (key : String) : Option Nat :=
  let startOpt : Option Nat :=
    match parentOpt with
    | some pIdx =>
      if h : pIdx < st.nodes.size then
        st.nodeGetSubkey st.nodes[pIdx]
      else none
    | none =>
      if st.dataSize == 0 || st.nodes.size == 0 then none else some 0
  let rec loop (nodeOpt : Option Nat) (currKey : String) (fuel : Nat) : Option Nat :=
    match fuel, nodeOpt with
    | 0, _ => none
    | _, none => none
    | fuel' + 1, some idx =>
      if h : idx < st.nodes.size then
        let node := st.nodes[idx]
        if !node.isKey then
          none
        else
          match xbcNodeMatchPrefix st node currKey with
          | none =>
            loop (st.nodeGetNext node) currKey fuel'
          | some restKey =>
            if !restKey.isEmpty then
              loop (st.nodeGetSubkey node) restKey fuel'
            else
              some idx
      else
        none
  loop startOpt key (st.nodes.size + 1)

/-- `xbc_node_find_value(parent, key, &vnode)` -/
def xbcNodeFindValue (st : XbcState) (parentOpt : Option Nat) (key : String) : Option String × Option Nat :=
  match xbcNodeFindSubkey st parentOpt key with
  | none => (none, none)
  | some kIdx =>
    if h : kIdx < st.nodes.size then
      let kNode := st.nodes[kIdx]
      if !kNode.isKey then
        (none, none)
      else
        match st.nodeGetChild kNode with
        | none => (some "", none)
        | some cIdx =>
          if hc : cIdx < st.nodes.size then
            let cNode := st.nodes[cIdx]
            if !cNode.isValue then
              (none, none)
            else
              (st.nodeGetData cNode, some cIdx)
          else
            (some "", none)
    else
      (none, none)

/--
`xbc_node_compose_key_after(root, node, buf, size)` (Linux v7.4-rc3):
- Reflects commit `cab697164b47` (depth check before push, allowing depth == XBC_DEPTH_MAX).
- `ParserMode.v7_4Original`:
  1. Only climbs 1 parent if `xbc_node_is_value(node)` (corrupts 2nd+ array value nodes).
  2. Checks `node == root` ONLY before climbing value parent, so passing a value node directly
     under `root` results in `depth == 0` and returns `.ok ""` (leaving `buf` uninitialized in C!)
     instead of `.error EINVAL`.
- `ParserMode.fixed`:
  Climbs all parent value nodes in a loop, then checks `if !node || node == root then return -EINVAL`.
-/
def xbcNodeComposeKeyAfter (st : XbcState) (rootOpt : Option Nat) (nodeOpt : Option Nat)
    : Except Int String :=
  match nodeOpt with
  | none => .error EINVAL
  | some nodeIdx0 =>
    if rootOpt == some nodeIdx0 then
      .error EINVAL
    else if h0 : nodeIdx0 < st.nodes.size then
      let startKeyOpt : Option Nat :=
        match st.mode with
        | .v7_4Original =>
          let n0 := st.nodes[nodeIdx0]
          if n0.isValue then st.nodeGetParent n0 else some nodeIdx0
        | .fixed =>
          let rec climbValues (curr : Nat) (fuel : Nat) : Option Nat :=
            match fuel with
            | 0 => some curr
            | fuel' + 1 =>
              if hc : curr < st.nodes.size then
                let cn := st.nodes[curr]
                if cn.isValue then
                  match st.nodeGetParent cn with
                  | none => none
                  | some p => climbValues p fuel'
                else
                  some curr
              else
                none
          climbValues nodeIdx0 st.nodes.size
      -- In `fixed` mode, re-check `!node || node == root` after climbing value parents
      let postClimbErr :=
        match st.mode with
        | .v7_4Original => false
        | .fixed => startKeyOpt.isNone || startKeyOpt == rootOpt
      if postClimbErr then
        .error EINVAL
      else
        let rec collectKeys (currOpt : Option Nat) (acc : List Nat) (fuel : Nat)
            : Except Int (Option Nat × List Nat) :=
          match fuel, currOpt with
          | 0, _ => .ok (currOpt, acc)
          | _, none => .ok (none, acc)
          | fuel' + 1, some curr =>
            if rootOpt == some curr then
              .ok (some curr, acc)
            else if acc.length == XBC_DEPTH_MAX then
              .error ERANGE
            else
              let acc' := curr :: acc
              if hc : curr < st.nodes.size then
                collectKeys (st.nodeGetParent st.nodes[curr]) acc' fuel'
              else
                .ok (none, acc')
        match collectKeys startKeyOpt [] (st.nodes.size + 1) with
        | .error e => .error e
        | .ok (finalNodeOpt, keys) =>
          if finalNodeOpt.isNone && rootOpt.isSome then
            .error EINVAL
          else
            let parts := keys.filterMap (fun idx =>
              if h : idx < st.nodes.size then st.nodeGetData st.nodes[idx] else none)
            .ok (pureIntercalate "." parts)
    else
      .error EINVAL

/-- `xbc_node_find_next_leaf(root, node)` -/
def xbcNodeFindNextLeaf (st : XbcState) (rootOpt : Option Nat) (nodeOpt : Option Nat) : Option Nat :=
  if st.dataSize == 0 || st.nodes.size == 0 then
    none
  else
    let rec descendToLeaf (currOpt : Option Nat) (fuel : Nat) : Option Nat :=
      match fuel, currOpt with
      | 0, _ => currOpt
      | _, none => none
      | fuel' + 1, some curr =>
        if h : curr < st.nodes.size then
          let node := st.nodes[curr]
          if st.nodeIsLeaf node then
            some curr
          else
            descendToLeaf (st.nodeGetChild node) fuel'
        else
          none

    match nodeOpt with
    | none =>
      let startIdx := rootOpt.getD 0
      descendToLeaf (some startIdx) st.nodes.size
    | some currIdx =>
      if h : currIdx < st.nodes.size then
        let currNode := st.nodes[currIdx]
        match st.nodeGetSubkey currNode with
        | some subIdx =>
          descendToLeaf (some subIdx) st.nodes.size
        | none =>
          if rootOpt == some currIdx then
            none
          else
            let rec climbUntilNext (cIdx : Nat) (fuel : Nat) : Option Nat :=
              match fuel with
              | 0 => none
              | fuel' + 1 =>
                if hc : cIdx < st.nodes.size then
                  let cNode := st.nodes[cIdx]
                  match st.nodeGetNext cNode with
                  | some nxtIdx => some nxtIdx
                  | none =>
                    match st.nodeGetParent cNode with
                    | none => none
                    | some pIdx =>
                      if rootOpt == some pIdx then
                        none
                      else
                        climbUntilNext pIdx fuel'
                else
                  none
            match climbUntilNext currIdx st.nodes.size with
            | none => none
            | some nextStart => descendToLeaf (some nextStart) st.nodes.size
      else
        none

/-- `xbc_node_find_next_key_value(root, &leaf)` -/
def xbcNodeFindNextKeyValue (st : XbcState) (rootOpt : Option Nat) (leafOpt : Option Nat)
    : Option (Nat × String) :=
  match xbcNodeFindNextLeaf st rootOpt leafOpt with
  | none => none
  | some leafIdx =>
    if h : leafIdx < st.nodes.size then
      let leafNode := st.nodes[leafIdx]
      match st.nodeGetChild leafNode with
      | none => some (leafIdx, "")
      | some cIdx =>
        if hc : cIdx < st.nodes.size then
          let valStr := (st.nodeGetData st.nodes[cIdx]).getD ""
          some (leafIdx, valStr)
        else
          some (leafIdx, "")
    else
      none

/--
Model of `xbc_snprint_cmdline_filter(buf, size, root, NULL, NULL)` (Linux v7.4-rc3).
Tracks both the rendered total length and whether an out-of-bounds pointer (`buf + len` with `len > size`
on a non-NULL `buf`) was formed during `snprintf()` calls.
-/
structure CmdlineRenderResult where
  totalLen     : Nat
  rendered     : String
  oobPtrFormed : Bool
  deriving Repr, BEq, DecidableEq

def strContainsWhitespace (s : String) : Bool :=
  s.toList.any (fun c => c == ' ' || c == '\t' || c == '\r' || c == '\n')

def xbcSnprintCmdlineModel (st : XbcState) (bufIsNonNull : Bool) (size : Nat) (rootOpt : Option Nat)
    : Except Int CmdlineRenderResult :=
  let checkOob (len : Nat) : Bool :=
    match st.mode with
    | .v7_4Original =>
      -- In v7.4-rc3: `snprintf(buf ? buf + len : NULL, rest(len, size), ...)`
      -- Forming `buf + len` when `buf != NULL` and `len > size` is out-of-bounds pointer arithmetic UB!
      bufIsNonNull && len > size
    | .fixed =>
      -- In fixed mode: `snprintf(buf && len < size ? buf + len : NULL, rest(len, size), ...)`
      -- Never forms `buf + len` when `len >= size`!
      false

  let rec renderArray (vOpt : Option Nat) (keyName : String) (len : Nat) (acc : String) (oob : Bool) (fuel : Nat)
      : Nat × String × Bool :=
    match fuel, vOpt with
    | 0, _ => (len, acc, oob)
    | _, none => (len, acc, oob)
    | fuel' + 1, some vIdx =>
      if h : vIdx < st.nodes.size then
        let vNode := st.nodes[vIdx]
        let val := (st.nodeGetData vNode).getD ""
        let q := if strContainsWhitespace val then "\"" else ""
        let piece := keyName ++ "=" ++ q ++ val ++ q ++ " "
        let oob' := oob || checkOob len
        renderArray (st.nodeGetChild vNode) keyName (len + piece.length) (acc ++ piece) oob' fuel'
      else
        (len, acc, oob)

  let rec loop (leafOpt : Option Nat) (len : Nat) (acc : String) (oob : Bool) (fuel : Nat)
      : Except Int CmdlineRenderResult :=
    match fuel with
    | 0 => .ok { totalLen := len, rendered := acc, oobPtrFormed := oob }
    | fuel' + 1 =>
      match xbcNodeFindNextLeaf st rootOpt leafOpt with
      | none => .ok { totalLen := len, rendered := acc, oobPtrFormed := oob }
      | some knodeIdx =>
        if rootOpt == some knodeIdx then
          loop (some knodeIdx) len acc oob fuel'
        else
          match xbcNodeComposeKeyAfter st rootOpt (some knodeIdx) with
          | .error e => .error e
          | .ok keyName =>
            if h : knodeIdx < st.nodes.size then
              match st.nodeGetChild st.nodes[knodeIdx] with
              | none =>
                let piece := keyName ++ " "
                let oob' := oob || checkOob len
                loop (some knodeIdx) (len + piece.length) (acc ++ piece) oob' fuel'
              | some vIdx =>
                let (len', acc', oob') := renderArray (some vIdx) keyName len acc oob st.nodes.size
                loop (some knodeIdx) len' acc' oob' fuel'
            else
              loop (some knodeIdx) len acc oob fuel'
  loop none 0 "" false (st.nodes.size + 1)

/-- Collect all key-value pairs in the tree -/
def xbcCollectList (st : XbcState) : List (String × List String) :=
  let rec collectArrayValues (vOpt : Option Nat) (fuel : Nat) (acc : List String) : List String :=
    match fuel, vOpt with
    | 0, _ => acc.reverse
    | _, none => acc.reverse
    | fuel' + 1, some vIdx =>
      if h : vIdx < st.nodes.size then
        let vNode := st.nodes[vIdx]
        let s := (st.nodeGetData vNode).getD ""
        collectArrayValues (st.nodeGetChild vNode) fuel' (s :: acc)
      else
        acc.reverse

  let rec loop (leafOpt : Option Nat) (fuel : Nat) (acc : List (String × List String))
      : List (String × List String) :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      match xbcNodeFindNextLeaf st none leafOpt with
      | none => acc.reverse
      | some leafIdx =>
        match xbcNodeComposeKeyAfter st none (some leafIdx) with
        | .error _ => acc.reverse
        | .ok keyStr =>
          let vals :=
            if h : leafIdx < st.nodes.size then
              match st.nodeGetChild st.nodes[leafIdx] with
              | none => [""]
              | some cIdx => collectArrayValues (some cIdx) st.nodes.size []
            else
              [""]
          loop (some leafIdx) fuel' ((keyStr, vals) :: acc)
  loop none (st.nodes.size + 1) []

end Bootconfig
