namespace Bootconfig

/-- Constants from `include/linux/bootconfig.h` -/
def XBC_KEY : UInt16 := 0
def XBC_VALUE : UInt16 := (1 : UInt16) <<< (15 : UInt16)
def XBC_DATA_MAX : Nat := 32767
def XBC_NODE_MAX : Nat := 8192
def XBC_KEYLEN_MAX : Nat := 256
def XBC_DEPTH_MAX : Nat := 16

/-- Linux errno constants used by bootconfig -/
def EINVAL : Int := -22
def ENOMEM : Int := -12
def ENOENT : Int := -2
def EBUSY  : Int := -16
def ERANGE : Int := -34
def ENODEV : Int := -19

/--
`struct xbc_node` from `include/linux/bootconfig.h`.
Note that in C, `next`, `child`, `parent`, `data` are `uint16_t`.
We use `Nat` in the structure for clean theorem proving and indexing,
while enforcing the `uint16_t` bit layout and bounds in operations.
-/
structure XbcNode where
  next   : Nat := 0
  child  : Nat := 0
  parent : Nat := 0
  data   : Nat := 0
  deriving Repr, BEq, Inhabited, DecidableEq

def XbcValBit : Nat := 32768 -- 1 <<< 15

def XbcNode.isValue (node : XbcNode) : Bool :=
  node.data >= XbcValBit

def XbcNode.isKey (node : XbcNode) : Bool :=
  !node.isValue

def XbcNode.isArray (node : XbcNode) : Bool :=
  node.isValue && node.child != 0

def XbcNode.dataOffset (node : XbcNode) : Nat :=
  node.data % XbcValBit

/--
Parser mode (synchronized with Linux v7.4-rc3 `lib/bootconfig.c`):
- `v7_4Original`: 100% compatible with upstream Linux v7.4-rc3 (`381b391bfaa3`)
- `fixed`: Fixes all remaining & newly discovered bugs:
  1. `xbc_node_get_subkey` in `xbc_verify_tree` so mixed value+subkey nodes don't bypass depth/length checks
  2. `while (node && xbc_node_is_value(node))` + post-loop `if (!node || node == root) return -EINVAL;`
     in `xbc_node_compose_key_after` (fixes both 2nd+ array element corruption and root-value empty-return bug)
  3. `buf && len < size ? buf + len : NULL` in `xbc_snprint_cmdline_filter` to avoid out-of-bounds pointer arithmetic UB
-/
inductive ParserMode where
  | v7_4Original
  | fixed
  deriving Repr, BEq, DecidableEq, Inhabited

/--
Global state of `lib/bootconfig.c`, represented functionally.
`buf` models the in-place mutable `char *xbc_data` buffer (null-terminated bytes).
-/
structure XbcState where
  nodes      : Array XbcNode := #[]
  buf        : Array UInt8 := #[]
  dataSize   : Nat := 0
  lastParent : Option Nat := none
  errMsg     : String := ""
  errPos     : Int := -1
  openBrace  : Array Nat := Array.replicate XBC_DEPTH_MAX 0
  braceIndex : Nat := 0
  mode       : ParserMode := .v7_4Original
  deriving Repr, Inhabited

/-- Helper to read a null-terminated string starting at `offset` in `buf`. -/
def XbcState.getStringAt (st : XbcState) (offset : Nat) : String :=
  let rec loop (i : Nat) (fuel : Nat) (acc : List Char) : List Char :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      if h : i < st.buf.size then
        let b := st.buf[i]
        if b == 0 then
          acc.reverse
        else
          loop (i + 1) fuel' (Char.ofNat b.toNat :: acc)
      else
        acc.reverse
  String.ofList (loop offset (st.buf.size - offset) [])

/-- `xbc_node_get_data` -/
def XbcState.nodeGetData (st : XbcState) (node : XbcNode) : Option String :=
  let offset := node.dataOffset
  if offset >= st.dataSize then
    none
  else
    some (st.getStringAt offset)

/-- `xbc_node_get_data` returning offset -/
def XbcState.nodeGetDataOffset (node : XbcNode) : Nat :=
  node.dataOffset

/-- `xbc_node_get_parent` -/
def XbcState.nodeGetParent (st : XbcState) (node : XbcNode) : Option Nat :=
  if node.parent == XBC_NODE_MAX then
    none
  else if node.parent < st.nodes.size then
    some node.parent
  else
    none

/-- `xbc_node_get_child` -/
def XbcState.nodeGetChild (st : XbcState) (node : XbcNode) : Option Nat :=
  if node.child != 0 && node.child < st.nodes.size then
    some node.child
  else
    none

/-- `xbc_node_get_next` -/
def XbcState.nodeGetNext (st : XbcState) (node : XbcNode) : Option Nat :=
  if node.next != 0 && node.next < st.nodes.size then
    some node.next
  else
    none

/-- `xbc_node_get_subkey` -/
def XbcState.nodeGetSubkey (st : XbcState) (node : XbcNode) : Option Nat :=
  match st.nodeGetChild node with
  | none => none
  | some cidx =>
    if h : cidx < st.nodes.size then
      let child := st.nodes[cidx]
      if child.isValue then
        st.nodeGetNext child
      else
        some cidx
    else
      none

/-- `xbc_node_is_leaf` -/
def XbcState.nodeIsLeaf (st : XbcState) (node : XbcNode) : Bool :=
  node.isKey &&
  match st.nodeGetChild node with
  | none => true
  | some cidx =>
    if h : cidx < st.nodes.size then
      st.nodes[cidx].isValue
    else
      true

end Bootconfig
