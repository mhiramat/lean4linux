import Bootconfig.Types
import Bootconfig.Lexer
import Bootconfig.Parser
import Bootconfig.Query

namespace Bootconfig.Proofs

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (by intro hc; injection hc; contradiction)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (by rw [h]) else isFalse (by intro hc; injection hc; contradiction)
  | .ok _, .error _ => isFalse (by intro hc; cases hc)
  | .error _, .ok _ => isFalse (by intro hc; cases hc)

/-!
# Formal Verification & Bug Proofs for Linux v7.4-rc3 Bootconfig (`lib/bootconfig.c`)

This module proves key invariants of the Bootconfig parser (synchronized with
Linux v7.4-rc3, commit `381b391bfaa3`) and provides machine-checked counterexample
theorems for the 4 bugs found in `v7.4-rc3`:
1. `xbc_verify_tree()` skips subkeys of valued keys (bypasses `XBC_DEPTH_MAX` / `XBC_KEYLEN_MAX`).
2. `xbc_node_compose_key_after()` corrupts key strings when passed 2nd+ array value nodes.
3. `xbc_node_compose_key_after(root, root->child)` returns `0` (empty string, uninitialized `buf` in C!)
   instead of `-EINVAL` when passed a value node directly owned by `root`.
4. `xbc_snprint_cmdline_filter()` forms out-of-bounds pointers (`buf + len` with `len > size`)
   when `buf != NULL` and the rendered string exceeds `size`.
-/

/-! ## 1. Node Flag, Capacity & Brace Stack Invariants -/

theorem xbcInitNode_key_correct (offset : Nat) (h : offset < XBC_DATA_MAX) :
    ∃ node, xbcInitNode offset 0 = some node ∧
      node.isKey = true ∧
      node.isValue = false ∧
      node.dataOffset = offset := by
  refine ⟨{ data := offset, child := 0, next := 0, parent := 0 }, ?_, ?_, ?_, ?_⟩
  · simp [xbcInitNode, h]
  · simp [XbcNode.isKey, XbcNode.isValue, XbcValBit, XBC_DATA_MAX] at *
    omega
  · simp [XbcNode.isValue, XbcValBit, XBC_DATA_MAX] at *
    omega
  · simp [XbcNode.dataOffset, XbcValBit, XBC_DATA_MAX] at *
    omega

theorem xbcInitNode_val_correct (offset : Nat) (h : offset < XBC_DATA_MAX) :
    ∃ node, xbcInitNode offset XbcValBit = some node ∧
      node.isValue = true ∧
      node.isKey = false ∧
      node.dataOffset = offset := by
  refine ⟨{ data := offset + XbcValBit, child := 0, next := 0, parent := 0 }, ?_, ?_, ?_, ?_⟩
  · simp [xbcInitNode, h]
  · simp [XbcNode.isValue, XbcValBit]
  · simp [XbcNode.isKey, XbcNode.isValue, XbcValBit]
  · simp [XbcNode.dataOffset, XbcValBit, XBC_DATA_MAX] at *
    omega

theorem xbcInitNode_rejects_overflow (offset flag : Nat) (h : offset >= XBC_DATA_MAX) :
    xbcInitNode offset flag = none := by
  unfold xbcInitNode
  simp [h]

theorem xbcAddNode_size_bound (st : XbcState) (data flag : Nat)
    (hBound : st.nodes.size ≤ XBC_NODE_MAX) :
    (xbcAddNode st data flag).1.nodes.size ≤ XBC_NODE_MAX := by
  unfold xbcAddNode
  by_cases hEq : st.nodes.size == XBC_NODE_MAX
  · simp [hEq, hBound]
  · simp [hEq]
    cases xbcInitNode data flag with
    | none => exact hBound
    | some node =>
      simp [Array.size_push]
      have hNe : st.nodes.size ≠ XBC_NODE_MAX := by
        intro hContra
        apply hEq
        exact beq_iff_eq.mpr hContra
      omega

theorem xbcInit_rejects_invalid_size (rawBytes : Array UInt8) (mode : ParserMode)
    (hInvalid : rawBytes.size > XBC_DATA_MAX ∨ rawBytes.size = 0) :
    (xbcInit rawBytes mode).2 = ERANGE ∧
    (xbcInit rawBytes mode).1.errPos = -1 := by
  unfold xbcInit
  rcases hInvalid with hBig | hZero
  · have hCond : (rawBytes.size > XBC_DATA_MAX || rawBytes.size == 0) = true := by simp [hBig]
    simp [hCond]
  · have hCond : (rawBytes.size > XBC_DATA_MAX || rawBytes.size == 0) = true := by simp [hZero]
    simp [hCond]

/--
Theorem: In v7.4-rc3, `xbcOpenBraceCore` checks `braceIndex >= XBC_DEPTH_MAX` BEFORE pushing,
so on success `0 < st'.braceIndex ≤ XBC_DEPTH_MAX` (allowing up to 16 nested braces safely).
-/
theorem xbcOpenBraceCore_success_invariant (st : XbcState) (p : Nat)
    (hSuccess : (xbcOpenBraceCore st p).2 = 0) :
    let st' := (xbcOpenBraceCore st p).1
    0 < st'.braceIndex ∧
    st'.braceIndex ≤ XBC_DEPTH_MAX ∧
    st'.braceIndex = st.braceIndex + 1 := by
  unfold xbcOpenBraceCore at hSuccess ⊢
  by_cases hGe : st.braceIndex >= XBC_DEPTH_MAX
  · simp [hGe, xbcParseError, EINVAL] at hSuccess
  · simp [hGe]
    omega

theorem xbcCloseBraceCore_underflow_fails (st : XbcState) (p : Nat)
    (hZero : st.braceIndex = 0) :
    (xbcCloseBraceCore st p).2 = EINVAL ∧
    (xbcCloseBraceCore st p).1.errMsg = "Unexpected closing brace" := by
  unfold xbcCloseBraceCore
  simp [hZero, xbcParseError]

/-! ## 2. Verification of Upstream v7.4-rc3 Fixes -/

/--
In Linux v7.4-rc3, `open_brace[brace_index - 1]` is already fixed upstream,
so `bad-tree.bconf` now accurately reports the unclosed outer `tree` at offset 23 (2:1).
-/
def badTreeSampleInput : String :=
  "# brace is not closing\ntree {\n  node {\n    value = 1\n}\n"

theorem v7_4_unclosed_brace_already_fixed :
    (xbcInitString badTreeSampleInput false .v7_4Original).2 = EINVAL ∧
    (xbcInitString badTreeSampleInput false .v7_4Original).1.errMsg = "Brace is not closed" ∧
    (xbcInitString badTreeSampleInput false .v7_4Original).1.errPos = 23 := by
  decide

/--
In Linux v7.4-rc3 (commit `cab697164b47`), keys of depth 16 (`XBC_DEPTH_MAX`) are allowed
by both `xbc_verify_tree()` and `xbc_node_compose_key_after()`.
-/
def maxDepth16Input : String :=
  "k1.k2.k3.k4.k5.k6.k7.k8.k9.k10.k11.k12.k13.k14.k15.k16 = v\n"

theorem v7_4_max_depth_16_compose_succeeds :
    (xbcInitString maxDepth16Input false .v7_4Original).2 = 17 ∧
    xbcNodeComposeKeyAfter (xbcInitString maxDepth16Input false .v7_4Original).1 none (some 15) =
      .ok "k1.k2.k3.k4.k5.k6.k7.k8.k9.k10.k11.k12.k13.k14.k15.k16" := by
  decide

/-! ## 3. Machine-Checked Proofs of the 4 Bugs in Linux v7.4-rc3 -/

/-! ### Bug 1 (Unfixed in v7.4-rc3): `xbc_verify_tree()` skips subkeys of valued keys -/

def bug1MixedDepthInput : String :=
  "k1 = v1\nk1.k2.k3.k4.k5.k6.k7.k8.k9.k10.k11.k12.k13.k14.k15.k16.k17 = v2\n"

theorem bug1_v7_4_mixed_kv_bypasses_depth_limit :
    (xbcInitString bug1MixedDepthInput false .v7_4Original).2 = 19 ∧
    xbcNodeComposeKeyAfter (xbcInitString bug1MixedDepthInput false .v7_4Original).1 none (some 17) =
      .error ERANGE ∧
    (xbcInitString bug1MixedDepthInput false .fixed).2 = EINVAL ∧
    (xbcInitString bug1MixedDepthInput false .fixed).1.errMsg = "Too many key words" := by
  decide

/-! ### Bug 2 (Unfixed in v7.4-rc3): `xbc_node_compose_key_after()` corrupts 2nd+ array value keys -/

def bug2ArrayInput : String := "foo.bar = \"val1\", \"val2\", \"val3\"\n"

theorem bug2_v7_4_array_value_compose_key_corruption :
    (xbcInitString bug2ArrayInput false .v7_4Original).2 = 5 ∧
    (xbcInitString bug2ArrayInput false .fixed).2 = 5 ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .v7_4Original).1 none (some 2) = .ok "foo.bar" ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .v7_4Original).1 none (some 3) = .ok "foo.bar.val1" ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .v7_4Original).1 none (some 4) = .ok "foo.bar.val1.val2" ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .fixed).1 none (some 2) = .ok "foo.bar" ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .fixed).1 none (some 3) = .ok "foo.bar" ∧
    xbcNodeComposeKeyAfter (xbcInitString bug2ArrayInput false .fixed).1 none (some 4) = .ok "foo.bar" := by
  decide

/-!
### Bug 3 (Newly discovered in v7.4-rc3): `xbc_node_compose_key_after(root, root->child)` returns 0 (empty / uninitialized `buf`) instead of `-EINVAL`

When `root` is a key node (e.g. `foo`, index 0) and `node` is a value node owned directly by `root`
(e.g. `"val1"`, index 1, or `"val2"`, index 2):
- In `v7_4Original`:
  `if (!node || node == root)` is checked BEFORE climbing value parents, so `node` (index 1) != `root` (index 0).
  Then `node` climbs to `root` (index 0), the `while (node && node != root)` loop runs 0 times (`depth = 0`),
  the `while (--depth >= 0)` loop runs 0 times (NEVER writing to `buf`, not even a NUL terminator!),
  and the function returns `total = 0` (success!) instead of `-EINVAL`!
- In `fixed`:
  Re-checking `if (!node || node == root) return -EINVAL;` AFTER climbing value parents properly
  returns `-EINVAL` for any value node directly owned by `root`.
-/

def bug3RootValueInput : String := "foo = \"val1\", \"val2\"\n"

theorem bug3_v7_4_compose_key_after_root_value_returns_empty_not_einval :
    (xbcInitString bug3RootValueInput false .v7_4Original).2 = 3 ∧
    -- Passing root = foo (0), node = "val1" (1): v7.4 returns .ok "" (total=0, buf untouched!)
    xbcNodeComposeKeyAfter (xbcInitString bug3RootValueInput false .v7_4Original).1 (some 0) (some 1) = .ok "" ∧
    -- In fixed mode, both "val1" (1) and "val2" (2) climb to root (0) and return EINVAL (-22)
    xbcNodeComposeKeyAfter (xbcInitString bug3RootValueInput false .fixed).1 (some 0) (some 1) = .error EINVAL ∧
    xbcNodeComposeKeyAfter (xbcInitString bug3RootValueInput false .fixed).1 (some 0) (some 2) = .error EINVAL := by
  decide

/-!
### Bug 4 (Newly discovered in v7.4-rc3): Out-of-bounds pointer arithmetic UB in `xbc_snprint_cmdline_filter()`

In `lib/bootconfig.c` (lines 590 & 604):
```c
ret = snprintf(buf ? buf + len : NULL, rest(len, size), ...);
```
When `buf != NULL` and the rendered cmdline exceeds `size` (e.g. `size = 8` for `"a=1 b=2 "` which is 8 bytes,
or `size = 4` for `"a=1 b=2 "`):
- After `"a=1 "` (4 bytes), `len = 4 == size`.
- After `"b=2 "` (4 bytes), `len = 8 > size` (4).
- On the 3rd key `"c=3 "`, `buf ? buf + len : NULL` evaluates `buf + 8`, which is 4 bytes PAST the end of
  the `size = 4` buffer! Forming a pointer past one-past-the-end of an allocation is undefined behavior in C
  (and trips UBSan / pointer-overflow sanitizers), even when the length argument `rest(len, size)` is `0`.
- Using `buf && len < size ? buf + len : NULL` prevents ever forming an out-of-bounds pointer.
-/

def bug4CmdlineInput : String := "kernel.a = 1\nkernel.b = 2\nkernel.c = 3\n"

theorem bug4_v7_4_snprint_cmdline_oob_pointer_ub :
    let (stOrig, _) := xbcInitString bug4CmdlineInput false .v7_4Original
    let (stFix, _)  := xbcInitString bug4CmdlineInput false .fixed
    -- With non-NULL buf of size 4, v7.4-rc3 forms an OOB pointer `buf + 8` on the 3rd key:
    (xbcSnprintCmdlineModel stOrig true 4 (some 0)) =
      .ok { totalLen := 12, rendered := "a=1 b=2 c=3 ", oobPtrFormed := true } ∧
    -- Fixed mode (`buf && len < size ? buf + len : NULL`) never forms an OOB pointer:
    (xbcSnprintCmdlineModel stFix true 4 (some 0)) =
      .ok { totalLen := 12, rendered := "a=1 b=2 c=3 ", oobPtrFormed := false } := by
  decide

end Bootconfig.Proofs
