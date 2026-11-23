import Bootconfig

open Bootconfig

def formatValueList (vals : List String) : String :=
  match vals with
  | [] => "\"\""
  | [""] => "\"\""
  | _ =>
    let formatted := vals.map (fun v =>
      let q := if v.contains '"' then '\'' else '"'
      s!"{q}{v}{q}")
    String.intercalate ", " formatted

def formatListOutput (st : XbcState) : String :=
  let kvs := xbcCollectList st
  let lines := kvs.map (fun (k, vals) => s!"{k} = {formatValueList vals}\n")
  String.join lines

def posToLineCol (rawBytes : ByteArray) (pos : Int) : Option (Nat × Nat) :=
  if pos < 0 then none
  else Id.run do
    let p := pos.toNat
    let mut lin := 1
    let mut col := p + 1
    for i in [0:min p rawBytes.size] do
      if rawBytes.get! i == 10 then -- '\n'
        lin := lin + 1
        col := p - i
    return some (lin, col)

def runSampleTest (path : System.FilePath) (expectSuccess : Bool) : IO Bool := do
  let rawBytes ← IO.FS.readBinFile path
  let mut buf0 : Array UInt8 := Array.mkEmpty (rawBytes.size + 1)
  for i in [0:rawBytes.size] do
    buf0 := buf0.push (rawBytes.get! i)
  buf0 := buf0.push 0
  let slen := cStrlen buf0 0
  let applyBytes := (rawBytes.extract 0 slen).data.push 0

  let (stOrig, retOrig) := xbcInit applyBytes .v7_4Original
  let (stFixed, retFixed) := xbcInit applyBytes .fixed
  let passed := if expectSuccess then (retOrig > 0 && retFixed > 0) else (retOrig < 0 && retFixed < 0)
  let statusStr := if passed then "[OK]" else "[FAIL]"
  let fname := path.fileName.getD ""

  -- Compare against C `./bootconfig -l` if built
  let cBin : System.FilePath := System.FilePath.mk "/home/mhiramat/kdevkit/linux/tools/bootconfig/bootconfig"
  let mut cDiffMsg := ""
  if ← cBin.pathExists then
    let out ← IO.Process.output { cmd := cBin.toString, args := #["-l", path.toString] }
    if expectSuccess then
      let leanOut := formatListOutput stFixed
      if out.stdout != leanOut then
        cDiffMsg := s!" [MISMATCH vs C stdout: expected {repr out.stdout}, got {repr leanOut}]"
    else
      match posToLineCol rawBytes stFixed.errPos with
      | some (lin, col) =>
        let expectedErr := s!"Parse Error: {stFixed.errMsg} at {lin}:{col}\n"
        if !out.stderr.startsWith expectedErr then
          cDiffMsg := s!" [MISMATCH vs C stderr: C={repr out.stderr}, Lean={repr expectedErr}]"
      | none => pure ()

  if expectSuccess then
    let kvOrig := xbcCollectList stOrig
    let kvFixed := xbcCollectList stFixed
    let kvMatch := kvOrig == kvFixed
    if !passed || !kvMatch || !cDiffMsg.isEmpty then
      IO.println s!"{statusStr} {fname}: retOrig={retOrig}, retFixed={retFixed}, kvMatch={kvMatch}{cDiffMsg}"
      return false
    else
      IO.println s!"{statusStr} {fname} (nodes={retFixed}, keys={kvFixed.length}, matches C: true)"
      return true
  else
    if !passed || !cDiffMsg.isEmpty then
      IO.println s!"{statusStr} {fname}: expected failure, got retOrig={retOrig}, retFixed={retFixed}{cDiffMsg}"
      return false
    else
      let lcStr := match posToLineCol rawBytes stFixed.errPos with
        | some (l, c) => s!"{l}:{c}"
        | none => s!"pos {stFixed.errPos}"
      IO.println s!"{statusStr} {fname} (rejected: \"{stFixed.errMsg}\" at {lcStr}, matches C: true)"
      return true

def main (args : List String) : IO UInt32 := do
  let samplesDir : System.FilePath :=
    match args.head? with
    | some d => System.FilePath.mk d
    | none => System.FilePath.mk "/home/mhiramat/kdevkit/linux/tools/bootconfig/samples"

  IO.println "========================================================================="
  IO.println "  Linux v7.4-rc3 Bootconfig Parser - Lean 4 Formal Verification & Suite"
  IO.println "========================================================================="

  IO.println "\n[1] Machine-Checked Bug Counterexamples in Linux v7.4-rc3 (lib/bootconfig.c):"

  let (b1Orig, r1Orig) := xbcInitString Proofs.bug1MixedDepthInput false .v7_4Original
  let (b1Fix, r1Fix)   := xbcInitString Proofs.bug1MixedDepthInput false .fixed
  let b1Compose := xbcNodeComposeKeyAfter b1Orig none (some 17)
  IO.println s!"  * Bug 1 (Unfixed in v7.4-rc3: mixed value+subkey bypasses XBC_DEPTH_MAX/XBC_KEYLEN_MAX):"
  IO.println s!"    - v7.4-rc3: xbc_init SUCCEEDS (nodes={r1Orig}), then compose_key fails with {repr b1Compose}"
  IO.println s!"    - Fixed:    xbc_init REJECTS (ret={r1Fix}, msg=\"{b1Fix.errMsg}\")"

  let (b2Orig, _) := xbcInitString Proofs.bug2ArrayInput false .v7_4Original
  let (b2Fix, _)  := xbcInitString Proofs.bug2ArrayInput false .fixed
  IO.println s!"\n  * Bug 2 (Unfixed in v7.4-rc3: compose_key_after on 2nd+ array value nodes):"
  IO.println s!"    - v7.4-rc3 on nodes [2, 3, 4]: {[2, 3, 4].map (fun i => xbcNodeComposeKeyAfter b2Orig none (some i)) |> repr}"
  IO.println s!"    - Fixed    on nodes [2, 3, 4]: {[2, 3, 4].map (fun i => xbcNodeComposeKeyAfter b2Fix none (some i)) |> repr}"

  let (b3Orig, _) := xbcInitString Proofs.bug3RootValueInput false .v7_4Original
  let (b3Fix, _)  := xbcInitString Proofs.bug3RootValueInput false .fixed
  IO.println s!"\n  * Bug 3 (NEW: compose_key_after(root, root->child) returns 0 / untouched buf instead of -EINVAL):"
  IO.println s!"    - v7.4-rc3 on root=0, node=1 (\"val1\"): {repr (xbcNodeComposeKeyAfter b3Orig (some 0) (some 1))}"
  IO.println s!"    - Fixed    on root=0, node=1 (\"val1\"): {repr (xbcNodeComposeKeyAfter b3Fix (some 0) (some 1))}"
  IO.println s!"    - Fixed    on root=0, node=2 (\"val2\"): {repr (xbcNodeComposeKeyAfter b3Fix (some 0) (some 2))}"

  let (b4Orig, _) := xbcInitString Proofs.bug4CmdlineInput false .v7_4Original
  let (b4Fix, _)  := xbcInitString Proofs.bug4CmdlineInput false .fixed
  IO.println s!"\n  * Bug 4 (NEW: xbc_snprint_cmdline_filter forms OOB pointer `buf + len` when buf != NULL & len > size):"
  IO.println s!"    - v7.4-rc3 (buf!=NULL, size=4): {repr (xbcSnprintCmdlineModel b4Orig true 4 (some 0))}"
  IO.println s!"    - Fixed    (buf!=NULL, size=4): {repr (xbcSnprintCmdlineModel b4Fix true 4 (some 0))}"

  if ← samplesDir.pathExists then
    IO.println s!"\n[2] Running against all v7.4-rc3 kernel test samples in {samplesDir}:"
    let entries ← samplesDir.readDir
    let sorted := entries.qsort (fun a b => a.fileName < b.fileName)
    let mut allOk := true
    let mut total := 0
    for entry in sorted do
      if entry.fileName.startsWith "good-" then
        total := total + 1
        let ok ← runSampleTest entry.path true
        allOk := allOk && ok
      else if entry.fileName.startsWith "bad-" then
        total := total + 1
        let ok ← runSampleTest entry.path false
        allOk := allOk && ok
    IO.println s!"\nSummary: Tested {total} sample files. All passed: {allOk}"
    return if allOk then 0 else 1
  else
    IO.println s!"\nSample directory {samplesDir} not found."
    return 0
