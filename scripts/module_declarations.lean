import Lean

/-! Read declarations owned by compiled modules without importing their environments. -/

def main (args : List String) : IO Unit := do
  let [input, output] := args
    | throw <| IO.userError "Expected an input TSV and output JSON path"
  let listing ← IO.FS.readFile input
  let mut fields : List (String × Lean.Json) := []
  for line in listing.splitOn "\n" do
    if line.isEmpty then continue
    let [name, path] := line.splitOn "\t"
      | throw <| IO.userError "Invalid module listing"
    let file : System.FilePath := path
    let mut files := #[file]
    let server := Lean.OLeanLevel.server.adjustFileName file
    if ← server.pathExists then
      files := files.push server
      let privateFile := Lean.OLeanLevel.private.adjustFileName file
      if ← privateFile.pathExists then files := files.push privateFile
    let parts ← Lean.readModuleDataParts files
    let some part := parts[parts.size - 1]?
      | throw <| IO.userError s!"No module data: {path}"
    let declarations := part.1.constants.map fun (info : Lean.ConstantInfo) =>
      let signature := match info with
        | .thmInfo value => Lean.Json.arr #[
            Lean.toJson info.type.hash.toNat,
            Lean.toJson (info.levelParams.map fun (n : Lean.Name) => n.toString),
            Lean.toJson (value.all.map fun (n : Lean.Name) => n.toString)]
        | _ => Lean.Json.null
      (info.name.toString, signature)
    fields := (name, Lean.toJson declarations) :: fields
  IO.FS.writeFile output (Lean.Json.mkObj fields).compress
