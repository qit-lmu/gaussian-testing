import GaussianTesting

/-!
Reject `sorry` in every project declaration, including private implementation
helpers. Check that the public import covers every library source file as well,
so an unimported file cannot silently escape this audit.

This audit intentionally uses a legacy import: Lean then loads private data
throughout the import closure. A module-system `import all` would only expose
private data from the directly imported module.
-/

private partial def librarySources (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut sources := #[]
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      sources := sources ++ (← librarySources entry.path)
    else if entry.path.extension == some "lean" then
      sources := sources.push entry.path
  return sources

run_elab do
  let env ← Lean.getEnv
  let modules := env.header.moduleNames.map Lean.Name.toString
  for path in ← librarySources "GaussianTesting" do
    let moduleName := (path.withExtension "").toString.replace "/" "."
    unless modules.contains moduleName do
      throwError "Library source is not covered by the public import: {path}"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := modules[index]!
    unless moduleName == "GaussianTesting" || moduleName.startsWith "GaussianTesting." do
      continue
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Lean.Expr.hasSorry then
      throwError "Declaration contains sorry: {name}"
    checked := checked + 1
  if checked == 0 then
    throwError "The sorry audit did not inspect any project declarations"
  Lean.logInfo m!"Checked {checked} project declarations: no sorry."
