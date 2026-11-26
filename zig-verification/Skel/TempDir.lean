/-! The temporary directories of the test suites. `IO.FS.createTempDir` makes the parent directory with an atomic
system call (`mkdtemp`): no two calls, in one process or in several processes, get the same path, and a path that
exists is never given. The tag names the directory inside it, so a left directory shows which check made it. -/

namespace Skel

/-- A new empty directory `<new temporary directory>/skel-<tag>`. -/
def tempDir (tag : String) : IO System.FilePath := do
  let dir := (← IO.FS.createTempDir) / s!"skel-{tag}"
  IO.FS.createDir dir
  return dir

end Skel
