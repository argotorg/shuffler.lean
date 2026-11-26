import Lean.Data.Json

/-! The reply store of the model rung (`docs/research/class-r-coordinator-deepseek-20261118.md`, section 3): the replies of
the model, keyed by the hash of the prompt. Pure. The file form is JSON lines, one object with the fields `hash`, `prompt`
and `reply` for each entry (`.skel/replies.jsonl`). The text is parsed one time, at the boundary. -/

namespace Skel

/-- The 64-bit FNV-1a hash of the UTF-8 bytes of `s` (offset `0xcbf29ce484222325`, prime `0x100000001b3`). It depends on
the bytes of `s` only, so it is the same in each run, on each platform and with each version of Lean. -/
def hashPrompt (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

/-- The 16 hexadecimal digits of a hash, in lower case. -/
def hashHex (h : UInt64) : String :=
  let ds := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

/-- An entry: a prompt, its reply, and the hash of the prompt. Make it with `ReplyEntry.make`. -/
structure ReplyEntry where (hash : UInt64) (prompt reply : String) deriving DecidableEq, Repr

/-- The entry of a prompt and its reply. -/
def ReplyEntry.make (prompt reply : String) : ReplyEntry :=
  { hash := hashPrompt prompt, prompt := prompt, reply := reply }

/-- The store: at most one entry for each hash. -/
structure ReplyStore where (entries : List ReplyEntry) deriving DecidableEq, Repr

/-- The store with no entry. -/
def ReplyStore.empty : ReplyStore := ⟨[]⟩

/-- The reply of the entry whose hash is the hash of `prompt`. -/
def ReplyStore.lookup (s : ReplyStore) (prompt : String) : Option String :=
  let h := hashPrompt prompt
  (s.entries.find? (·.hash == h)).map (·.reply)

/-- The store with the entry of `prompt` and `reply`, which replaces the entry with the same hash. -/
def ReplyStore.insert (s : ReplyStore) (prompt reply : String) : ReplyStore :=
  let e := ReplyEntry.make prompt reply
  ⟨s.entries.filter (·.hash != e.hash) ++ [e]⟩

/-- The line of an entry: one JSON object, with no newline. -/
private def entryLine (e : ReplyEntry) : String :=
  Lean.Json.compress <| Lean.Json.mkObj
    [("hash", Lean.toJson (hashHex e.hash)), ("prompt", Lean.toJson e.prompt), ("reply", Lean.toJson e.reply)]

/-- The file form of the store: one line for each entry, each line ends with a newline. -/
def ReplyStore.toJsonl (s : ReplyStore) : String := String.join (s.entries.map fun e => entryLine e ++ "\n")

/-- The entry of a line. The line is one JSON object with the string fields `hash`, `prompt` and `reply`, and `hash` is
the hash of `prompt`. -/
private def entryOf (line : String) : Except String ReplyEntry := do
  let j ← Lean.Json.parse line
  let hash ← j.getObjValAs? String "hash"
  let prompt ← j.getObjValAs? String "prompt"
  let reply ← j.getObjValAs? String "reply"
  if hash != hashHex (hashPrompt prompt) then throw "the hash is not the hash of the prompt"
  pure (ReplyEntry.make prompt reply)

/-- The store of a file text. A line that is not an entry (an empty line in the middle included) is an error that starts
with `line N:`, N counted from 1. The newline at the end of the text is not a line. An entry with the hash of an earlier
entry replaces it. -/
def ReplyStore.parse (text : String) : Except String ReplyStore := do
  let ls := text.splitOn "\n"
  let ls := if ls.getLast? == some "" then ls.dropLast else ls
  let es ← ((List.range ls.length).zip ls).mapM fun (i, l) => (entryOf l).mapError fun e => s!"line {i + 1}: {e}"
  pure (es.foldl (fun s e => s.insert e.prompt e.reply) ReplyStore.empty)

end Skel
