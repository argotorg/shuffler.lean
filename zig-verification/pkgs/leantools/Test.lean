import Test.Text
import Test.History
import Test.HoleFeedback
import Test.Pos
import Test.Validate
import Test.Config
import Test.Http
import Test.Chat
import Test.OpenAI
import Test.Responses
import Test.Anthropic
import Test.Prove
import Test.ProveBudget
import Test.ProveConfig
import Test.Tools
import Test.Deny
import Test.Report
import Test.RunMetadata
import Test.Axioms
import Test.Ask
import Lean

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  if args == ["--prove"] then
    return ← Test.run [("Prove", Test.Prove.suite), ("ProveContext", Test.Prove.contextSuite), ("ProveThreshold", Test.Prove.thresholdSuite),
      ("ProveToolset", Test.Prove.toolsetSuite), ("ProveConfig", Test.ProveConfig.suite),
      ("ProveBudget", Test.ProveBudget.suite)]
  if args == ["--holes"] then
    return ← Test.run [("HoleFeedback", Test.HoleFeedback.suite),
      ("HoleFeedbackRuntime", Test.HoleFeedback.runtimeSuite)]
  if args == ["--module-validation"] then
    return ← Test.run [("ValidateModule", Test.Validate.moduleSuite)]
  if args == ["--validation"] then
    return ← Test.run [("Validate", Test.Validate.suite)]
  if args == ["--http-clients"] then
    return ← Test.run [("OpenAI", Test.OpenAI.suite), ("Responses", Test.Responses.suite), ("Anthropic", Test.Anthropic.suite)]
  if args == ["--concurrency"] then
    return ← Test.run [("Config", Test.Config.suite), ("Concurrency", Test.Tools.concurrencySuite)]
  if args == ["--search"] then
    return ← Test.run [("Report", Test.Report.suite), ("DenyPure", Test.Deny.pureSuite), ("Deny", Test.Deny.suite)]
  Test.run [("Anthropic", Test.Anthropic.suite), ("Responses", Test.Responses.suite), ("Validate", Test.Validate.suite), ("Text", Test.Text.suite), ("History", Test.History.suite), ("HoleFeedback", Test.HoleFeedback.suite), ("HoleFeedbackRuntime", Test.HoleFeedback.runtimeSuite), ("Pos", Test.Pos.suite), ("Config", Test.Config.suite), ("Http", Test.Http.suite), ("Chat", Test.Chat.suite), ("OpenAI", Test.OpenAI.suite), ("Prove", Test.Prove.suite), ("ProveContext", Test.Prove.contextSuite), ("ProveThreshold", Test.Prove.thresholdSuite), ("ProveBudget", Test.ProveBudget.suite), ("ProveToolset", Test.Prove.toolsetSuite), ("ProveConfig", Test.ProveConfig.suite), ("Tools", Test.Tools.suite), ("Concurrency", Test.Tools.concurrencySuite), ("DenyPure", Test.Deny.pureSuite), ("Deny", Test.Deny.suite), ("ToolParams", Test.Tools.paramsSuite), ("ToolEdits", Test.Tools.editsSuite), ("Deadline", Test.Tools.deadlineSuite), ("Subprocess", Test.Tools.processSuite), ("Report", Test.Report.suite), ("RunMetadata", Test.RunMetadata.suite), ("AskPure", Test.Ask.pureSuite), ("Ask", Test.Ask.serverSuite), ("AskParallel", Test.Ask.parallelSuite)]
