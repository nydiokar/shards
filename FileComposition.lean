-- File Composition Analysis: Line→Token Arrows
import Lean

namespace FileComposition

-- Analyze file composition via line→token arrows
structure LineAnalysis where
  line_num : Nat
  line_shard : Nat  -- mod 59
  token_shard : Nat -- mod 47
  token_count : Nat
  shadow : Float

def analyze_line (line : String) (line_num : Nat) : LineAnalysis :=
  let tokens := line.split (· == ' ') |>.filter (· ≠ "")
  let token_count := tokens.length
  let line_hash := line.hash
  let line_shard := line_hash.toUInt64 % 59
  let token_shard := token_count % 47
  
  -- Shadow: distance from pure shard (0,0)
  let line_dist := min line_shard.toNat (59 - line_shard.toNat)
  let token_dist := min token_shard (47 - token_shard)
  let shadow := (line_dist.toFloat / 59.0 + token_dist.toFloat / 47.0) / 2.0
  
  { line_num, line_shard := line_shard.toNat, token_shard, token_count, shadow }

def analyze_file (path : String) : IO (Array LineAnalysis) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  
  let mut analyses := #[]
  for (i, line) in lines.toArray.zipWithIndex do
    analyses := analyses.push (analyze_line line (i + 1))
  
  return analyses

-- Compute file repair cost from line composition
def file_repair_cost (analyses : Array LineAnalysis) : Float :=
  let total_shadow := analyses.foldl (fun acc a => acc + a.shadow) 0.0
  let avg_shadow := total_shadow / analyses.size.toFloat
  let complexity := analyses.size.toFloat
  let eigenvalue := 0.25 + (complexity / 71.0) * (complexity / 71.0)
  avg_shadow * eigenvalue

-- Command: #analyze_composition <file>
elab "#analyze_composition" path:str : command => do
  let file_path := path.getString
  
  let analyses ← Elab.Command.liftIO (analyze_file file_path)
  let repair_cost := file_repair_cost analyses
  
  logInfo s!"File Composition Analysis: {file_path}"
  logInfo s!"  Total lines: {analyses.size}"
  logInfo s!"  Avg shadow: {analyses.foldl (fun acc a => acc + a.shadow) 0.0 / analyses.size.toFloat:.4f}"
  logInfo s!"  Repair cost: {repair_cost:.4f}"
  logInfo s!"\nFirst 10 lines:"
  
  for a in analyses.toList.take 10 do
    logInfo s!"  Line {a.line_num}: shard({a.line_shard},{a.token_shard}) tokens={a.token_count} shadow={a.shadow:.4f}"
  
  logInfo s!"\n∴ File composition analyzed via line→token arrows ✓"

end FileComposition
