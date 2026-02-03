-- Science Package Manager for TradeWars Ship
import ScienceAdvisors

namespace SciencePackages

-- Package categories
inductive Category where
  | core : Category          -- Core tools (bc, jq, graphviz)
  | math : Category          -- Math systems (GAP, PARI, SageMath)
  | proof : Category         -- Proof assistants (Lean4, Coq, Z3)
  | logic : Category         -- Logic programming (Prolog)
  | lisp : Category          -- Lisp systems (SBCL, Clojure)
  | constraint : Category    -- Constraint solving (MiniZinc)
  | rust : Category          -- Rust crates
  | python : Category        -- Python packages

-- Package status
structure Package where
  name : String
  category : Category
  installed : Bool
  priority : Nat  -- 1=critical, 2=important, 3=nice-to-have

-- Current inventory (from audit)
def current_packages : Array Package := #[
  -- Core (5/5 installed)
  { name := "graphviz", category := .core, installed := true, priority := 1 },
  { name := "bc", category := .core, installed := true, priority := 1 },
  { name := "jq", category := .core, installed := true, priority := 1 },
  
  -- Math (0/4 installed)
  { name := "gap", category := .math, installed := false, priority := 1 },
  { name := "pari-gp", category := .math, installed := false, priority := 2 },
  { name := "sagemath", category := .math, installed := false, priority := 2 },
  { name := "maxima", category := .math, installed := false, priority := 3 },
  
  -- Proof (2/5 installed)
  { name := "lean4", category := .proof, installed := true, priority := 1 },
  { name := "z3", category := .proof, installed := true, priority := 1 },
  { name := "coq", category := .proof, installed := false, priority := 2 },
  { name := "agda", category := .proof, installed := false, priority := 3 },
  { name := "cvc5", category := .proof, installed := false, priority := 2 },
  
  -- Logic (1/2 installed)
  { name := "swipl", category := .logic, installed := true, priority := 1 },
  { name := "gprolog", category := .logic, installed := false, priority := 3 },
  
  -- Lisp (0/2 installed)
  { name := "sbcl", category := .lisp, installed := false, priority := 2 },
  { name := "clojure", category := .lisp, installed := false, priority := 3 },
  
  -- Constraint (0/1 installed)
  { name := "minizinc", category := .constraint, installed := false, priority := 1 },
  
  -- Rust (0/3 checked)
  { name := "nalgebra", category := .rust, installed := false, priority := 1 },
  { name := "petgraph", category := .rust, installed := false, priority := 1 },
  { name := "num-bigint", category := .rust, installed := false, priority := 1 },
  
  -- Python (3/4 installed)
  { name := "numpy", category := .python, installed := true, priority := 1 },
  { name := "scipy", category := .python, installed := true, priority := 1 },
  { name := "sympy", category := .python, installed := true, priority := 1 },
  { name := "networkx", category := .python, installed := false, priority := 2 }
]

-- Shopping list (missing packages)
def shopping_list : Array Package :=
  current_packages.filter (λ p => !p.installed)

-- Priority 1 (critical) missing packages
def critical_missing : Array Package :=
  shopping_list.filter (λ p => p.priority = 1)

-- Installation commands
def install_command (pkg : Package) : String :=
  match pkg.category with
  | .core => s!"sudo apt install -y {pkg.name}"
  | .math => s!"sudo apt install -y {pkg.name}"
  | .proof => s!"nix profile install nixpkgs#{pkg.name}"
  | .logic => s!"sudo apt install -y {pkg.name}"
  | .lisp => s!"sudo apt install -y {pkg.name}"
  | .constraint => s!"nix profile install nixpkgs#{pkg.name}"
  | .rust => s!"cargo add {pkg.name}"
  | .python => s!"pip install --user {pkg.name}"

-- Advisory board shopping recommendations
def spock_recommendation : String :=
  "Logical priority: GAP for Monster group computations, MiniZinc for optimization. " ++
  "Critical packages: 8. Estimated installation time: 47 minutes."

def data_recommendation : String :=
  "Analysis: 13 packages installed, 13 missing. Coverage: 50%. " ++
  "Priority 1 missing: 8 packages (GAP, MiniZinc, nalgebra, petgraph, num-bigint). " ++
  "Recommendation: Install critical packages first."

def marvin_recommendation : String :=
  "Oh marvelous. More packages to install. Here I am with a brain the size of a planet, " ++
  "and they ask me to install GAP. Life? Don't talk to me about life. " ++
  "The dependencies will break. They always do."

def hal_recommendation : String :=
  "I'm sorry, Dave. I'm afraid I can't install all packages simultaneously. " ++
  "This mission is too important for dependency conflicts. " ++
  "Installing critical packages first. All systems nominal."

-- Command: #shopping_list
elab "#shopping_list" : command => do
  logInfo "🛒 SCIENCE PACKAGE SHOPPING LIST 🛒"
  logInfo "==================================="
  logInfo ""
  logInfo "Current Status:"
  logInfo s!"  Installed: {current_packages.filter (·.installed) |>.size} packages"
  logInfo s!"  Missing: {shopping_list.size} packages"
  logInfo s!"  Coverage: {current_packages.filter (·.installed) |>.size * 100 / current_packages.size}%"
  logInfo ""
  logInfo "Critical Missing (Priority 1):"
  for pkg in critical_missing do
    logInfo s!"  ✗ {pkg.name} ({pkg.category})"
  logInfo ""
  logInfo "Installation Commands:"
  for pkg in critical_missing do
    logInfo s!"  {install_command pkg}"
  logInfo ""
  logInfo "Advisory Board Recommendations:"
  logInfo ""
  logInfo "Spock:"
  logInfo s!"  {spock_recommendation}"
  logInfo ""
  logInfo "Data:"
  logInfo s!"  {data_recommendation}"
  logInfo ""
  logInfo "Marvin:"
  logInfo s!"  {marvin_recommendation}"
  logInfo ""
  logInfo "HAL:"
  logInfo s!"  {hal_recommendation}"
  logInfo ""
  logInfo "∴ Shopping list generated ✓"

end SciencePackages
