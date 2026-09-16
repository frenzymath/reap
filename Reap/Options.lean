module

public meta import Lean.Data.Options

public meta section

structure ReapGenerationConfig where
  /-- Number of samples to generate. -/
  numSamples : Nat := 6
  /-- Number of queries to premise selection service. -/
  numPremises : Nat := 16
  /-- Maximum number of tokens in the response. -/
  maxTokens : Nat := 1024
  /-- Temperature for the LLM. -/
  temperature : Float := 0.99

structure ReapMCTSConfig where
  /-- MCTS exploration hyper-parameter c_base. -/
  cBase : Float := 3200.0
  /-- MCTS exploration hyper-parameter c_init. -/
  cInit : Float := 0.001
  /-- MCTS value discount multiplier, γ in the AlphaProof paper. -/
  visitDiscount : Float := 0.99
  /-- MCTS prior temperature exponent. τ in the AlphaProof paper. -/
  priorTemperature : Float := 50.0
  /-- MCTS progressive sampling c parameter. -/
  progressiveSamplingC : Float := 0.01
  /-- MCTS progressive sampling alpha parameter. -/
  progressiveSamplingAlpha : Float := 0.6

structure ReapTotalLimitsConfig where
  /-- Maximum number of MCTS nodes to explore. -/
  maxGoals : Nat := 64
  /-- Maximum number of MCTS iterations. -/
  maxSteps : Nat := 64

structure ReapStepLimitsConfig where
  /-- Maximum heartbeats per tactic -/
  heartbeats : Nat := 1000000000
  /-- Timeout in milliseconds per tactic -/
  timeout : Nat := 200000

structure ReapResourceLimitsConfig where
  /-- Limits for the whole MCTS search. -/
  total : ReapTotalLimitsConfig := {}
  /-- Limits for each candidate tactic evaluation. -/
  step : ReapStepLimitsConfig := {}

structure ReapConfig where
  /-- Resource limits for the search and tactic evaluation. -/
  limits : ReapResourceLimitsConfig := {}
  /-- Parameters for premise selection and tactic generation. -/
  generation : ReapGenerationConfig := {}
  /-- MCTS hyperparameters. -/
  mcts : ReapMCTSConfig := {}

register_option reap.ps_endpoint : String :=
  { defValue := "<premise_selection_endpoint>"
    descr := "Endpoint for the premise selection service." }

register_option reap.value_endpoint : String :=
  { defValue := "<value_endpoint>"
    descr := "Endpoint for the value service." }

register_option reap.policy_endpoint : String :=
  { defValue := "<policy_endpoint>"
    descr := "Endpoint for the LLM service." }

register_option reap.llm_api_key : String :=
  { defValue := "awesome-reaper"
    descr := "API key for the LLM service." }

register_option reap.model : String :=
  { defValue := "awesome-reaper"
    descr := "Model to use for the LLM." }

register_option reap.wall_clock_log_path : String :=
  { defValue := ""
    descr := "Optional JSONL path for per-action wall-clock records. Empty disables file logging." }

register_option reap.raw_tree_path : String :=
  { defValue := ""
    descr := "Optional JSON path for the final raw MCTS tree. Empty disables file export." }
