module

public meta import Lean.Data.Options

public meta section

register_option reap.ps_endpoint : String :=
  { defValue := "https://console.siflow.cn/siflow/auriga/skyinfer/ytwang/ps2-1/retrieve_premises"
    descr := "Endpoint for the premise selection service." }

register_option reap.value_endpoint : String :=
  { defValue := "https://siflow-auriga.siflow.cn/siflow/auriga/skyinfer/ytwang/reap-1-7-value/v1"
    descr := "Endpoint for the value service." }

register_option reap.use_value_model : Bool :=
  { defValue := true
    descr := "Whether to use the value model service." }

register_option reap.policy_endpoint : String :=
  { defValue := "https://siflow-auriga.siflow.cn/siflow/auriga/skyinfer/ytwang/reap-1-7b/v1"
    descr := "Endpoint for the LLM service." }

register_option reap.llm_api_key : String :=
  { defValue := "awesome-reaper"
    descr := "API key for the LLM service." }

register_option reap.num_samples : Nat :=
  { defValue := 10
    descr := "Number of samples to generate." }

register_option reap.num_premises : Nat :=
  { defValue := 16
    descr := "Number of queries to the premise selection service." }

register_option reap.max_tokens : Nat :=
  { defValue := 1024
    descr := "Maximum number of tokens in the response." }

register_option reap.model : String :=
  { defValue := "awesome-reaper"
    descr := "Model to use for the LLM." }

register_option reap.temperature : Nat :=
  { defValue := 99
    descr := "Temperature for the LLM (In percentage)." }

register_option reap.max_goals : Nat :=
  { defValue := 64
    descr := "Max number of nodes in tree search" }

register_option reap.max_steps : Nat :=
  { defValue := 64
    descr := "Max number of steps in MCTS tree search"
  }

register_option reap.heartbeats : Nat := {
  defValue := 1000000000
  descr := "Maximum heartbeats per tactic"
}

register_option reap.c_base : Nat :=
  { defValue := 3200
    descr := "MCTS exploration hyper-parameter c_base." }

register_option reap.c_init : Nat :=
  { defValue := 1
    descr := "MCTS exploration hyper-parameter c_init, scaled by 1000." }

register_option reap.visit_discount : Nat :=
  { defValue := 990
    descr := "MCTS value discount multiplier, scaled by 1000. γ in the AlphaProof paper." }

register_option reap.prior_temperature : Nat :=
  { defValue := 200
    descr := "MCTS prior temperature exponent. τ in the AlphaProof paper." }
