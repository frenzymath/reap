module

public meta import Lean.Data.Options

public meta section

register_option reap.ps_endpoint : String :=
  { defValue := "https://console.siflow.cn/siflow/auriga/skyinfer/ytwang/ps2-1"
    descr := "Endpoint for the premise selection service." }

register_option reap.value_endpoint : String :=
  { defValue := "https://siflow-auriga.siflow.cn/siflow/auriga/skyinfer/ytwang/reap-1-7-value"
    descr := "Endpoint for the value service." }

register_option reap.llm_endpoint : String :=
  { defValue := "https://siflow-auriga.siflow.cn/siflow/auriga/skyinfer/ytwang/reap-1-7b"
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
