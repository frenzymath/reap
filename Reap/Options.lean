module

public meta import Lean.Data.Options

public meta section

register_option reap.ps_endpoint : String :=
  { defValue := "https://console.siflow.cn/siflow/auriga/skyinfer/ytwang/retrieve-premises-1/retrieve_premises"
    group := "tacticgenerator"
    descr := "Endpoint for the premise selection service." }

register_option reap.llm_endpoint : String :=
  { defValue := "https://console.siflow.cn/siflow/auriga/skyinfer/ytwang/awesome-reaper-1/v1"
    group := "tacticgenerator"
    descr := "Endpoint for the LLM service." }

register_option reap.llm_api_key : String :=
  { defValue := "awesome-reaper"
    group := "tacticgenerator"
    descr := "API key for the LLM service." }

register_option reap.num_samples : Nat :=
  { defValue := 10
    group := "tacticgenerator"
    descr := "Number of samples to generate." }

register_option reap.num_premises : Nat :=
  { defValue := 16
    group := "tacticgenerator"
    descr := "Number of queries to the premise selection service." }

register_option reap.max_tokens : Nat :=
  { defValue := 1024
    group := "tacticgenerator"
    descr := "Maximum number of tokens in the response." }

register_option reap.model : String :=
  { defValue := "awesome-reaper"
    group := "tacticgenerator"
    descr := "Model to use for the LLM." }

register_option reap.temperature : Nat :=
  { defValue := 99
    group := "tacticgenerator"
    descr := "Temperature for the LLM (In percentage)." }

register_option reap.max_goals : Nat :=
  { defValue := 64
    group := "tacticgenerator"
    descr := "Max number of nodes in aesop tree search" }
