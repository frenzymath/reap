import Reap.LeanSearch.API

open Lean PremiseSelectionClient

def client : PremiseSelectionClient := {
  apiUrl := "https://console.siflow.cn/siflow/auriga/skyinfer/ytwang/relate-theorem-extern-1/retrieve_premises"
}

def ppp : CoreM Unit := do
  let s ← (client.getResults "cauchy theorem" 3)
  for r in s do
    IO.println r.formal_statement

#eval (client.getResults "cauchy theorem" 3)
#eval (client.getResults "n: Nat |- Even n" 3)
#eval ppp
