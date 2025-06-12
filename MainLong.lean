import LeanDisco

set_option maxHeartbeats 10000000

-- Test the system with mining enabled for richer discovery
#eval LeanDisco.runDiscovery 200 true

def main : IO Unit := do
  IO.println "Hello from LeanDisco!"
