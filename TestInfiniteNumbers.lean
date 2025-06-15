import LeanDisco
import LeanDisco.Domains.InfiniteNumbers

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000000

open LeanDisco
open LeanDisco.Domains.InfiniteNumbers

def main : IO Unit := do
  IO.println "Testing InfiniteNumbers Domain!"

#eval runInfiniteNumbersDiscovery 25
