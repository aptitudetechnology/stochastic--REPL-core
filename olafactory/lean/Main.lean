import DTQC.Basic
import DTQC.Olfaction
import DTQC.Theorems.Basic
import DTQC.Theorems.Olfaction

/-!
# DTQC Main Entry Point
Demonstrates the formalization of DTQC principles for olfactory systems.
-/

def main : IO Unit := do
  IO.println "DTQC Formalization Loaded"
  IO.println s!"Solar period: {DTQC.solar_period} hours"
  IO.println s!"Lunar period: {DTQC.lunar_period} hours"
  IO.println s!"Beat period: ~{DTQC.solar_lunar_beat} hours (29.5 days)"
