import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# DTQC Basic Definitions
Core definitions for Discrete Time Quasicrystal (DTQC) research.
-/

namespace DTQC

/-- A periodic signal with period τ -/
def PeriodicSignal (τ : ℝ) : ℝ → ℝ :=
  fun t => Real.sin (2 * Real.pi * t / τ)

/-- A quasiperiodic signal with two incommensurate periods -/
structure QuasiperiodicSignal (τ₁ τ₂ : ℝ) where
  amplitude₁ : ℝ
  amplitude₂ : ℝ
  h_positive₁ : amplitude₁ > 0
  h_positive₂ : amplitude₂ > 0

/-- Evaluate a quasiperiodic signal at time t -/
def QuasiperiodicSignal.eval {τ₁ τ₂ : ℝ} (signal : QuasiperiodicSignal τ₁ τ₂) (t : ℝ) : ℝ :=
  signal.amplitude₁ * Real.sin (2 * Real.pi * t / τ₁) +
  signal.amplitude₂ * Real.sin (2 * Real.pi * t / τ₂)

/-- Beat period for two interfering frequencies -/
def beat_period (τ₁ τ₂ : ℝ) : ℝ :=
  |τ₁ * τ₂ / (τ₂ - τ₁)|

/-- Solar (circadian) period in hours -/
def solar_period : ℝ := 24.0

/-- Lunar (tidal) period in hours -/
def lunar_period : ℝ := 24.84

/-- Solar-lunar beat period (synodic month approximation) -/
def solar_lunar_beat : ℝ := beat_period solar_period lunar_period

/-- The golden ratio -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

end DTQC
