import DTQC.Basic
import Mathlib.Data.Real.Basic

/-!
# Olfaction-Specific DTQC Definitions
Structures and definitions for olfactory systems with circadian coupling.
-/

namespace DTQC.Olfaction

/-- A circadian oscillator with a natural period -/
structure CircadianSystem where
  natural_period : ℝ
  h_positive : natural_period > 0

/-- Olfactory receptor with circadian modulation -/
structure OlfactoryReceptor where
  baseline_sensitivity : ℝ
  circadian_amplitude : ℝ
  circadian : CircadianSystem
  h_baseline_pos : baseline_sensitivity > 0
  h_amplitude_bound : 0 < circadian_amplitude ∧ circadian_amplitude < 1

/-- Receptor sensitivity at time t with circadian modulation -/
def OlfactoryReceptor.sensitivity (receptor : OlfactoryReceptor) (t : ℝ) : ℝ :=
  receptor.baseline_sensitivity *
  (1 + receptor.circadian_amplitude *
   Real.sin (2 * Real.pi * t / receptor.circadian.natural_period))

/-- Circadian modulation factor (normalized to [0,2]) -/
def OlfactoryReceptor.circadian_modulation (receptor : OlfactoryReceptor) (t : ℝ) : ℝ :=
  1 + receptor.circadian_amplitude *
  Real.sin (2 * Real.pi * t / receptor.circadian.natural_period)

/-- Discrimination accuracy between two odor stimuli (placeholder metric) -/
structure DiscriminationMetric where
  d_prime : ℝ  -- d' (d-prime) from signal detection theory
  h_nonneg : d_prime ≥ 0

/-- DTQC forcing condition: quasiperiodic with solar+lunar periods -/
def dtqc_forcing_condition (τ₁ τ₂ : ℝ) : Prop :=
  τ₁ = DTQC.solar_period ∧ τ₂ = DTQC.lunar_period

end DTQC.Olfaction
