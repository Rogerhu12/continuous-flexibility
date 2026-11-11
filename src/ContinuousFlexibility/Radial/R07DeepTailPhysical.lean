import ContinuousFlexibility.Radial.R07DeepTailSharp
import ContinuousFlexibility.Radial.R07DeepTailLocalization

/-!
# Actual physical data satisfying the complete R06 hypotheses
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_deepTail_physical_relation {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    TailPhysicalRelation D (r07DeepTailData T D right j start η K) right j start := by
  refine ⟨rfl, ?_, ?_, r07_deepTail_localization h right j hstart η K,
    r07_deepTail_physical_product h hσ hb right hj hstart h32 η K hclose⟩
  · cases right <;> rfl
  · intro x hx
    exact ⟨r07_physical_radius_core_of_Ico (r07_realization_geometry h)
      (r07_deepTail_entrance_core h right j hstart η K) ⟨hx.1.le, hx.2⟩, rfl⟩

/-- One explicit physical density and one common depth satisfy both complete
R06 predicates for every height sequence and both endpoint orientations. -/
theorem r07_exists_uniform_deepTailPhysical
    (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization T σ (family σ) C ∧ MorseMassResistanceBounds T σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b)
    {j : ℕ} (hj : 2 ≤ j) {η K : ℝ} (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K)
    (minimum : ℕ) :
    ∃ start : ℕ, minimum ≤ start ∧ T.index < start ∧ 32 ≤ start ∧
      ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → ∀ right : Bool,
        let Q := r07DeepTailData T (family σ) right j start η K
        DeepTailHypotheses Q ∧ TailPhysicalRelation (family σ) Q right j start := by
  obtain ⟨start, hmin, hstart, h32, hall⟩ :=
    r07_exists_uniform_deepTailHypotheses T C family hfamily hends hj hη hη1 hK minimum
  refine ⟨start, hmin, hstart, h32, ?_⟩
  intro σ hσ right
  have hQ := hall σ hσ right
  exact ⟨hQ.2, r07_deepTail_physical_relation (hfamily σ hσ).1 hσ (hfamily σ hσ).2
    right hj hstart h32 η K hQ.1⟩

/-- Apply the given R06 theorem to the actual physical densities. The output
is one globally smooth nonzero natural solution at each deep entrance. -/
theorem r07_exists_uniform_deep_naturalTail (hR06 : R06Statement)
    (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization T σ (family σ) C ∧ MorseMassResistanceBounds T σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b)
    {j : ℕ} (hj : 2 ≤ j) (minimum : ℕ) :
    ∃ start : ℕ, minimum ≤ start ∧ T.index < start ∧
      ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → ∀ right : Bool,
        ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
          RadialNaturalTail (family σ) right j
            (if right then r07MassNodeRadius T right start
              else morseChainResistanceEnd T right start) v := by
  obtain ⟨A, η, K, hA, hη, hη1, hK, hoperator, hphysical, hparameter⟩ := hR06
  obtain ⟨start, hmin, hstart, h32, hall⟩ :=
    r07_exists_uniform_deepTailPhysical T C family hfamily hends hj hη hη1 hK minimum
  refine ⟨start, hmin, hstart, ?_⟩
  intro σ hσ right
  have hreal := (hfamily σ hσ).1
  have hQ := hall σ hσ right
  have hacc := r07_realization_accumulating hreal
  have hflat := (hphysical (family σ) (r07DeepTailData T (family σ) right j start η K)
    right j start hacc hQ.1 le_rfl le_rfl hQ.2).1
  have hnat := r07_naturalTail_of_physicalFlat hacc rfl hflat
  have hc : (if right then r07MassNodeRadius T right start
      else morseChainResistanceEnd T right start) ∈ radialCore (family σ) := by
    cases right
    · exact r07_chain_resistanceEnd_core hreal false hstart
    · exact (r07_chain_mass_nodes_core hreal true hstart.le).1
  have hp := (r07_realization_geometry hreal).1.trans hc.1
  simpa only [r07DeepTailData, r07_radius_outwardLog right hp] using hnat

end ContinuousFlexibility.Radial
