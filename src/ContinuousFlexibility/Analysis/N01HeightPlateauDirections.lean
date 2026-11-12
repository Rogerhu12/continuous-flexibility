import ContinuousFlexibility.Analysis.N01FlowGermLocality
import ContinuousFlexibility.Analysis.N01PlateauEnergyEnvelope

/-!
# Actual physical height-pair localizations without a trace term

The trace cutoff is constant on a negative component. Localizing the
decoded Sobolev height alone therefore preserves every characteristic
coefficient there, up to the harmless additive height constant. The
resulting directions have zero trace and a summable physical envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Topology

theorem N01Properties.exists_height_pair_plateau_directions
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (ξ : HeightPair S) :
    ∃ η : ℕ → HeightPair S,
      (∀ m, (η m).2 = 0) ∧
      (∀ m, (S.height (3 / 4 : ℝ)).decode (η m).1 =
        radialPlateauLocalization D T (C.left m) (C.right m)
          ((S.height (3 / 4 : ℝ)).decode ξ.1)) ∧
      (∀ m, ∃ c : ℝ, ∀ t ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
        heightPairField S (η m) (t, θ) = heightPairField S ξ (t, θ) + c) ∧
      (∀ s : ℕ,
        (∑' m : ℕ, physicalPlateauEnergy D T C (3 / 4 : ℝ) s
          ((S.height (3 / 4 : ℝ)).decode ξ.1) m) < ⊤ ∧
        ∀ m, heightPairGrading S s (η m) ≤
          Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) s
            ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal) := by
  obtain ⟨v, hv, hgerm, henergy⟩ :=
    hN.exists_height_plateau_localizations hT (hS.1 (3 / 4 : ℝ)) ξ.1
  have hc : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨fun m => (v m, 0), fun _ => rfl, hv, ?_, ?_⟩
  · intro m
    obtain ⟨c, hcχ⟩ := hS.2.2.1.constant_on_negative_component (hc.2.2.2.1 m)
    refine ⟨-(ξ.2 * c), fun t ht θ => ?_⟩
    have heq := (hgerm m t ht θ).eq_of_nhds
    simp only [heightPairField, zero_mul, add_zero, heq, hcχ t ht]
    ring
  · intro s
    refine ⟨(henergy s).1, fun m => ?_⟩
    change (S.height (3 / 4 : ℝ)).grading s (v m) + ‖(0 : ℝ)‖ ≤ _
    simpa only [norm_zero, add_zero] using (henergy s).2 m

end ContinuousFlexibility.Statements
