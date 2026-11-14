module

public import ContinuousFlexibility.Analysis.N01PlateauEnergy
public import ContinuousFlexibility.Analysis.PhysicalGradeEnergy

/-!
# Summable envelopes for actual localized height directions

The envelope includes all levels up to the requested order. It therefore
controls the supplied projective grading of any realization of the
localized field, and its sum is a genuine finite physical energy.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

def physicalPlateauEnergy (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (γ : ℝ) (s : ℕ) (f : PolarPoint → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val
    (radialPlateauLocalization D T (C.left m) (C.right m) f)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.physicalPlateauEnergy_tsum_lt_top
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (s : ℕ) :
    (∑' m : ℕ, physicalPlateauEnergy D T C γ s f m) < ⊤ := by
  classical
  have hlevel (i : ℕ) :
      (∑' m : ℕ, physicalLevelEnergy T γ i
        (radialPlateauLocalization D T (C.left m) (C.right m) f)) < ⊤ := by
    have heq : (∑' m : ℕ, physicalLevelEnergy T γ i
        (radialPlateauLocalization D T (C.left m) (C.right m) f)) =
        ∑ j : JetIndex i, ∑' m : ℕ,
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
            (radialPlateauLocalization D T (C.left m) (C.right m) f))
            2 materialCylinderMeasure ^ 2 := by
      simpa only [physicalLevelEnergy, tsum_fintype] using
        ENNReal.tsum_comm (f := fun m (j : JetIndex i) =>
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
            (radialPlateauLocalization D T (C.left m) (C.right m) f))
            2 materialCylinderMeasure ^ 2)
    rw [heq]
    apply ENNReal.sum_lt_top.mpr
    intro j hj
    exact hN.controlPlateau_cutoff_jet_energy_tsum_lt_top hT hf _ _ _
  have heq : (∑' m : ℕ, physicalPlateauEnergy D T C γ s f m) =
      ∑ i : Fin (s + 1), ∑' m : ℕ, physicalLevelEnergy T γ i.val
        (radialPlateauLocalization D T (C.left m) (C.right m) f) := by
    simpa only [physicalPlateauEnergy, tsum_fintype] using
      ENNReal.tsum_comm (f := fun m (i : Fin (s + 1)) =>
        physicalLevelEnergy T γ i.val
          (radialPlateauLocalization D T (C.left m) (C.right m) f))
  rw [heq]
  exact ENNReal.sum_lt_top.mpr (fun i hi => hlevel i.val)

theorem sobolevModel_localized_grading_le_plateauEnergy
    {γ : ℝ} {H : SobolevModelData} (hH : IsSobolevModel D T γ H)
    (u v : H.Space) (s m : ℕ)
    (hv : H.decode v = radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)) :
    H.grading s v ≤ Real.sqrt (physicalPlateauEnergy D T C γ s (H.decode u) m).toReal := by
  have h := sobolevModel_grading_le_sqrt_energy_sum hH v s
  simpa only [hv, physicalPlateauEnergy] using h

/-- The decoder realizes a complete family of actual localized inputs.
Each is locally identical on its component and has a summable envelope
for every projective grading level. -/
theorem N01Properties.exists_height_plateau_localizations
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {γ : ℝ} {H : SobolevModelData} (hH : IsSobolevModel D T γ H) (u : H.Space) :
    ∃ v : ℕ → H.Space,
      (∀ m, H.decode (v m) =
        radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)) ∧
      (∀ m t, t ∈ Ioo (C.left m) (C.right m) → ∀ θ : ℝ,
        H.decode (v m) =ᶠ[𝓝 (t, θ)] H.decode u) ∧
      (∀ s : ℕ, (∑' m : ℕ, physicalPlateauEnergy D T C γ s (H.decode u) m) < ⊤ ∧
        ∀ m, H.grading s (v m) ≤
          Real.sqrt (physicalPlateauEnergy D T C γ s (H.decode u) m).toReal) := by
  have hc : controlGeometryConditions D S C := hN.2.2.2.1
  have hu := hH.2.2.2.1 u
  have hm (m : ℕ) := hH.2.2.2.2.1
    (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u))
    (radialPlateauLocalization_member hT hu (hc.1 m).1 (hc.1 m).2.2)
  choose v hv using hm
  refine ⟨v, hv, ?_, ?_⟩
  · intro m t ht θ
    rw [hv m]
    exact radialPlateauLocalization_eq_germ hT (H.decode u) (hc.1 m).1 (hc.1 m).2.2 ht θ
  · intro s
    exact ⟨hN.physicalPlateauEnergy_tsum_lt_top hT hu s,
      fun m => sobolevModel_localized_grading_le_plateauEnergy hH u (v m) s m (hv m)⟩

end ContinuousFlexibility.Statements
