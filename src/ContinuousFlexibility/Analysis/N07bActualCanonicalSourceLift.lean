module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceLift
public import ContinuousFlexibility.Analysis.N07bCanonicalSourceJets
public import ContinuousFlexibility.Analysis.N07bCanonicalSourceWeakJets
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Lifting the actual physical source into the chosen volume model

The physical decoder gives a globally smooth, even, periodic source.
The actual chart geometry then supplies every local L² jet, reflection,
and weak angular derivative required by the volume graph. Material sample
positivity also follows from the reference and material data.

The sole additional analytic input below is summability of the displayed
actual weighted jet energy. No uniform bound for that energy is claimed,
and no hypothesis is added to the frozen N07b statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The prescribed forget factor is positive at every actual material sample. -/
theorem n07bCanonicalSourceFactor_pos_of_material
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ t : ℝ) (m : ℕ) : 0 < n07bCanonicalSourceFactor T K γ t m := by
  obtain ⟨_, hprofile⟩ := hD
  have hr := materialSample_mem_radialCore hT hprofile.2.1 (K.cell m)
  have hp := hT.2.1 _ hr
  exact mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hp.2.2.2) (-t))
    (Real.rpow_pos_of_pos hp.2.1 γ)

/-- The actual angular derivatives of the actual source conversion. -/
def n07bActualCanonicalAngularJet (K : CanonicalData S) (z : AnnularState S × ℝ)
    (f : S.Source) (m j : ℕ) : PolarPoint → ℝ :=
  mixedDerivative 0 j
    (canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val))

theorem n07bActualCanonicalAngularJet_zero (K : CanonicalData S)
    (z : AnnularState S × ℝ) (f : S.Source) (m : ℕ) :
    n07bActualCanonicalAngularJet K z f m 0 =
      canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  funext p
  simp only [n07bActualCanonicalAngularJet, mixedDerivative, iteratedDeriv_zero, Prod.eta]

theorem n07bActualCanonicalAngularJet_memLp
    (hK : Blueprint.N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (f : S.Source) (m j : ℕ) :
    MemLp (n07bActualCanonicalAngularJet K z f m j) 2 (canonicalMeasure S K m) :=
  n07b_canonicalSource_mixedDerivative_memLp_of_contDiff hK hz hs m
    (physical_height_contDiff_and_flatJets hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      f.val).1 0 j

/-- Raw weighted energy, independent of any choice of L² representative. -/
def n07bActualCanonicalJetEnergy (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (f : S.Source) (γ t : ℝ) (s m : ℕ) : ℝ :=
  ∑ j : Fin (s + 1), (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
    (eLpNorm (n07bActualCanonicalAngularJet K z f m j.val)
      2 (canonicalMeasure S K m)).toReal ^ 2

theorem n07bActualCanonicalJetEnergy_nonneg (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (f : S.Source) (γ t : ℝ) (s m : ℕ) :
    0 ≤ n07bActualCanonicalJetEnergy T K z f γ t s m :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- All local geometric inputs to the chosen canonical lift are proved.
Only the actual global weighted energy summability remains as an input. -/
theorem n07b_exists_actualCanonicalSourceLift
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : Blueprint.N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) (γ t : ℝ) (s : ℕ)
    (hsum : Summable (n07bActualCanonicalJetEnergy T K z f γ t s)) :
    ∃ F : V.level γ t s,
      (∀ m (j : Fin (s + 1)), (F.val m j : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] fun p =>
          (n07bCanonicalSourceFactor T K γ t m)⁻¹ *
            n07bActualCanonicalAngularJet K z f m j.val p) ∧
      (∀ m, (V.forget γ t s F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val)) ∧
      ‖F‖ ^ 2 = ∑' m, n07bActualCanonicalJetEnergy T K z f γ t s m := by
  let f₀ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode f.val
  have hf : ContDiff ℝ ∞ f₀ :=
    (physical_height_contDiff_and_flatJets hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      f.val).1
  have hperiod : Function.Periodic f₀ (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).2.2.1
  let g : ∀ m : ℕ, Fin (s + 1) → PolarPoint → ℝ :=
    fun m j => n07bActualCanonicalAngularJet K z f m j.val
  have hg (m : ℕ) (j : Fin (s + 1)) : MemLp (g m j) 2 (canonicalMeasure S K m) :=
    n07bActualCanonicalAngularJet_memLp hK hz hs hT hS f m j.val
  have hzero (m : ℕ) : g m 0 = canonicalSource S K z m f₀ :=
    n07bActualCanonicalAngularJet_zero K z f m
  have href : ∀ m, (fun p : PolarPoint => g m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m 0 := by
    intro m
    rw [hzero m]
    exact n07b_physicalSource_canonical_reflection_ae hK hz hs hS f m
  have hweak : ∀ m j φ, CanonicalTest S K m φ →
      (∫ p, g m j p * φ p ∂canonicalMeasure S K m) =
        (-1 : ℝ) ^ j.val *
          ∫ p, g m 0 p * mixedDerivative 0 j.val φ p ∂canonicalMeasure S K m := by
    intro m j φ hφ
    rw [hzero m]
    exact n07b_canonicalSource_weakAngular_integral hK hz hs f₀ hperiod m j.val
      (n07b_contDiffOn_canonicalSource hK hz hs m (fun _ _ => hf.contDiffAt))
      (n07b_canonicalSource_memLp hK hz hs m hf.continuous.continuousOn) (hg m j) hφ
  have henergy (m : ℕ) : n07bCanonicalJetEnergy (T := T) hg γ t m =
      n07bActualCanonicalJetEnergy T K z f γ t s m := by
    simp only [n07bCanonicalJetEnergy, n07bCanonicalWeightedJet,
      n07bActualCanonicalJetEnergy, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Lp.norm_toLp, g]
  have hsum' : Summable (n07bCanonicalJetEnergy (T := T) hg γ t) :=
    hsum.congr (fun m => (henergy m).symm)
  let F : V.level γ t s := n07bCanonicalSourceLift hg hV href hweak hsum'
  refine ⟨F, ?_, ?_, ?_⟩
  · intro m j
    have hc : F.val m j = n07bCanonicalWeightedJet (T := T) hg γ t m j :=
      n07bCanonicalSourceLift_coordinate hg hV href hweak hsum' m j
    rw [hc]
    exact n07bCanonicalWeightedJet_ae (T := T) hg γ t m j
  · intro m
    have he := n07bCanonicalSourceLift_forget_ae hg hV href hweak hsum'
      (fun k => (n07bCanonicalSourceFactor_pos_of_material hD hT γ t k).ne') m
    simpa only [hzero m] using he
  · exact (n07bCanonicalSourceLift_norm_sq hg hV href hweak hsum').trans
      (tsum_congr henergy)

end ContinuousFlexibility.Analysis
