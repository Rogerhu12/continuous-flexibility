import ContinuousFlexibility.Radial.TailHighFormBound
import ContinuousFlexibility.Radial.TailReflectedInverse
import ContinuousFlexibility.Radial.TailMassCells

/-!
# Closing the high-mode estimate in the actual form space

The smooth core is dense in the Hilbert form space by its defining closure.
For a continuous projection preserving that core, the actual zero-mean
conditions give the high-mode estimate on core residuals. Continuity of both
energy coordinates then gives the same estimate on the full form space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def tailGradientCore (T : DeepTailData) (endCut : ℝ) : Set (tailGradientSpace T endCut) :=
  {u | (tailFormBase T endCut u, tailFormGradient T endCut u) ∈ TailEnergyCore T endCut}

/-- The genuine smooth core, with the linear structure induced by the two
actual coordinate maps. -/
def tailGradientCoreSubmodule (T : DeepTailData) (endCut : ℝ) :
    Submodule ℝ (tailGradientSpace T endCut) :=
  (tailEnergyCoreSubmodule T endCut).comap
    ((tailFormBase T endCut).prod (tailFormGradient T endCut)).toLinearMap

theorem mem_tailGradientCoreSubmodule (T : DeepTailData) (endCut : ℝ)
    (u : tailGradientSpace T endCut) :
    u ∈ tailGradientCoreSubmodule T endCut ↔ u ∈ tailGradientCore T endCut := by
  rw [tailGradientCoreSubmodule, Submodule.mem_comap]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply]
  exact mem_tailEnergyCoreSubmodule T endCut _

theorem tailGradientCore_zero (T : DeepTailData) (endCut : ℝ) :
    (0 : tailGradientSpace T endCut) ∈ tailGradientCore T endCut :=
  (mem_tailGradientCoreSubmodule T endCut 0).mp (tailGradientCoreSubmodule T endCut).zero_mem

theorem tailGradientCore_add {T : DeepTailData} {endCut : ℝ}
    {u v : tailGradientSpace T endCut}
    (hu : u ∈ tailGradientCore T endCut) (hv : v ∈ tailGradientCore T endCut) :
    u + v ∈ tailGradientCore T endCut :=
  (mem_tailGradientCoreSubmodule T endCut _).mp
    ((tailGradientCoreSubmodule T endCut).add_mem
      ((mem_tailGradientCoreSubmodule T endCut u).mpr hu)
      ((mem_tailGradientCoreSubmodule T endCut v).mpr hv))

theorem tailGradientCore_smul {T : DeepTailData} {endCut : ℝ}
    {u : tailGradientSpace T endCut} (hu : u ∈ tailGradientCore T endCut) (c : ℝ) :
    c • u ∈ tailGradientCore T endCut :=
  (mem_tailGradientCoreSubmodule T endCut _).mp
    ((tailGradientCoreSubmodule T endCut).smul_mem c
      ((mem_tailGradientCoreSubmodule T endCut u).mpr hu))

theorem tailGradientCore_sum {ι : Type*} {T : DeepTailData} {endCut : ℝ}
    (s : Finset ι) (u : ι → tailGradientSpace T endCut)
    (hu : ∀ i ∈ s, u i ∈ tailGradientCore T endCut) :
    (∑ i ∈ s, u i) ∈ tailGradientCore T endCut :=
  (mem_tailGradientCoreSubmodule T endCut _).mp
    ((tailGradientCoreSubmodule T endCut).sum_mem (fun i hi =>
      (mem_tailGradientCoreSubmodule T endCut (u i)).mpr (hu i hi)))

theorem mem_tailGradientCore_iff (T : DeepTailData) (endCut : ℝ)
    (u : tailGradientSpace T endCut) :
    u ∈ tailGradientCore T endCut ↔
      WithLp.ofLp (u : GradientHilbert (DeepTailL2 T)) ∈ TailEnergyCore T endCut := by
  have he : (tailFormBase T endCut u, tailFormGradient T endCut u) =
      WithLp.ofLp (u : GradientHilbert (DeepTailL2 T)) := by
    rw [tailFormBase_apply, tailFormGradient_apply]
    exact Prod.ext (WithLp.ofLp_fst _).symm (WithLp.ofLp_snd _).symm
  change _ ∈ TailEnergyCore T endCut ↔ _
  rw [he]

theorem tailGradientCore_sub {T : DeepTailData} {endCut : ℝ}
    {u v : tailGradientSpace T endCut}
    (hu : u ∈ tailGradientCore T endCut) (hv : v ∈ tailGradientCore T endCut) :
    u - v ∈ tailGradientCore T endCut :=
  (mem_tailGradientCoreSubmodule T endCut _).mp
    ((tailGradientCoreSubmodule T endCut).sub_mem
      ((mem_tailGradientCoreSubmodule T endCut u).mpr hu)
      ((mem_tailGradientCoreSubmodule T endCut v).mpr hv))

theorem tailGradientCore_dense (T : DeepTailData) (endCut : ℝ) :
    Dense (tailGradientCore T endCut) := by
  apply Subtype.dense_iff.mpr
  have hi : (Subtype.val '' tailGradientCore T endCut : Set (GradientHilbert (DeepTailL2 T))) =
      WithLp.ofLp ⁻¹' TailEnergyCore T endCut := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (mem_tailGradientCore_iff T endCut u).mp hu
    · intro hq
      have hmem : q ∈ tailGradientSpace T endCut :=
        (mem_tailGradientSpace T endCut q).mpr (subset_closure hq)
      exact ⟨⟨q, hmem⟩, (mem_tailGradientCore_iff T endCut ⟨q, hmem⟩).mpr hq, rfl⟩
  rw [hi]
  have hc : closure (WithLp.ofLp ⁻¹' TailEnergyCore T endCut :
      Set (GradientHilbert (DeepTailL2 T))) = WithLp.ofLp ⁻¹' TailFormLift T endCut := by
    have h := (WithLp.prodContinuousLinearEquiv 2 ℝ (DeepTailL2 T)
      (DeepTailL2 T)).toHomeomorph.preimage_closure (TailEnergyCore T endCut)
    have hfun :
        ⇑(WithLp.prodContinuousLinearEquiv 2 ℝ (DeepTailL2 T) (DeepTailL2 T)).toHomeomorph =
          WithLp.ofLp := by
      funext q
      simp only [ContinuousLinearEquiv.coe_toHomeomorph,
        WithLp.prodContinuousLinearEquiv_apply]
    rw [hfun] at h
    simpa only [TailFormLift] using h.symm
  rw [hc]
  exact fun q hq => (mem_tailGradientSpace T endCut q).mp hq

theorem tail_core_high_norm_bound_of_set_means {T : DeepTailData}
    (hT : DeepTailHypotheses T) {endCut : ℝ} (hcut : endCut ≤ T.endpoint)
    {u : tailGradientSpace T endCut} (hu : u ∈ tailGradientCore T endCut)
    (hmean : ∀ n, tailFirstMassIndex T ≤ n →
      (∫ x in tailMassCell T n, (tailFormBase T endCut u) x ∂deepTailMeasure T) = 0) :
    T.Λ * ‖tailFormBase T endCut u‖ ^ 2 ≤
      5 * T.η * ‖tailFormGradient T endCut u‖ ^ 2 := by
  obtain ⟨φ, hφ, hcφ, hsφ, hub, hug⟩ := hu
  apply tail_core_high_norm_bound hT hφ hcφ
    (hsφ.trans (fun x hx => ⟨hx.1, hx.2.trans_le hcut⟩)) hub hug
  intro n hn
  calc
    (∫ x in T.node n..T.massEnd n, T.p x * φ x) =
        ∫ x in tailMassCell T n, T.p x * φ x := by
      rw [intervalIntegral.integral_of_le (deepTail_node_lt_massEnd hT n).le,
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in tailMassCell T n, φ x ∂deepTailMeasure T :=
      (tail_setIntegral_density hT (tailMassCell_measurable T n)
        (tailMassCell_subset hT n) φ).symm
    _ = ∫ x in tailMassCell T n, (tailFormBase T endCut u) x ∂deepTailMeasure T := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hub.symm
    _ = 0 := hmean n hn

/-- A core-preserving bounded projection with the stated actual weighted
mean cancellation has the same high-mode estimate on every form vector.
The construction of such a projection is a separate obligation. -/
theorem tail_closed_high_norm_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {endCut : ℝ} (hcut : endCut ≤ T.endpoint)
    (P : tailGradientSpace T endCut →L[ℝ] tailGradientSpace T endCut)
    (hcore : ∀ u, u ∈ tailGradientCore T endCut → P u ∈ tailGradientCore T endCut)
    (hmean : ∀ (u : tailGradientSpace T endCut) n, tailFirstMassIndex T ≤ n →
      (∫ x in tailMassCell T n, (tailFormBase T endCut (u - P u)) x ∂deepTailMeasure T) = 0)
    (u : tailGradientSpace T endCut) :
    T.Λ * ‖tailFormBase T endCut (u - P u)‖ ^ 2 ≤
      5 * T.η * ‖tailFormGradient T endCut (u - P u)‖ ^ 2 := by
  have hres : Continuous (fun v : tailGradientSpace T endCut => v - P v) :=
    continuous_id.sub P.continuous
  have hc : IsClosed {v : tailGradientSpace T endCut |
      T.Λ * ‖tailFormBase T endCut (v - P v)‖ ^ 2 ≤
        5 * T.η * ‖tailFormGradient T endCut (v - P v)‖ ^ 2} :=
    isClosed_le
      (continuous_const.mul (((tailFormBase T endCut).continuous.comp hres).norm.pow 2))
      (continuous_const.mul (((tailFormGradient T endCut).continuous.comp hres).norm.pow 2))
  have hd : tailGradientCore T endCut ⊆ {v : tailGradientSpace T endCut |
      T.Λ * ‖tailFormBase T endCut (v - P v)‖ ^ 2 ≤
        5 * T.η * ‖tailFormGradient T endCut (v - P v)‖ ^ 2} := by
    intro v hv
    exact tail_core_high_norm_bound_of_set_means hT hcut
      (tailGradientCore_sub hv (hcore v hv)) (hmean v)
  exact (closure_minimal hd hc) (tailGradientCore_dense T endCut u)

end ContinuousFlexibility.Radial
