import ContinuousFlexibility.Radial.CentralCompactColumn
import ContinuousFlexibility.Radial.CentralColumnInverse

/-!
# The physical central inverse with an actual compact column

An ordinary radial integral against the central kernel is the only
nonorthogonality assumption. Its relation to the Hilbert kernel pairing
is proved with the actual density and the original kernel normalization.
The inverse is an isometric conjugate of `centralColumnInverse`; its graph
is the pre-existing physical distributional equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

private theorem compactColumn_integral_positive_eq (g u : ℝ → ℝ)
    (hp : tsupport g ⊆ Ioi 0) :
    (∫ r in Ioi 0, g r * u r) = ∫ r : ℝ, g r * u r := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hzero : g r = 0 := image_eq_zero_of_notMem_tsupport (fun h => hr (hp h))
  change g r * u r = 0
  rw [hzero, zero_mul]

private theorem compactColumn_ordinary_absolutelyContinuous {scale : ℝ}
    (hscale : 0 < scale) :
    volume.restrict (Ioi (0 : ℝ)) ≪ centralRadialSpectralMeasure scale := by
  unfold centralRadialSpectralMeasure
  apply withDensity_absolutelyContinuous' (centralRadialVarpi_aemeasurable scale)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (ENNReal.ofReal_pos.mpr (centralRadialVarpi_pos hscale hr)).ne'

/-- Ordinary dr row pairing after the actual central Hilbert transform. -/
theorem centralCompactColumn_row_transport {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (u : CentralRadialHilbert scale) :
    ⟪centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp),
      centralRadialHilbertEquiv hscale u⟫_ℝ = ∫ r : ℝ, g r * u r := by
  rw [(centralRadialHilbertEquiv hscale).inner_map_map,
    centralCompactColumn_row_pairing hscale hg hc hp,
    compactColumn_integral_positive_eq g u hp]

/-- The physical kernel is φ / sqrt scale; its transformed vector retains
the original Gaussian normalization. -/
theorem centralCompactColumn_auxiliaryKernel_pairing {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    ⟪centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp),
      centralAuxiliaryKernelVector⟫_ℝ =
      (∫ r : ℝ, g r * centralKernelHeight r) / sqrt scale := by
  rw [← centralAuxiliaryKernel_transform hscale,
    (centralRadialHilbertEquiv hscale).inner_map_map,
    centralCompactColumn_row_pairing hscale hg hc hp]
  have ha : ((centralAuxiliaryKernel hscale : CentralRadialHilbert scale) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioi 0)] centralAuxiliaryKernelFunction scale := by
    unfold centralAuxiliaryKernel
    exact (compactColumn_ordinary_absolutelyContinuous hscale).ae_eq
      (centralAuxiliaryKernelFunction_memLp hscale).coeFn_toLp
  calc
    (∫ r in Ioi 0, g r * centralAuxiliaryKernel hscale r) =
        ∫ r in Ioi 0, (g r * centralKernelHeight r) / sqrt scale := by
      apply integral_congr_ae
      filter_upwards [ha] with r hr
      change g r * centralAuxiliaryKernel hscale r =
        (g r * centralKernelHeight r) / sqrt scale
      rw [hr, centralAuxiliaryKernelFunction]
      ring
    _ = (∫ r in Ioi 0, g r * centralKernelHeight r) / sqrt scale :=
      integral_div _ _
    _ = (∫ r : ℝ, g r * centralKernelHeight r) / sqrt scale := by
      rw [compactColumn_integral_positive_eq g centralKernelHeight hp]

/-- The exact normalization factor relating the ordinary pairing to the
kernel vector of the actual closed differential graph. -/
theorem centralCompactColumn_kernel_pairing {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    centralAuxiliaryKernelScale *
      ⟪centralRadialKernelVector,
        centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp)⟫_ℝ =
      (∫ r : ℝ, g r * centralKernelHeight r) / sqrt scale := by
  have hh := centralCompactColumn_auxiliaryKernel_pairing hscale hg hc hp
  rw [centralAuxiliaryKernelVector, real_inner_smul_right,
    real_inner_comm _ centralRadialKernelVector] at hh
  exact hh

theorem centralCompactColumn_kernel_pairing_ne_zero {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0) :
    ⟪centralRadialKernelVector,
      centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp)⟫_ℝ ≠ 0 := by
  intro hz
  have hh := centralCompactColumn_kernel_pairing hscale hg hc hp
  rw [hz, mul_zero] at hh
  exact div_ne_zero hpair (sqrt_pos.mpr hscale).ne' hh.symm

/-- The actual distributional block with positive Hilbert column g / varpi
and ordinary radial row. -/
def CentralCompactColumnEquation {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ) : Prop :=
  CentralRadialDistributionEquation scale 2 u
      (F - c • centralCompactColumn hscale hg hc hp) ∧
    (∫ r : ℝ, g r * u r) = t

theorem centralCompactColumnEquation_iff {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ) :
    CentralCompactColumnEquation hscale hg hc hp F t u c ↔
      SimpleKernelBorderGraph (centralRadialClosedGraph 2)
        (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))
        (centralRadialHilbertEquiv hscale u, c) (centralRadialHilbertEquiv hscale F, t) := by
  unfold CentralCompactColumnEquation SimpleKernelBorderGraph
  rw [centralRadialDistributionEquation_iff_graph hscale, map_sub, map_smul,
    ← centralCompactColumn_row_transport hscale hg hc hp]

/-- Isometric transport of the genuine central column inverse. -/
def centralCompactColumnInverse {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    (CentralRadialHilbert scale × ℝ) →L[ℝ] (CentralRadialHilbert scale × ℝ) :=
  (centralAuxiliaryPairEquiv hscale).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((centralColumnInverse
      (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))).comp
        (centralAuxiliaryPairEquiv hscale).toContinuousLinearEquiv.toContinuousLinearMap)

theorem centralCompactColumnInverse_apply {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (p : CentralRadialHilbert scale × ℝ) :
    centralCompactColumnInverse hscale hg hc hp p =
      (centralAuxiliaryPairEquiv hscale).symm
        (centralColumnInverse
          (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))
          (centralAuxiliaryPairEquiv hscale p)) := rfl

theorem centralCompactColumnInverse_transform {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (p : CentralRadialHilbert scale × ℝ) :
    centralAuxiliaryPairEquiv hscale (centralCompactColumnInverse hscale hg hc hp p) =
      centralColumnInverse
        (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))
        (centralAuxiliaryPairEquiv hscale p) := by
  rw [centralCompactColumnInverse_apply, LinearIsometryEquiv.apply_symm_apply]

private theorem compactColumn_pairEquiv_apply {scale : ℝ} (hscale : 0 < scale)
    (p : CentralRadialHilbert scale × ℝ) :
    centralAuxiliaryPairEquiv hscale p = (centralRadialHilbertEquiv hscale p.1, p.2) := by
  rcases p with ⟨u, c⟩
  exact centralAuxiliaryPairEquiv_apply hscale u c

theorem centralCompactColumnInverse_solves {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0)
    (F : CentralRadialHilbert scale) (t : ℝ) :
    CentralCompactColumnEquation hscale hg hc hp F t
      (centralCompactColumnInverse hscale hg hc hp (F, t)).1
      (centralCompactColumnInverse hscale hg hc hp (F, t)).2 := by
  apply (centralCompactColumnEquation_iff hscale hg hc hp F t _ _).mpr
  have hs := centralColumnInverse_solves _
    (centralCompactColumn_kernel_pairing_ne_zero hscale hg hc hp hpair)
    (centralRadialHilbertEquiv hscale F, t)
  have ht := centralCompactColumnInverse_transform hscale hg hc hp (F, t)
  rw [compactColumn_pairEquiv_apply, centralAuxiliaryPairEquiv_apply] at ht
  rw [← ht] at hs
  exact hs

theorem centralCompactColumnInverse_unique {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ)
    (hu : CentralCompactColumnEquation hscale hg hc hp F t u c) :
    centralCompactColumnInverse hscale hg hc hp (F, t) = (u, c) := by
  apply (centralAuxiliaryPairEquiv hscale).injective
  rw [centralCompactColumnInverse_transform, centralAuxiliaryPairEquiv_apply,
    centralAuxiliaryPairEquiv_apply]
  exact centralColumnInverse_unique _
    (centralCompactColumn_kernel_pairing_ne_zero hscale hg hc hp hpair) _ _
    ((centralCompactColumnEquation_iff hscale hg hc hp F t u c).mp hu)

theorem centralCompactColumnInverse_norm_le {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    ‖centralCompactColumnInverse hscale hg hc hp‖ ≤
      ‖centralColumnInverse
        (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro p
  calc
    ‖centralCompactColumnInverse hscale hg hc hp p‖ =
        ‖centralColumnInverse
          (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))
          (centralAuxiliaryPairEquiv hscale p)‖ := by
      rw [← (centralAuxiliaryPairEquiv hscale).norm_map,
        centralCompactColumnInverse_transform]
    _ ≤ _ := by
      simpa only [(centralAuxiliaryPairEquiv hscale).norm_map] using
        (centralColumnInverse
          (centralRadialHilbertEquiv hscale (centralCompactColumn hscale hg hc hp))).le_opNorm
          (centralAuxiliaryPairEquiv hscale p)

/-- A bounded linear two-sided inverse under the actual ordinary-radial
nonorthogonality condition. -/
theorem exists_centralCompactColumnInverse {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∃ G : (CentralRadialHilbert scale × ℝ) →L[ℝ] (CentralRadialHilbert scale × ℝ),
        ‖G‖ ≤ C ∧
        (∀ F t, CentralCompactColumnEquation hscale hg hc hp F t (G (F, t)).1 (G (F, t)).2) ∧
        (∀ F t u c, CentralCompactColumnEquation hscale hg hc hp F t u c → G (F, t) = (u, c)) := by
  refine ⟨‖centralCompactColumnInverse hscale hg hc hp‖ + 1, by positivity,
    centralCompactColumnInverse hscale hg hc hp, ?_,
    centralCompactColumnInverse_solves hscale hg hc hp hpair,
    centralCompactColumnInverse_unique hscale hg hc hp hpair⟩
  exact le_add_of_nonneg_right (by norm_num)

end ContinuousFlexibility.Radial
