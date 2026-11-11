import ContinuousFlexibility.Analysis.PhysicalJetLinearity
import ContinuousFlexibility.Analysis.PhysicalTopology
import ContinuousFlexibility.Analysis.CylinderUniformNorm
import ContinuousFlexibility.Analysis.ScalarDerivativeLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Genuine physical-space derivatives from weighted Taylor remainders

Each actual material jet has a scalar Taylor estimate dominated by an
L² function. The finite collection of jet norms controls each projective
level. Consequently the full difference quotient converges in the
supplied height space and in its compatibility kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

local instance physicalTaylorDifferentiationRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem eLpNorm_le_real_scalar_envelope
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {A : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hA : 0 ≤ A)
    (hb : ∀ x, |f x| ≤ A * g x) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (A * (eLpNorm g 2 μ).toReal) := by
  have hmono : eLpNorm f 2 μ ≤ eLpNorm (A • g) 2 μ :=
    eLpNorm_mono_real hf.aestronglyMeasurable
      (fun x => by simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hb x)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA] at hmono
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
  exact hmono

theorem physicalNorm_le_of_jet_envelopes
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (s : ℕ) (G : JetIndex s → PolarPoint → ℝ)
    (hG : ∀ j, MemLp (G j) 2 materialCylinderMeasure) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j p,
      |weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f p| ≤ A * G j p) :
    physicalNorm T γ s f ≤
      (Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
        ∑ j, (eLpNorm (G j) 2 materialCylinderMeasure).toReal) * A := by
  classical
  let B : ℝ := ∑ j, (eLpNorm (G j) 2 materialCylinderMeasure).toReal
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hjet (j : JetIndex s) :
      eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
        2 materialCylinderMeasure ≤ ENNReal.ofReal (A * B) := by
    have hnorm := eLpNorm_le_real_scalar_envelope
      (hf.2.2.2.2 (j.val 0).val (j.val 1).val (j.val 2).val) (hG j) hA (hb j)
    have hj : (eLpNorm (G j) 2 materialCylinderMeasure).toReal ≤ B :=
      Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    exact hnorm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hj hA))
  exact (physicalNorm_le_of_common_jet_bound (mul_nonneg hA hB) hjet).trans_eq (by
    dsimp only [B]
    ring)

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}

theorem height_curve_slope_error_bound
    (hH : IsSobolevModel D T γ H) (hT : IsMaterialData D T)
    (c : ℝ → H.Space) (dc : H.Space) (J₁ J₂ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hfirst : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => weightedPhysicalJet T γ a b d (H.decode (c u)) p)
        (J₁ t a b d p) t)
    (hsecond : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => J₁ u a b d p) (J₂ t a b d p) t)
    (hvalue : ∀ a b d p, J₁ 0 a b d p = weightedPhysicalJet T γ a b d (H.decode dc) p)
    (s : ℕ) (G : JetIndex s → PolarPoint → ℝ)
    (hG : ∀ j, MemLp (G j) 2 materialCylinderMeasure)
    (hGpos : ∀ j p, 0 ≤ G j p)
    (hbound : ∀ t, |t| < δ → ∀ j p,
      |J₂ t (j.val 0).val (j.val 1).val (j.val 2).val p| ≤ G j p)
    {h : ℝ} (hh : |h| < δ) (hne : h ≠ 0) :
    physicalNorm T γ s (H.decode (h⁻¹ • (c h - c 0) - dc)) ≤
      (Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
        ∑ j, (eLpNorm (G j) 2 materialCylinderMeasure).toReal) * |h| := by
  apply physicalNorm_le_of_jet_envelopes
    (hH.2.2.2.1 (h⁻¹ • (c h - c 0) - dc)) s G hG (abs_nonneg h)
  intro j p
  let L := heightWeightedJetLinear hH hT (j.val 0).val (j.val 1).val (j.val 2).val
  have heq : weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
      (H.decode (h⁻¹ • (c h - c 0) - dc)) p =
      h⁻¹ * (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
        (H.decode (c h)) p - weightedPhysicalJet T γ (j.val 0).val (j.val 1).val
          (j.val 2).val (H.decode (c 0)) p) - J₁ 0 (j.val 0).val (j.val 1).val (j.val 2).val p := by
    rw [hvalue]
    change L (h⁻¹ • (c h - c 0) - dc) p = h⁻¹ * (L (c h) p - L (c 0) p) - L dc p
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [heq, mul_comm |h|]
  exact abs_slope_sub_derivative_le_of_second_derivative_bound hδ (hGpos j p)
    (fun t ht => hfirst t ht (j.val 0).val (j.val 1).val (j.val 2).val p)
    (fun t ht => hsecond t ht (j.val 0).val (j.val 1).val (j.val 2).val p)
    (fun t ht => hbound t ht j p) hh hne

theorem height_hasProjectiveCurveDerivAt_of_second_jet_envelopes
    (hH : IsSobolevModel D T γ H) (hT : IsMaterialData D T)
    (c : ℝ → H.Space) (dc : H.Space) (J₁ J₂ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hfirst : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => weightedPhysicalJet T γ a b d (H.decode (c u)) p)
        (J₁ t a b d p) t)
    (hsecond : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => J₁ u a b d p) (J₂ t a b d p) t)
    (hvalue : ∀ a b d p, J₁ 0 a b d p = weightedPhysicalJet T γ a b d (H.decode dc) p)
    (hbound : ∀ a b d, ∃ G : PolarPoint → ℝ,
      MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
        ∀ t, |t| < δ → ∀ p, |J₂ t a b d p| ≤ G p) :
    HasProjectiveCurveDerivAt c dc 0 := by
  classical
  choose G hG hGpos hb using hbound
  apply (height_hasProjectiveCurveDerivAt_iff_physicalNorm hH c dc 0).mpr
  intro s
  let Gs : JetIndex s → PolarPoint → ℝ := fun j =>
    G (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
    ∑ j : JetIndex s, (eLpNorm (Gs j) 2 materialCylinderMeasure).toReal
  have hlim : Tendsto (fun h : ℝ => K * |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ha : Tendsto (fun h : ℝ => |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [abs_zero] using
        (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using ha.const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)) _ hlim
  have hsmall : {h : ℝ | |h| < δ} ∈ 𝓝 (0 : ℝ) := by
    simpa only [Metric.ball, Real.dist_eq, sub_zero] using Metric.ball_mem_nhds (0 : ℝ) hδ
  filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with h hh hne
  have hne' : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  simpa only [zero_add] using height_curve_slope_error_bound hH hT c dc J₁ J₂ hδ
    hfirst hsecond hvalue s Gs (fun j => hG _ _ _) (fun j p => hGpos _ _ _ p)
    (fun t ht j p => hb _ _ _ t ht p) hh hne'

theorem source_hasProjectiveCurveDerivAt_of_second_jet_envelopes
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (c : ℝ → S.Source) (dc : S.Source) (J₁ J₂ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hfirst : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b d
        (physicalSourceDecode S (c u)) p) (J₁ t a b d p) t)
    (hsecond : ∀ t, |t| < δ → ∀ a b d p,
      HasDerivAt (fun u => J₁ u a b d p) (J₂ t a b d p) t)
    (hvalue : ∀ a b d p, J₁ 0 a b d p =
      weightedPhysicalJet T (3 / 4 : ℝ) a b d (physicalSourceDecode S dc) p)
    (hbound : ∀ a b d, ∃ G : PolarPoint → ℝ,
      MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
        ∀ t, |t| < δ → ∀ p, |J₂ t a b d p| ≤ G p) :
    HasProjectiveCurveDerivAt c dc 0 := by
  apply (source_hasProjectiveCurveDerivAt_iff_height c dc 0).mpr
  exact height_hasProjectiveCurveDerivAt_of_second_jet_envelopes (hS.1 (3 / 4 : ℝ)) hT
    (fun t => (c t).val) dc.val J₁ J₂ hδ hfirst hsecond hvalue hbound

end ContinuousFlexibility.Statements
