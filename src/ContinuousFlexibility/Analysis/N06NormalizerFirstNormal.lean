module

public import ContinuousFlexibility.Analysis.N06NormalizerWeights
public import ContinuousFlexibility.Analysis.N06WeakAngularLeibniz

/-!
# The original weak first normal derivative under a normalizer change

The correction direction has its first normal derivative from the old
N05 estimate at the same material weight and input angular order. The
new normal field is the corresponding linear combination in the actual
volume space. Linearity is proved using the original canonical test
pairings, without differentiating L2 representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

/-- The last clause of N05, retaining the original canonical tests. -/
def N06CanonicalFirstNormalBound (V : VolumeModelData S K)
    (J : CanonicalSequence S K → CanonicalUnknown S K)
    (loss t : ℝ) (s : ℕ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ F : V.level (3 / 4 : ℝ) t (s + 1),
    ∃ W : V.level (3 / 4 : ℝ) (t - loss) s,
      (∀ m φ, CanonicalTest S K m φ →
        (∫ p, V.forget (3 / 4 : ℝ) (t - loss) s W m p * φ p
          ∂canonicalMeasure S K m) =
        -(∫ p, (J (V.forget (3 / 4 : ℝ) t (s + 1) F)).1 m p *
          mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧
      ‖W‖ ≤ C₀ * ‖F‖

theorem n06_normalizer_first_normal_pairing
    {γ t : ℝ} {s : ℕ} (U v : CanonicalUnknown S K)
    (W Wv : V.level γ t s)
    (hW : ∀ m φ, CanonicalTest S K m φ →
      (∫ p, V.forget γ t s W m p * φ p ∂canonicalMeasure S K m) =
        -(∫ p, U.1 m p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m))
    (hWv : ∀ m φ, CanonicalTest S K m φ →
      (∫ p, V.forget γ t s Wv m p * φ p ∂canonicalMeasure S K m) =
        -(∫ p, v.1 m p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) :
    ∀ m φ, CanonicalTest S K m φ →
      (∫ p, V.forget γ t s (W + U.2.2.2 • Wv) m p * φ p
        ∂canonicalMeasure S K m) =
      -(∫ p, (n06NormalizerUnknownShear (n06NormalizerLambda S K) v U).1 m p *
        mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
  intro m φ hφ
  let P : CanonicalL2 S K m →ₗ[ℝ] ℝ := n06CanonicalPairing φ hφ.1.continuous
  let Q : CanonicalL2 S K m →ₗ[ℝ] ℝ :=
    n06CanonicalPairing (mixedDerivative 1 0 φ) (contDiff_mixedDerivative hφ.1 1 0).continuous
  have hw : P (V.forget γ t s W m) = -Q (U.1 m) := hW m φ hφ
  have hv : P (V.forget γ t s Wv m) = -Q (v.1 m) := hWv m φ hφ
  have hf : V.forget γ t s (W + U.2.2.2 • Wv) m =
      V.forget γ t s W m + U.2.2.2 • V.forget γ t s Wv m := by
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have hu : (n06NormalizerUnknownShear (n06NormalizerLambda S K) v U).1 m =
      U.1 m + U.2.2.2 • v.1 m := by
    have he := congrFun (n06NormalizerUnknownShear_height v U) m
    exact he
  change P (V.forget γ t s (W + U.2.2.2 • Wv) m) =
    -Q ((n06NormalizerUnknownShear (n06NormalizerLambda S K) v U).1 m)
  rw [hf, hu, map_add, map_smul, map_add, map_smul, hw, hv]
  simp only [smul_eq_mul]
  ring

/-- The extra normal field is fixed at the requested level, while its
scalar coefficient is bounded by the original central height estimate
at input order s+1. -/
theorem n06Normalizer_first_normal_bound
    {J : CanonicalSequence S K → CanonicalUnknown S K}
    {d : CanonicalSequence S K} {v : CanonicalUnknown S K}
    {loss t : ℝ} {s : ℕ}
    (hd : VolumeMember S K V (3 / 4 : ℝ) t (s + 1) d) (hv : J d = v)
    (hheight : N06CanonicalInverseBound V J loss (3 / 4 : ℝ) t (s + 1))
    (hnormal : N06CanonicalFirstNormalBound V J loss t s) :
    N06CanonicalFirstNormalBound V
      (fun F => n06NormalizerUnknownShear (n06NormalizerLambda S K) v (J F)) loss t s := by
  obtain ⟨C₀, hC₀, hb⟩ := hnormal
  obtain ⟨C₁, hC₁, hh⟩ := hheight
  obtain ⟨D₀, hD₀⟩ := hd
  obtain ⟨Wv, hWv, _⟩ := hb D₀
  have hsource : J (V.forget (3 / 4 : ℝ) t (s + 1) D₀) = v :=
    (congrArg J hD₀).trans hv
  have hWv' : ∀ m φ, CanonicalTest S K m φ →
      (∫ p, V.forget (3 / 4 : ℝ) (t - loss) s Wv m p * φ p
        ∂canonicalMeasure S K m) =
      -(∫ p, v.1 m p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
    intro m φ hφ
    have h := hWv m φ hφ
    rw [hsource] at h
    exact h
  refine ⟨C₀ + C₁ * ‖Wv‖,
    add_pos_of_pos_of_nonneg hC₀ (mul_nonneg hC₁.le (norm_nonneg _)), ?_⟩
  intro F
  obtain ⟨W, hW, hnorm⟩ := hb F
  obtain ⟨H, _, hH⟩ := hh F
  let U : CanonicalUnknown S K := J (V.forget (3 / 4 : ℝ) t (s + 1) F)
  have hscalar : |U.2.2.2| ≤ C₁ * ‖F‖ :=
    (n06_normalizer_lambda_le_scalars U).trans
      ((le_add_of_nonneg_left (norm_nonneg H)).trans hH)
  refine ⟨W + U.2.2.2 • Wv,
    n06_normalizer_first_normal_pairing U v W Wv hW hWv', ?_⟩
  calc
    ‖W + U.2.2.2 • Wv‖ ≤ ‖W‖ + |U.2.2.2| * ‖Wv‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le W (U.2.2.2 • Wv)
    _ ≤ C₀ * ‖F‖ + (C₁ * ‖F‖) * ‖Wv‖ :=
      add_le_add hnorm (mul_le_mul_of_nonneg_right hscalar (norm_nonneg _))
    _ = (C₀ + C₁ * ‖Wv‖) * ‖F‖ := by ring

theorem n06NormalizerDomain_first_normal
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (hd : ∀ γ t : ℝ, ∀ s : ℕ,
      VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2)) :
    ∀ t : ℝ, ∀ s : ℕ,
      N06CanonicalFirstNormalBound (n06NormalizerVolume V ψ)
        (n06NormalizerDomain B ψ v hv).globalInverse
        (n06NormalizerDomain B ψ v hv).lossMaterial t s := by
  intro t s
  change N06CanonicalFirstNormalBound V
    (fun F => n06NormalizerUnknownShear (n06NormalizerLambda S K) v.val.1 (B.globalInverse F))
    B.lossMaterial t s
  exact n06Normalizer_first_normal_bound (hd (3 / 4 : ℝ) t (s + 1))
    (n06N05_globalInverse_graph_source h05 v)
    (h05.2.2.2.2.2.2.2.2.2.2.2.2.1 t (s + 1))
    (h05.2.2.2.2.2.2.2.2.2.2.2.2.2 t s)

end ContinuousFlexibility.Statements
