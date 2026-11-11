import ContinuousFlexibility.Analysis.N05CanonicalMollifiedJets

/-!
# Signed reflection, weak limits, and a radial plateau

Signed reflection averages are continuous on canonical L² and are the
ordinary derivatives of the even average. Actual weak derivative pairs
are preserved under strong limits. A wider explicit radial cutoff is
identically one on the support of the original cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def n05CanonicalSignedProjection (S : PhysicalSpacesData) (K : CanonicalData S)
    (m j : ℕ) : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ (CanonicalL2 S K m) +
    (-1 : ℝ) ^ j • (n05CanonicalReflection S K m).toContinuousLinearMap)

theorem n05CanonicalSignedProjection_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (m j : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalSignedProjection S K m j u =
      (1 / 2 : ℝ) • (u + (-1 : ℝ) ^ j • n05CanonicalReflection S K m u) := by
  simp only [n05CanonicalSignedProjection, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap]

theorem n05CanonicalSignedProjection_zero (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : n05CanonicalSignedProjection S K m 0 = n05CanonicalEvenProjection S K m := by
  simp only [n05CanonicalSignedProjection, pow_zero, one_smul, n05CanonicalEvenProjection]

theorem n05CanonicalSignedProjection_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m j : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalSignedProjection S K m j u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => (1 / 2 : ℝ) * (u p + (-1 : ℝ) ^ j * u (p.1, Real.pi - p.2)) := by
  rw [n05CanonicalSignedProjection_apply]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + (-1 : ℝ) ^ j • n05CanonicalReflection S K m u),
    Lp.coeFn_add u ((-1 : ℝ) ^ j • n05CanonicalReflection S K m u),
    Lp.coeFn_smul ((-1 : ℝ) ^ j) (n05CanonicalReflection S K m u),
    n05CanonicalReflection_ae S K m u] with p hhalf hadd hsign href
  rw [hhalf]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsign]
  simp only [Pi.smul_apply, smul_eq_mul, href]

theorem n05CanonicalSmoothJet_even (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    n05CanonicalSmoothJet S K m (spacesCylinderEvenFunction_contDiff hf) j =
      n05CanonicalSignedProjection S K m j (n05CanonicalSmoothJet S K m hf j) := by
  apply Lp.ext
  have ha := n05CanonicalSmoothJet_ae S K m hf j
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [n05CanonicalSmoothJet_ae S K m (spacesCylinderEvenFunction_contDiff hf) j,
    n05CanonicalSignedProjection_ae S K m j (n05CanonicalSmoothJet S K m hf j), ha, hr]
    with p hp hq ha hr
  change n05CanonicalSmoothJet S K m hf j (p.1, Real.pi - p.2) =
    mixedDerivative 0 j f (p.1, Real.pi - p.2) at hr
  rw [hp, hq, spacesCylinderEvenFunction_mixedDerivative hf, ha, hr]

theorem n05CanonicalSmoothJet_radial_mul (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C) :
    n05CanonicalSmoothJet S K m ((hχ.comp contDiff_fst).mul hf) j =
      n05CanonicalRadialMultiply S K m χ hχ.continuous C hC
        (n05CanonicalSmoothJet S K m hf j) := by
  apply Lp.ext
  filter_upwards [n05CanonicalSmoothJet_ae S K m ((hχ.comp contDiff_fst).mul hf) j,
    n05CanonicalRadialMultiply_ae S K m χ hχ.continuous C hC (n05CanonicalSmoothJet S K m hf j),
    n05CanonicalSmoothJet_ae S K m hf j] with p hp hq hr
  rw [hp, hq, hr, n05CanonicalAngularDerivative_radial_mul]

theorem n05WeakCanonicalAngularDerivative_of_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → CanonicalL2 S K m} {f₀ g₀ : CanonicalL2 S K m}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀))
    (h : ∀ i, WeakCanonicalAngularDerivative S K m (f i) (g i) j) :
    WeakCanonicalAngularDerivative S K m f₀ g₀ j := by
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  let Q := n05CanonicalTestPairing S K m (mixedDerivative 0 j φ)
    (n05CanonicalTest_angular_memLp hφ j)
  have he (i : ι) : P (g i) = (-1 : ℝ) ^ j * Q (f i) := by
    simpa only [P, Q, n05CanonicalTestPairing_apply] using h i φ hφ
  have hl : Tendsto (fun i => P (g i)) l (𝓝 (P g₀)) := P.continuous.tendsto g₀ |>.comp hg
  have hr : Tendsto (fun i => (-1 : ℝ) ^ j * Q (f i))
      l (𝓝 ((-1 : ℝ) ^ j * Q f₀)) :=
    tendsto_const_nhds.mul (Q.continuous.tendsto f₀ |>.comp hf)
  have hlim : P g₀ = (-1 : ℝ) ^ j * Q f₀ :=
    tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun i => (he i).symm)))
  simpa only [P, Q, n05CanonicalTestPairing_apply] using hlim

theorem n05CanonicalCutoffWidth_double (n : ℕ) :
    2 * n05CanonicalCutoffWidth (2 * n + 1) = n05CanonicalCutoffWidth n := by
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hd : (2 : ℝ) * (n : ℝ) + 1 + 1 ≠ 0 := ne_of_gt (by positivity)
  simp only [n05CanonicalCutoffWidth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp [hn, hd] <;> ring

theorem n05CanonicalRadialCutoffFunction_plateau (a b : ℝ) (n : ℕ) {r : ℝ}
    (hr : r ∈ tsupport (n05CanonicalRadialCutoffFunction a b n)) :
    n05CanonicalRadialCutoffFunction a b (2 * n + 1) r = 1 := by
  have hi := n05CanonicalRadialCutoffFunction_tsupport a b n hr
  have hl : 2 * n05CanonicalCutoffWidth (2 * n + 1) ≤ r - a := by
    rw [n05CanonicalCutoffWidth_double]
    linarith [hi.1]
  have hh : 2 * n05CanonicalCutoffWidth (2 * n + 1) ≤ b - r := by
    rw [n05CanonicalCutoffWidth_double]
    linarith [hi.2]
  simp only [n05CanonicalRadialCutoffFunction,
    intervalLayerThreshold_one (n05CanonicalCutoffWidth_pos _) hl,
    intervalLayerThreshold_one (n05CanonicalCutoffWidth_pos _) hh, mul_one]

theorem n05CanonicalRadialCutoffFunction_plateau_mul (a b : ℝ) (n : ℕ) (r : ℝ) :
    n05CanonicalRadialCutoffFunction a b (2 * n + 1) r *
      n05CanonicalRadialCutoffFunction a b n r =
        n05CanonicalRadialCutoffFunction a b n r := by
  by_cases hr : n05CanonicalRadialCutoffFunction a b n r = 0
  · rw [hr, mul_zero]
  · rw [n05CanonicalRadialCutoffFunction_plateau a b n (subset_tsupport _ hr), one_mul]

theorem n05CanonicalRadialCutoffOperator_plateau (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalRadialCutoffOperator S K m (2 * n + 1)
      (n05CanonicalRadialCutoffOperator S K m n u) = n05CanonicalRadialCutoffOperator S K m n u := by
  apply Lp.ext
  filter_upwards [n05CanonicalRadialCutoffOperator_ae S K m (2 * n + 1)
      (n05CanonicalRadialCutoffOperator S K m n u),
    n05CanonicalRadialCutoffOperator_ae S K m n u] with p hp hq
  rw [hp, hq, ← mul_assoc, n05CanonicalRadialCutoffFunction_plateau_mul]

end ContinuousFlexibility.Statements
