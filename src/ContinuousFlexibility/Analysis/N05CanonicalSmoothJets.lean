import ContinuousFlexibility.Analysis.N05CanonicalEvenDensity
import ContinuousFlexibility.Analysis.CircleJetEncoding

/-!
# Smooth angular jets in each actual canonical rectangle

The angular integration-by-parts formula is integrated in the radial
variable. It identifies the ordinary smooth derivatives with the exact
weak canonical derivatives used by the closed volume graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n05Canonical_integral_angularDerivative_mul (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) {f φ : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f (0, Real.pi))
    (hφ : CanonicalTest S K m φ) (j : ℕ) :
    (∫ p, mixedDerivative 0 j f p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
  letI : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hl : Integrable (fun p => mixedDerivative 0 j f p * φ p)
      (canonicalMeasure S K m) :=
    (n05Canonical_memLp_of_continuous S K m
      ((contDiff_mixedDerivative hf 0 j).continuous.mul hφ.1.continuous)).integrable
        (by norm_num)
  have hr : Integrable (fun p => f p * mixedDerivative 0 j φ p)
      (canonicalMeasure S K m) :=
    (n05Canonical_memLp_of_continuous S K m
      (hf.continuous.mul (contDiff_mixedDerivative hφ.1 0 j).continuous)).integrable
        (by norm_num)
  rw [n05CanonicalMeasure_eq_prod] at hl hr ⊢
  rw [integral_prod _ hl, integral_prod _ hr, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  have hfr : ContDiff ℝ ∞ (fun θ : ℝ => f (r, θ)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hφr : ContDiff ℝ ∞ (fun θ : ℝ => φ (r, θ)) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hfpr : Function.Periodic (fun θ : ℝ => f (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hfp (r, θ)
  have hφpr : Function.Periodic (fun θ : ℝ => φ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    integral_angle_iteratedDeriv_mul hfr hfpr j hφr hφpr

def n05CanonicalSmoothJet (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    CanonicalL2 S K m :=
  (n05Canonical_memLp_of_continuous S K m (contDiff_mixedDerivative hf 0 j).continuous).toLp
    (mixedDerivative 0 j f)

theorem n05CanonicalSmoothJet_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    (n05CanonicalSmoothJet S K m hf j : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      mixedDerivative 0 j f :=
  MemLp.coeFn_toLp _

theorem n05CanonicalSmoothJet_zero_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    (n05CanonicalSmoothJet S K m hf 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f := by
  filter_upwards [n05CanonicalSmoothJet_ae S K m hf 0] with p hp
  simpa only [mixedDerivative, iteratedDeriv_zero, Prod.eta] using hp

theorem n05CanonicalSmoothJet_weak (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi)) (j : ℕ) :
    WeakCanonicalAngularDerivative S K m (n05CanonicalSmoothJet S K m hf 0)
      (n05CanonicalSmoothJet S K m hf j) j := by
  intro φ hφ
  have hl : (∫ p, n05CanonicalSmoothJet S K m hf j p * φ p ∂canonicalMeasure S K m) =
      ∫ p, mixedDerivative 0 j f p * φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [n05CanonicalSmoothJet_ae S K m hf j] with p hp
    rw [hp]
  have hr : (∫ p, n05CanonicalSmoothJet S K m hf 0 p * mixedDerivative 0 j φ p
      ∂canonicalMeasure S K m) =
      ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [n05CanonicalSmoothJet_zero_ae S K m hf] with p hp
    rw [hp]
  rw [hl, hr]
  exact n05Canonical_integral_angularDerivative_mul S K m hf hp hφ j

theorem n05CanonicalSmoothJet_zero_even (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) :
    n05CanonicalReflection S K m (n05CanonicalSmoothJet S K m hf 0) =
      n05CanonicalSmoothJet S K m hf 0 := by
  apply (n05CanonicalReflection_fixed_iff S K m _).mpr
  have ha := n05CanonicalSmoothJet_zero_ae S K m hf
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [hr, ha] with p hp hq
  change n05CanonicalSmoothJet S K m hf 0 (p.1, Real.pi - p.2) = f (p.1, Real.pi - p.2) at hp
  exact hp.trans ((he p).trans hq.symm)


theorem n05WeakCanonicalAngularDerivative_zero (S : PhysicalSpacesData)
    (K : CanonicalData S) (m j : ℕ) :
    WeakCanonicalAngularDerivative S K m 0 0 j := by
  intro φ hφ
  rw [← n05CanonicalTestPairing_apply S K m φ (n05CanonicalTest_memLp hφ)
      (0 : CanonicalL2 S K m), map_zero,
    ← n05CanonicalTestPairing_apply S K m (mixedDerivative 0 j φ)
      (n05CanonicalTest_angular_memLp hφ j) (0 : CanonicalL2 S K m),
    map_zero, mul_zero]

def n05CanonicalSmoothSingleRaw (S : PhysicalSpacesData) (K : CanonicalData S)
    (m s : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    CanonicalVolumeJets S K s :=
  lp.single 2 m (WithLp.toLp 2 (fun j : Fin (s + 1) =>
    n05CanonicalSmoothJet S K m hf j.val))

theorem n05CanonicalSmoothSingleRaw_self (S : PhysicalSpacesData) (K : CanonicalData S)
    (m s : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin (s + 1)) :
    n05CanonicalSmoothSingleRaw S K m s hf m j =
      n05CanonicalSmoothJet S K m hf j.val := by
  rw [n05CanonicalSmoothSingleRaw, lp.single_apply_self]

theorem n05CanonicalSmoothSingleRaw_ne (S : PhysicalSpacesData) (K : CanonicalData S)
    (m s : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (hn : n ≠ m) (j : Fin (s + 1)) :
    n05CanonicalSmoothSingleRaw S K m s hf n j = 0 := by
  simp only [n05CanonicalSmoothSingleRaw, lp.single_apply_ne 2 m _ hn, PiLp.zero_apply]

theorem n05CanonicalSmoothSingleRaw_mem_graph (S : PhysicalSpacesData)
    (K : CanonicalData S) (m s : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) :
    n05CanonicalSmoothSingleRaw S K m s hf ∈ canonicalVolumeGraph S K s := by
  refine ⟨?_, ?_⟩
  · intro n
    apply (n05CanonicalReflection_fixed_iff S K n _).mp
    by_cases hn : n = m
    · subst n
      simpa only [n05CanonicalSmoothSingleRaw_self, Fin.val_zero] using
        n05CanonicalSmoothJet_zero_even S K m hf he
    · simp only [n05CanonicalSmoothSingleRaw_ne S K m s hf hn, map_zero]
  · intro n j
    by_cases hn : n = m
    · subst n
      simpa only [n05CanonicalSmoothSingleRaw_self, Fin.val_zero] using
        n05CanonicalSmoothJet_weak S K m hf hp j.val
    · simp only [n05CanonicalSmoothSingleRaw_ne S K m s hf hn]
      exact n05WeakCanonicalAngularDerivative_zero S K n j.val

def n05CanonicalSmoothSingle (S : PhysicalSpacesData) (K : CanonicalData S)
    (m s : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) :
    n05CanonicalClosedSubmodule S K s :=
  ⟨n05CanonicalSmoothSingleRaw S K m s hf, by
    rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
    exact n05CanonicalSmoothSingleRaw_mem_graph S K m s hf hp he⟩

theorem n05CanonicalSmoothSingle_zero_test {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f : PolarPoint → ℝ} (hf : CanonicalTest S K m f)
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) (s : ℕ) :
    (n05CanonicalSmoothSingle S K m s hf.1 hf.2.1 he).val m 0 = n05CanonicalTestL2 hf := by
  change n05CanonicalSmoothSingleRaw S K m s hf.1 m 0 = n05CanonicalTestL2 hf
  rw [n05CanonicalSmoothSingleRaw_self]
  apply Lp.ext
  exact (n05CanonicalSmoothJet_zero_ae S K m hf.1).trans (n05CanonicalTestL2_ae hf).symm


end ContinuousFlexibility.Statements

