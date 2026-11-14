module

public import ContinuousFlexibility.Analysis.N05CanonicalUniqueness

/-!
# One actual canonical radial derivative independent of source weights

Canonical tests separate L² classes. Whenever a sequence has a genuine
square-summable first radial derivative, the choice below is that unique
sequence. Its linearity is proved only on such actual derivative pairs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

def n05WeakCanonicalRadialDerivative (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (f d : CanonicalL2 S K m) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, d p * φ p ∂canonicalMeasure S K m) =
      -(∫ p, f p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)

theorem n05WeakCanonicalRadialDerivative_unique {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f d e : CanonicalL2 S K m}
    (hd : n05WeakCanonicalRadialDerivative S K m f d)
    (he : n05WeakCanonicalRadialDerivative S K m f e) : d = e := by
  apply sub_eq_zero.mp
  apply n05CanonicalL2_eq_zero_of_test S K m (d - e)
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  calc
    (∫ p, (d - e) p * φ p ∂canonicalMeasure S K m) = P (d - e) :=
      (n05CanonicalTestPairing_apply S K m φ _ (d - e)).symm
    _ = P d - P e := P.map_sub d e
    _ = (∫ p, d p * φ p ∂canonicalMeasure S K m) -
        (∫ p, e p * φ p ∂canonicalMeasure S K m) := by
      dsimp only [P]
      rw [n05CanonicalTestPairing_apply, n05CanonicalTestPairing_apply]
    _ = 0 := sub_eq_zero.mpr ((hd φ hφ).trans (he φ hφ).symm)

theorem n05WeakCanonicalRadialDerivative_add {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f g d e : CanonicalL2 S K m}
    (hd : n05WeakCanonicalRadialDerivative S K m f d)
    (he : n05WeakCanonicalRadialDerivative S K m g e) :
    n05WeakCanonicalRadialDerivative S K m (f + g) (d + e) := by
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  let Q := n05CanonicalTestPairing S K m (mixedDerivative 1 0 φ)
    (n05Canonical_memLp_of_continuous S K m (contDiff_mixedDerivative hφ.1 1 0).continuous)
  have hP (v : CanonicalL2 S K m) :
      P v = ∫ p, v p * φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m φ _ v
  have hQ (v : CanonicalL2 S K m) :
      Q v = ∫ p, v p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m (mixedDerivative 1 0 φ) _ v
  calc
    _ = P (d + e) := (hP _).symm
    _ = P d + P e := map_add P d e
    _ = -(Q f + Q g) := by
      rw [hP, hP, hQ, hQ, hd φ hφ, he φ hφ]
      ring
    _ = _ := by rw [← map_add, hQ]

theorem n05WeakCanonicalRadialDerivative_smul {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f d : CanonicalL2 S K m}
    (hd : n05WeakCanonicalRadialDerivative S K m f d) (c : ℝ) :
    n05WeakCanonicalRadialDerivative S K m (c • f) (c • d) := by
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  let Q := n05CanonicalTestPairing S K m (mixedDerivative 1 0 φ)
    (n05Canonical_memLp_of_continuous S K m (contDiff_mixedDerivative hφ.1 1 0).continuous)
  have hP (v : CanonicalL2 S K m) :
      P v = ∫ p, v p * φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m φ _ v
  have hQ (v : CanonicalL2 S K m) :
      Q v = ∫ p, v p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m (mixedDerivative 1 0 φ) _ v
  calc
    _ = P (c • d) := (hP _).symm
    _ = c * P d := by rw [map_smul, smul_eq_mul]
    _ = c * (-Q f) := by rw [hP, hQ, hd φ hφ]
    _ = -(Q (c • f)) := by rw [map_smul, smul_eq_mul]; ring
    _ = _ := by rw [hQ]

def n05CanonicalRadialJetSequence (S : PhysicalSpacesData) (K : CanonicalData S)
    (u : CanonicalL2Sequence S K) : CanonicalL2Sequence S K := by
  classical
  exact if h : ∃ d : CanonicalL2Sequence S K,
      ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (d m)
    then h.choose else 0

theorem n05CanonicalRadialJetSequence_eq_of_weak {S : PhysicalSpacesData}
    {K : CanonicalData S} {u d : CanonicalL2Sequence S K}
    (hd : ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (d m)) :
    n05CanonicalRadialJetSequence S K u = d := by
  classical
  have hex : ∃ e : CanonicalL2Sequence S K,
      ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (e m) := ⟨d, hd⟩
  rw [n05CanonicalRadialJetSequence, dite_eq_left hex]
  apply lp.ext
  funext m
  exact n05WeakCanonicalRadialDerivative_unique (hex.choose_spec m) (hd m)

theorem n05CanonicalRadialJetSequence_weak {S : PhysicalSpacesData}
    {K : CanonicalData S} {u d : CanonicalL2Sequence S K}
    (hd : ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (d m)) (m : ℕ) :
    n05WeakCanonicalRadialDerivative S K m (u m) (n05CanonicalRadialJetSequence S K u m) := by
  rw [n05CanonicalRadialJetSequence_eq_of_weak hd]
  exact hd m

theorem n05CanonicalRadialJetSequence_linear_combination
    {S : PhysicalSpacesData} {K : CanonicalData S}
    {u v du dv : CanonicalL2Sequence S K}
    (hu : ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (du m))
    (hv : ∀ m, n05WeakCanonicalRadialDerivative S K m (v m) (dv m)) (c d : ℝ) :
    n05CanonicalRadialJetSequence S K (c • u + d • v) = c • du + d • dv := by
  apply n05CanonicalRadialJetSequence_eq_of_weak
  intro m
  simpa only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply] using
    n05WeakCanonicalRadialDerivative_add
      (n05WeakCanonicalRadialDerivative_smul (hu m) c)
      (n05WeakCanonicalRadialDerivative_smul (hv m) d)

end ContinuousFlexibility.Statements
