module

public import ContinuousFlexibility.Analysis.N05CanonicalMultipliers

/-!
# A single canonical angular jet independent of endpoint weights

The weak canonical derivative is unique as an L² class on every piece.
When its coordinates form a genuine L² sequence, choose that sequence
once. Endpoint proofs can therefore supply different physical derivative
representatives and still identify exactly the same canonical jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

def n05CanonicalAngularJetSequence (S : PhysicalSpacesData) (K : CanonicalData S)
    (u : CanonicalL2Sequence S K) (j : ℕ) : CanonicalL2Sequence S K := by
  classical
  exact if h : ∃ d : CanonicalL2Sequence S K,
      ∀ m, WeakCanonicalAngularDerivative S K m (u m) (d m) j
    then h.choose else 0

theorem n05CanonicalAngularJetSequence_unique {S : PhysicalSpacesData}
    {K : CanonicalData S} {u d e : CanonicalL2Sequence S K} {j : ℕ}
    (hd : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (d m) j)
    (he : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (e m) j) : d = e := by
  apply lp.ext
  funext m
  exact n05WeakCanonicalAngularDerivative_unique (hd m) (he m)

theorem n05CanonicalAngularJetSequence_eq_of_weak {S : PhysicalSpacesData}
    {K : CanonicalData S} {u d : CanonicalL2Sequence S K} {j : ℕ}
    (hd : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (d m) j) :
    n05CanonicalAngularJetSequence S K u j = d := by
  classical
  have hex : ∃ e : CanonicalL2Sequence S K,
      ∀ m, WeakCanonicalAngularDerivative S K m (u m) (e m) j := ⟨d, hd⟩
  rw [n05CanonicalAngularJetSequence, dite_eq_left hex]
  exact n05CanonicalAngularJetSequence_unique hex.choose_spec hd

theorem n05CanonicalAngularJetSequence_weak {S : PhysicalSpacesData}
    {K : CanonicalData S} {u d : CanonicalL2Sequence S K} {j : ℕ}
    (hd : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (d m) j) (m : ℕ) :
    WeakCanonicalAngularDerivative S K m (u m)
      (n05CanonicalAngularJetSequence S K u j m) j := by
  rw [n05CanonicalAngularJetSequence_eq_of_weak hd]
  exact hd m

@[simp] theorem n05CanonicalAngularJetSequence_zero (S : PhysicalSpacesData)
    (K : CanonicalData S) (u : CanonicalL2Sequence S K) :
    n05CanonicalAngularJetSequence S K u 0 = u := by
  apply n05CanonicalAngularJetSequence_eq_of_weak
  intro m φ hφ
  simp only [pow_zero, one_mul, mixedDerivative, iteratedDeriv_zero, Prod.eta]

theorem n05WeakCanonicalAngularDerivative_add {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f g d e : CanonicalL2 S K m} {j : ℕ}
    (hd : WeakCanonicalAngularDerivative S K m f d j)
    (he : WeakCanonicalAngularDerivative S K m g e j) :
    WeakCanonicalAngularDerivative S K m (f + g) (d + e) j := by
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  let Q := n05CanonicalTestPairing S K m (mixedDerivative 0 j φ)
    (n05CanonicalTest_angular_memLp hφ j)
  have hP (v : CanonicalL2 S K m) :
      P v = ∫ p, v p * φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m φ _ v
  have hQ (v : CanonicalL2 S K m) :
      Q v = ∫ p, v p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m :=
    n05CanonicalTestPairing_apply S K m (mixedDerivative 0 j φ) _ v
  calc
    _ = P (d + e) := (hP _).symm
    _ = P d + P e := map_add P d e
    _ = (-1 : ℝ) ^ j * (Q f + Q g) := by
      rw [hP, hP, hQ, hQ, hd φ hφ, he φ hφ]
      ring
    _ = _ := by rw [← map_add, hQ]

/-- Linearity follows from genuine weak identities and uniqueness. It
does not require pointwise linearity of any chosen function representative. -/
theorem n05CanonicalAngularJetSequence_linear_combination
    {S : PhysicalSpacesData} {K : CanonicalData S}
    {u v du dv : CanonicalL2Sequence S K} {j : ℕ}
    (hu : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (du m) j)
    (hv : ∀ m, WeakCanonicalAngularDerivative S K m (v m) (dv m) j) (c d : ℝ) :
    n05CanonicalAngularJetSequence S K (c • u + d • v) j = c • du + d • dv := by
  apply n05CanonicalAngularJetSequence_eq_of_weak
  intro m
  simpa only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply] using
    n05WeakCanonicalAngularDerivative_add
      (n05WeakCanonicalAngularDerivative_smul (hu m) c)
      (n05WeakCanonicalAngularDerivative_smul (hv m) d)

end ContinuousFlexibility.Statements
