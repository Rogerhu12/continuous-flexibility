import ContinuousFlexibility.Analysis.N07aAngularRadialRegularity
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# The actual rough divergence equation recovers the first normal graph

Only angular weak jets of the unknown are assumed. Expanding the test
operator and transferring its angular derivatives gives the genuine
identity `(a u)ᵣᵣ = ((aᵣ - bθ)u - 2b uθ)ᵣ + F + (bᵣu - c uθ)θ`.
The compact Fourier argument then gives first normal regularity on each
smaller strip, with no trace hypothesis and no smooth unknown.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K J : CanonicalData S} {m n : ℕ}

private theorem n07a_openCoefficient_firstTest_pairing
    (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : Fin 2) :
    (∫ p, u p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
      (fun q => χ.value q * φ q) p ∂canonicalMeasure S K m) =
      (∫ p, (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).mul u p * φ p
        ∂canonicalMeasure S K m) +
      ∫ p, χ.mul u p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p
        ∂canonicalMeasure S K m := by
  have hi₁ := (Lp.memLp ((χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).mul u)).integrable_mul
    (n07a_canonicalTest_memLp hφ)
  have hi₂ := (Lp.memLp (χ.mul u)).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ
      (n07aFirstOrder j).1 (n07aFirstOrder j).2))
  have hsum := integral_add hi₁ hi₂
  simp only [Pi.mul_apply] at hsum
  rw [← hsum]
  apply integral_congr_ae
  filter_upwards [χ.mul_ae u,
    (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).mul_ae u,
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp hdp hpU
  rw [hp, hdp, n07a_mixedDerivative_first_mul_on χ.smooth hφ.1.contDiffOn j hpU]
  change u p * (mixedDerivative _ _ χ.value p * φ p + χ.value p * mixedDerivative _ _ φ p) = _
  dsimp only [N07aCanonicalOpenCoefficient.jet]
  ring

/-- The true distribution equation, without a known radial derivative,
gives a second-normal primitive identity in the actual canonical L² space. -/
theorem n07a_distribution_secondPrimitive
    (a b c : N07aCanonicalOpenCoefficient S K m)
    {u uθ uθθ F : CanonicalL2 S K m}
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (heq : N07aCanonicalDistributionEquation S K m
      ⟨a.value, b.value, c.value⟩ u F) :
    N07aCanonicalSecondPrimitiveEquation (a.mul u)
      ((a.jet 1 0).mul u - (b.jet 0 1).mul u - b.mul uθ - b.mul uθ)
      (F + (((b.jet 1 0).mul uθ + ((b.jet 1 0).jet 0 1).mul u) -
        (c.mul uθθ + (c.jet 0 1).mul uθ))) := by
  intro φ hφ
  have hfirst0 : n07aFirstOrder (0 : Fin 2) = (1, 0) := rfl
  have hfirst1 : n07aFirstOrder (1 : Fin 2) = (0, 1) := rfl
  let I (r t : ℕ) : CanonicalL2 S K m →L[ℝ] ℝ :=
    n07aCanonicalTestPairing (mixedDerivative r t φ)
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ r t))
  have hI (r t : ℕ) (v : CanonicalL2 S K m) : I r t v =
      ∫ p, v p * mixedDerivative r t φ p ∂canonicalMeasure S K m :=
    n07aCanonicalTestPairing_apply _ _ v
  have hI0 (v : CanonicalL2 S K m) : I 0 0 v =
      ∫ p, v p * φ p ∂canonicalMeasure S K m := by rw [hI, spaces_mixedDerivative_zero]
  let φr := mixedDerivative 1 0 φ
  let φθ := mixedDerivative 0 1 φ
  have hφr : CanonicalTest S K m φr := n07a_canonicalTest_mixedDerivative hφ 1 0
  have hφθ : CanonicalTest S K m φθ := n07a_canonicalTest_mixedDerivative hφ 0 1
  have htest (χ : N07aCanonicalOpenCoefficient S K m) (r t : ℕ) :
      CanonicalTest S K m (fun p => χ.value p * mixedDerivative r t φ p) :=
    n07a_canonicalTest_mul_on (n07a_canonicalTest_mixedDerivative hφ r t)
      χ.smooth χ.periodic
  have hprod (χ : N07aCanonicalOpenCoefficient S K m) (r t : ℕ) (j : Fin 2) :
      (∫ p, u p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
        (fun q => χ.value q * mixedDerivative r t φ q) p ∂canonicalMeasure S K m) =
      I r t ((χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).mul u) +
        I ((n07aFirstOrder j).1 + r) ((n07aFirstOrder j).2 + t) (χ.mul u) := by
    rw [n07a_openCoefficient_firstTest_pairing χ u
      (n07a_canonicalTest_mixedDerivative hφ r t) j,
      n07a_mixedDerivative_mixedDerivative hφ.1, ← hI, ← hI]
  have hi (χ : N07aCanonicalOpenCoefficient S K m) (r t dr dt : ℕ) :
      Integrable (fun p => u p * mixedDerivative dr dt
        (fun q => χ.value q * mixedDerivative r t φ q) p) (canonicalMeasure S K m) :=
    (Lp.memLp u).integrable_mul
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative (htest χ r t) dr dt))
  have hdiv : (∫ p, u p * divergenceOperator ⟨a.value, b.value, c.value⟩ φ p
      ∂canonicalMeasure S K m) =
      (I 1 0 ((a.jet 1 0).mul u) + I 2 0 (a.mul u)) +
      (I 0 1 ((b.jet 1 0).mul u) + I 1 1 (b.mul u)) +
      ((I 1 0 ((b.jet 0 1).mul u) + I 1 1 (b.mul u)) +
      (I 0 1 ((c.jet 0 1).mul u) + I 0 2 (c.mul u))) := by
    have he : (fun p => u p * divergenceOperator ⟨a.value, b.value, c.value⟩ φ p)
        =ᵐ[canonicalMeasure S K m] fun p =>
          (u p * mixedDerivative 1 0 (fun q => a.value q * φr q) p +
            u p * mixedDerivative 1 0 (fun q => b.value q * φθ q) p) +
          (u p * mixedDerivative 0 1 (fun q => b.value q * φr q) p +
            u p * mixedDerivative 0 1 (fun q => c.value q * φθ q) p) := by
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
      rw [n07a_open_divergence_mixed ⟨a.value, b.value, c.value⟩
        a.smooth b.smooth c.smooth hφ.1.contDiffOn hp]
      dsimp only
      rw [spaces_mixedDerivative_add (htest a 1 0).1 (htest b 0 1).1,
        spaces_mixedDerivative_add (htest b 1 0).1 (htest c 0 1).1]
      dsimp only [φr, φθ]
      ring
    have houter := integral_add ((hi a 1 0 1 0).add (hi b 0 1 1 0))
      ((hi b 1 0 0 1).add (hi c 0 1 0 1))
    simp only [Pi.add_apply] at houter
    rw [integral_congr_ae he]
    dsimp only [φr, φθ]
    rw [houter, integral_add (hi a 1 0 1 0) (hi b 0 1 1 0),
      integral_add (hi b 1 0 0 1) (hi c 0 1 0 1)]
    simpa only [hfirst0, hfirst1, Prod.fst, Prod.snd,
      zero_add, add_zero, Nat.reduceAdd] using
      congrArg₂ (· + ·) (congrArg₂ (· + ·) (hprod a 1 0 0) (hprod b 0 1 0))
        (congrArg₂ (· + ·) (hprod b 1 0 1) (hprod c 0 1 1))
  have hb := b.first_product (1 : Fin 2) hθ φr hφr
  have hc := c.first_product (1 : Fin 2) hθ φθ hφθ
  have hq := ((b.jet 1 0).first_product (1 : Fin 2) hθ).sub
    (c.first_product (1 : Fin 2) hθθ)
  have hqtest := hq φ hφ
  simp only [hfirst1, zero_add, add_zero, Nat.reduceAdd,
    pow_one, neg_one_mul, φr, φθ,
    n07a_mixedDerivative_mixedDerivative hφ.1] at hb hc hqtest
  rw [← hI 1 0, ← hI 1 1, map_add] at hb
  rw [← hI 0 1, ← hI 0 2, map_add] at hc
  rw [← hI0, ← hI 0 1, map_sub] at hqtest
  have h := heq φ hφ
  rw [hdiv, ← hI0] at h
  rw [← hI 2 0, ← hI 1 0, ← hI0, map_sub, map_sub, map_sub, map_add]
  simp only [map_add, map_sub] at hqtest ⊢
  linarith only [h, hb, hc, hqtest]

/-- Restriction of the actual solution has every angular jet and its first
normal jets, provided the real leading coefficient has its real reciprocal. -/
theorem n07a_distribution_firstRegular_restrict
    (hm : K.left m < K.right m)
    (a b c ρ : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    {u F : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m u 0)
    (hF : N07aCanonicalNormalRegular S K m F 0)
    (heq : N07aCanonicalDistributionEquation S K m
      ⟨a.value, b.value, c.value⟩ u F)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {ξ : ℝ → ℝ} (hξ : CanonicalTest S K m (fun p => ξ p.1))
    (hone : ∀ p ∈ canonicalOpen S J n, ξ p.1 = 1) :
    N07aCanonicalNormalRegular S J n (n07aCanonicalRestrict hsub u) 1 := by
  obtain ⟨uθ, hθ⟩ := hu 0 le_rfl 1
  have huθ : N07aCanonicalNormalRegular S K m uθ 0 := hu.derivative hθ
  obtain ⟨uθθ, hθθ⟩ := huθ 0 le_rfl 1
  have hq := ((b.jet 1 0).first_product (1 : Fin 2) hθ).sub
    (c.first_product (1 : Fin 2) hθθ)
  have hqreg := ((b.jet 1 0).angularRegular hu).sub (c.angularRegular huθ)
  have hqθreg : N07aCanonicalNormalRegular S K m
      (((b.jet 1 0).mul uθ + ((b.jet 1 0).jet 0 1).mul u) -
        (c.mul uθθ + (c.jet 0 1).mul uθ)) 0 := hqreg.derivative hq
  have hlocal := n07a_secondPrimitive_local_firstRegular m hm hξ
    (n07a_distribution_secondPrimitive a b c hθ hθθ heq)
    (a.angularRegular hu)
    ((((a.jet 1 0).angularRegular hu).sub ((b.jet 0 1).angularRegular hu)).sub
      (b.angularRegular huθ) |>.sub (b.angularRegular huθ))
    (hF.add hqθreg)
  exact n07aCanonicalRestrict_localFirst hsub hξ.1 hone
    (n07a_firstRegular_of_leading_localization a ρ hinv hξ.1 hlocal)

end ContinuousFlexibility.Analysis
