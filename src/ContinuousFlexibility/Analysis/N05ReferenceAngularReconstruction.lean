import ContinuousFlexibility.Analysis.N05ReferenceAngularCoefficientEnergy
import ContinuousFlexibility.Radial.R11bProductSeries

/-!
# Strong weighted reconstruction of the actual high angular jets

Square summability of the genuine singleton jet energies reconstructs an
actual weighted L² field. The ordinary finite angular derivatives converge
to it strongly, and its weighted energy is exactly the summed energy.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

theorem n05_referenceHighAngularJet_reconstruct {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M : ℝ}
    (f : PolarPoint → ℝ) (b : ℕ)
    (hp : ∀ n, MemLp (referenceBasisProjection {n + 2} f) 2
      (referenceWeightedMeasure D γ M))
    (hs : Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      sourceNormSquare D γ M (referenceBasisProjection {n + 2} f, 0))) :
    ∃ d : PolarPoint → ℝ,
      MemLp d 2 (referenceWeightedMeasure D γ M) ∧
      (∫ x, d x ^ 2 ∂referenceWeightedMeasure D γ M) =
        ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          sourceNormSquare D γ M (referenceBasisProjection {n + 2} f, 0) ∧
      Tendsto (fun N => ∫ x, (n05_referenceHighAngularJet (Finset.range N) b f x - d x) ^ 2
        ∂referenceWeightedMeasure D γ M) atTop (𝓝 0) := by
  let c : ℕ → ℝ → ℝ := fun n r =>
    (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient f (n + 2) r
  have hc (n : ℕ) : MemLp (c n) 2 (referenceRadialWeightedMeasure D γ M) :=
    (n05_referenceWeighted_singleCoefficient hab hpart n (hp n)).1.const_mul _
  have he (n : ℕ) : MemLp (n05_referenceHighJetBasis b n) 2 referenceAngularProbability :=
    memLp_referenceAngularProbability (n05_referenceHighJetBasis_memLp b n)
  have hunit (n : ℕ) :
      (∫ θ, n05_referenceHighJetBasis b n θ ^ 2 ∂referenceAngularProbability) = 1 := by
    rw [integral_referenceAngularProbability]
    simpa only [angularPairing, angularAverage, radialAngularMean, one_div, pow_two,
      ite_true] using n05_referenceHighJetBasis_pairing b n n
  have horth : Pairwise (fun i j =>
      (∫ θ, n05_referenceHighJetBasis b i θ * n05_referenceHighJetBasis b j θ
        ∂referenceAngularProbability) = 0) := by
    intro i j hij
    rw [integral_referenceAngularProbability]
    simpa only [angularPairing, angularAverage, radialAngularMean, one_div,
      ite_eq_right hij] using n05_referenceHighJetBasis_pairing b i j
  have henergy (n : ℕ) :
      (∫ r, c n r ^ 2 ∂referenceRadialWeightedMeasure D γ M) =
        (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          sourceNormSquare D γ M (referenceBasisProjection {n + 2} f, 0) := by
    have hpoint : (fun r => c n r ^ 2) =
        fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          referenceRadialCoefficient f (n + 2) r ^ 2 := by
      funext r
      dsimp only [c]
      rw [Nat.mul_comm 2 b, pow_mul]
      ring
    rw [hpoint, integral_const_mul,
      (n05_referenceWeighted_singleCoefficient hab hpart n (hp n)).2]
  have hsq : Summable (fun n => ∫ r, c n r ^ 2
      ∂referenceRadialWeightedMeasure D γ M) :=
    hs.congr (fun n => (henergy n).symm)
  obtain ⟨d, hd, hnorm, hlim⟩ := r11b_product_orthogonal_series c
    (n05_referenceHighJetBasis b) hc he hunit horth hsq
  have hraw (N : ℕ) (x : PolarPoint) :
      n05_referenceHighAngularJet (Finset.range N) b f x =
        ∑ n ∈ Finset.range N, c n x.1 * n05_referenceHighJetBasis b n x.2 := by
    simpa only [r11bFiniteSynthesis, c] using
      congrFun (n05_referenceHighAngularJet_synthesis (Finset.range N) b f) x
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa only [referenceWeightedMeasure_eq_radial_prod hpart] using hd
  · rw [referenceWeightedMeasure_eq_radial_prod hpart]
    exact hnorm.trans (tsum_congr henergy)
  · simpa only [hraw, referenceWeightedMeasure_eq_radial_prod hpart] using hlim

end ContinuousFlexibility.Radial
