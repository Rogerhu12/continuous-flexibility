import ContinuousFlexibility.Analysis.SpacesTorusFourier

/-!
# Real Fourier shells and finite frequency windows

Symmetry under simultaneous frequency reversal makes each finite band of
a real function real. Thus the physical analysis and synthesis operators
can use real cylinder `L²` rows while their Fourier calculation uses the
complex exponential basis internally.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate Topology

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : DecidableEq SpacesTorusFrequency := Classical.decEq _

theorem spacesTorusFourier_neg_of_real (u : SpacesTorusL2)
    (hu : (fun t => conj (u t)) =ᵐ[volume] u) (j : SpacesTorusFrequency) :
    spacesTorusFourier u (-j) = conj (spacesTorusFourier u j) := by
  rw [spacesTorusFourier_coefficient, spacesTorusFourier_coefficient]
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [hu] with t ht
  simp only [neg_neg, smul_eq_mul, map_mul, UnitAddTorus.mFourier_neg,
    starRingEnd_self_apply, ht]

theorem spacesTorusPolynomial_apply (S : Finset SpacesTorusFrequency)
    (u : SpacesTorusCoefficients) (t : SpacesTorus) :
    spacesTorusPolynomial S u t = ∑ j ∈ S, u j * UnitAddTorus.mFourier j t := by
  simp only [spacesTorusPolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_coe_sort S (fun j => u j * UnitAddTorus.mFourier j t)

theorem spacesTorusPolynomial_conj (S : Finset SpacesTorusFrequency)
    (u : SpacesTorusCoefficients) (hS : ∀ j : SpacesTorusFrequency, -j ∈ S ↔ j ∈ S)
    (hu : ∀ j, u (-j) = conj (u j)) (t : SpacesTorus) :
    conj (spacesTorusPolynomial S u t) = spacesTorusPolynomial S u t := by
  rw [spacesTorusPolynomial_apply, map_sum]
  calc
    (∑ j ∈ S, conj (u j * UnitAddTorus.mFourier j t)) =
        ∑ j ∈ S, u (-j) * UnitAddTorus.mFourier (-j) t := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_mul, hu, UnitAddTorus.mFourier_neg]
    _ = ∑ j ∈ S, u j * UnitAddTorus.mFourier j t := by
      apply Finset.sum_bij (fun j _ => -j)
      · intro j hj
        exact (hS j).mpr hj
      · intro i _ j _ hij
        exact neg_injective hij
      · intro j hj
        exact ⟨-j, (hS j).mpr hj, neg_neg j⟩
      · intro j _
        rfl

theorem spacesTorusPolynomial_re_coe (S : Finset SpacesTorusFrequency)
    (u : SpacesTorusCoefficients) (hS : ∀ j : SpacesTorusFrequency, -j ∈ S ↔ j ∈ S)
    (hu : ∀ j, u (-j) = conj (u j)) (t : SpacesTorus) :
    ((spacesTorusPolynomial S u t).re : ℂ) = spacesTorusPolynomial S u t :=
  Complex.conj_eq_iff_re.mp (spacesTorusPolynomial_conj S u hS hu t)

theorem spacesTorusBand_coeff_neg_of_real (band : SpacesTorusFrequency → ℕ)
    (hb : ∀ j, band (-j) = band j) (k : ℕ) (u : SpacesTorusL2)
    (hu : (fun t => conj (u t)) =ᵐ[volume] u) (j : SpacesTorusFrequency) :
    lpSpectralBand band k (spacesTorusFourier u) (-j) =
      conj (lpSpectralBand band k (spacesTorusFourier u) j) := by
  simp only [lpSpectralBand_apply, hb, spacesTorusFourier_neg_of_real u hu]
  split_ifs <;> simp

/-- A symmetric finite frequency box. -/
def spacesTorusFrequencyBox (N : ℕ) : Finset SpacesTorusFrequency :=
  Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) N)

theorem spacesTorusFrequencyBox_mem (N : ℕ) (j : SpacesTorusFrequency) :
    j ∈ spacesTorusFrequencyBox N ↔ ∀ i : Fin 2, |j i| ≤ (N : ℤ) := by
  simp only [spacesTorusFrequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]

theorem spacesTorusFrequencyBox_neg (N : ℕ) (j : SpacesTorusFrequency) :
    -j ∈ spacesTorusFrequencyBox N ↔ j ∈ spacesTorusFrequencyBox N := by
  simp only [spacesTorusFrequencyBox_mem, Pi.neg_apply, abs_neg]

theorem spacesTorusFrequencyBox_mem_of_real_bound {R : ℝ} {N : ℕ}
    (hRN : R ≤ N) {j : SpacesTorusFrequency} (hj : ∀ i : Fin 2, |(j i : ℝ)| ≤ R) :
    j ∈ spacesTorusFrequencyBox N := by
  apply (spacesTorusFrequencyBox_mem N j).mpr
  intro i
  exact_mod_cast (hj i).trans hRN

/-- Every logarithmic band of a size dominating both frequencies is finite. -/
theorem spacesTorusLogBand_frequencyBox (weight : SpacesTorusFrequency → ℝ)
    (hw : ∀ j, 1 ≤ weight j) (hfreq : ∀ j i, |(j i : ℝ)| ≤ weight j)
    (k : ℕ) (j : SpacesTorusFrequency) (hj : spectralLogBand weight j = k) :
    j ∈ spacesTorusFrequencyBox ⌈Real.exp ((k : ℝ) + 1)⌉₊ := by
  apply spacesTorusFrequencyBox_mem_of_real_bound (Nat.le_ceil _)
  intro i
  have h := spectralLogBand_upper weight hw j
  rw [hj] at h
  exact (hfreq j i).trans h.le

/-- Symmetric finite Fourier bands of a real function remain real almost everywhere. -/
theorem spacesTorusBand_real (band : SpacesTorusFrequency → ℕ)
    (hb : ∀ j, band (-j) = band j) (k N : ℕ)
    (hN : ∀ j, band j = k → j ∈ spacesTorusFrequencyBox N)
    (u : SpacesTorusL2) (hu : (fun t => conj (u t)) =ᵐ[volume] u) :
    (fun t => conj (spacesTorusBand band k u t)) =ᵐ[volume] spacesTorusBand band k u := by
  rw [spacesTorusBand_eq_polynomial band k (spacesTorusFrequencyBox N) hN]
  have hae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure SpacesTorus)
    (spacesTorusPolynomial (spacesTorusFrequencyBox N) (lpSpectralBand band k (spacesTorusFourier u)))
  filter_upwards [hae] with t ht
  rw [ht]
  exact spacesTorusPolynomial_conj _ _ (spacesTorusFrequencyBox_neg N)
    (spacesTorusBand_coeff_neg_of_real band hb k u hu) t

end ContinuousFlexibility.Analysis
