module

public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets
public import ContinuousFlexibility.Analysis.SpacesCircleSpectral

/-!
# Finite angular Fourier projections

Symmetric frequency sets preserve real-valued functions. The projection
formulas below are exact Fourier coefficient identities, not approximation
assumptions supplied by a caller.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate ContDiff

/-- Passing from the actual angular interval to the quotient circle preserves
our Fourier coefficients with their stated normalization. -/
theorem circleFourierCoeff_eq_liftIoc (f : ℝ → ℝ) (n : ℤ) :
    circleFourierCoeff f n =
      fourierCoeff (AddCircle.liftIoc Real.pi 0 (fun θ => (f θ : ℂ))) n := by
  simpa only [circleFourierCoeff, zero_add] using
    (fourierCoeff_liftIoc_eq (T := Real.pi) (a := 0) (fun θ => (f θ : ℂ)) n).symm

theorem fourierCoeffOn_circlePullback (g : AddCircle Real.pi → ℂ) (n : ℤ) :
    fourierCoeffOn Real.pi_pos (fun θ : ℝ => g (θ : AddCircle Real.pi)) n =
      fourierCoeff g n := by
  have hlift : AddCircle.liftIoc Real.pi 0 (fun θ : ℝ => g (θ : AddCircle Real.pi)) = g := by
    funext x
    simp only [AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply,
      AddCircle.coe_equivIoc]
  simpa only [zero_add, hlift] using
    (fourierCoeff_liftIoc_eq (T := Real.pi) (a := 0)
      (fun θ : ℝ => g (θ : AddCircle Real.pi)) n).symm

/-- A finite Fourier polynomial, on the actual angular coordinate. -/
def circleFourierPolynomial (s : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, c n * circleFourierWave n θ

theorem circleFourierPolynomial_contDiff (s : Finset ℤ) (c : ℤ → ℂ) :
    ContDiff ℝ ∞ (circleFourierPolynomial s c) :=
  ContDiff.sum (fun n _ => contDiff_const.mul (circleFourierWave_contDiff n))

theorem circleFourierPolynomial_periodic (s : Finset ℤ) (c : ℤ → ℂ) :
    Function.Periodic (circleFourierPolynomial s c) Real.pi := by
  intro θ
  apply Finset.sum_congr rfl
  intro n _
  rw [circleFourierWave_periodic n θ]

theorem circleFourierPolynomial_coeff (s : Finset ℤ) (c : ℤ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.pi_pos (circleFourierPolynomial s c) n =
      if n ∈ s then c n else 0 := by
  classical
  have hInt (j : ℤ) : Integrable
      (fun x : AddCircle Real.pi => c j * fourier (T := Real.pi) j x) AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier (T := Real.pi) j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum := congrFun (fourierCoeff.sum s
    (fun j => fun x : AddCircle Real.pi => c j * fourier (T := Real.pi) j x) (fun j _ => hInt j)) n
  have heq : circleFourierPolynomial s c =
      fun θ : ℝ => (fun x : AddCircle Real.pi => ∑ j ∈ s, c j * fourier (T := Real.pi) j x)
        (θ : AddCircle Real.pi) := rfl
  rw [heq]
  refine (fourierCoeffOn_circlePullback
    (fun x : AddCircle Real.pi => ∑ j ∈ s, c j * fourier (T := Real.pi) j x) n).trans ?_
  have hfun : (∑ j ∈ s, fun x : AddCircle Real.pi => c j * fourier (T := Real.pi) j x) =
      (fun x : AddCircle Real.pi => ∑ j ∈ s, c j * fourier (T := Real.pi) j x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [← hfun]
  refine hsum.trans ?_
  have hj (j : ℤ) : fourierCoeff (fun x : AddCircle Real.pi => c j * fourier (T := Real.pi) j x) n =
      c j * (Pi.single j (1 : ℂ) : ℤ → ℂ) n := by
    rw [fourierCoeff.const_mul (T := Real.pi) (fourier (T := Real.pi) j) (c j) n]
    rw [fourierCoeff_fourier (T := Real.pi) j]
  simp only [Finset.sum_apply, hj, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]

theorem circleFourierPolynomial_conj (s : Finset ℤ) (c : ℤ → ℂ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (hc : ∀ n, c (-n) = conj (c n)) (θ : ℝ) :
    conj (circleFourierPolynomial s c θ) = circleFourierPolynomial s c θ := by
  classical
  unfold circleFourierPolynomial
  rw [map_sum]
  calc
    (∑ n ∈ s, conj (c n * circleFourierWave n θ)) =
        ∑ n ∈ s, c (-n) * circleFourierWave (-n) θ := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [map_mul, hc n, circleFourierWave, fourier_neg]
    _ = ∑ n ∈ s, c n * circleFourierWave n θ := by
      apply Finset.sum_bij (fun n _ => -n)
      · intro n hn
        exact (hs n).mpr hn
      · intro a _ b _ hab
        exact neg_injective hab
      · intro b hb
        exact ⟨-b, (hs b).mpr hb, neg_neg b⟩
      · intro n _
        rfl

theorem circleFourierPolynomial_re_coe (s : Finset ℤ) (c : ℤ → ℂ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (hc : ∀ n, c (-n) = conj (c n)) (θ : ℝ) :
    ((circleFourierPolynomial s c θ).re : ℂ) = circleFourierPolynomial s c θ :=
  Complex.conj_eq_iff_re.mp (circleFourierPolynomial_conj s c hs hc θ)

theorem circleFourierPolynomial_re_coeff (s : Finset ℤ) (c : ℤ → ℂ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (hc : ∀ n, c (-n) = conj (c n)) (n : ℤ) :
    circleFourierCoeff (fun θ => (circleFourierPolynomial s c θ).re) n =
      if n ∈ s then c n else 0 := by
  unfold circleFourierCoeff
  have heq : (fun θ => ((circleFourierPolynomial s c θ).re : ℂ)) =
      circleFourierPolynomial s c := funext (circleFourierPolynomial_re_coe s c hs hc)
  rw [heq]
  exact circleFourierPolynomial_coeff s c n

end ContinuousFlexibility.Statements
