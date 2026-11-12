import ContinuousFlexibility.Analysis.N07aWeakNormalEquation

/-!
# An algebra of actual mixed weak jets

On a fixed bounded canonical piece, every globally smooth coefficient and
all its derivatives are bounded. Multiplication therefore preserves any
finite number of weak normal derivatives together with all angular
derivatives. The proof uses only the actual weak product rule and tests.
No smoothness of an L² unknown is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_smoothCanonical_bounded (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ A : ℝ, ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A := by
  let Q : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc 0 Real.pi
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact Q).bddAbove_image
    hχ.continuous.abs.continuousOn
  refine ⟨A, ?_⟩
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc 0 Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact hA ⟨p, ⟨Ioo_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩, rfl⟩

/-- The same actual L² multiplier, with a compact-piece bound chosen once. -/
def n07aSmoothCanonicalMul (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable
    (n07a_smoothCanonical_bounded (S := S) (K := K) (m := m) χ hχ).choose
    (n07a_smoothCanonical_bounded χ hχ).choose_spec

theorem n07aSmoothCanonicalMul_ae (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (u : CanonicalL2 S K m) :
    (n07aSmoothCanonicalMul χ hχ u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => χ p * u p :=
  n07aCanonicalMultiplier_ae χ _ _ _ u

/-- The choice of a coefficient bound does not change the multiplier. -/
theorem n07aSmoothCanonicalMul_eq (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℝ) (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A) :
    n07aSmoothCanonicalMul χ hχ =
      n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  exact (n07aSmoothCanonicalMul_ae χ hχ u).trans
    (n07aCanonicalMultiplier_ae χ _ A hA u).symm

theorem n07a_canonicalCoefficient_derivative_periodic {χ : PolarPoint → ℝ}
    (hχp : Function.Periodic χ (0, Real.pi)) (a b : ℕ) :
    Function.Periodic (mixedDerivative a b χ) (0, Real.pi) := by
  have hper (r : ℝ) : Function.Periodic (fun θ => χ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hχp (r, θ)
  rintro ⟨r, θ⟩
  simpa only [Prod.mk_add_mk, add_zero] using mixedDerivative_angular_periodic hper a b r θ

theorem n07aSmoothCanonicalMul_first_product {χ : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχp : Function.Periodic χ (0, Real.pi)) (j : Fin 2)
    {f g : CanonicalL2 S K m}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    N07aWeakCanonicalMixedDerivative S K m (n07aSmoothCanonicalMul χ hχ f)
      (n07aSmoothCanonicalMul χ hχ g +
        n07aSmoothCanonicalMul (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
          (contDiff_mixedDerivative hχ _ _) f)
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 := by
  obtain ⟨A, hA⟩ := n07a_smoothCanonical_bounded (S := S) (K := K) (m := m) χ hχ
  obtain ⟨B, hB⟩ := n07a_smoothCanonical_bounded (S := S) (K := K) (m := m)
    (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
    (contDiff_mixedDerivative hχ _ _)
  rw [n07aSmoothCanonicalMul_eq χ hχ A hA,
    n07aSmoothCanonicalMul_eq _ (contDiff_mixedDerivative hχ _ _) B hB]
  exact n07a_weakCanonical_first_product hχ hχp j A B hA hB hfg

/-- All angular derivatives and at most `n` normal derivatives, in the
original canonical L² and test spaces. -/
def N07aCanonicalNormalRegular (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) (n : ℕ) : Prop :=
  ∀ a : ℕ, a ≤ n → ∀ b : ℕ, ∃ v : CanonicalL2 S K m,
    N07aWeakCanonicalMixedDerivative S K m u v a b

theorem N07aCanonicalNormalRegular.mono {u : CanonicalL2 S K m} {n k : ℕ}
    (hu : N07aCanonicalNormalRegular S K m u n) (hkn : k ≤ n) :
    N07aCanonicalNormalRegular S K m u k :=
  fun a ha b => hu a (ha.trans hkn) b

theorem N07aCanonicalNormalRegular.add {u v : CanonicalL2 S K m} {n : ℕ}
    (hu : N07aCanonicalNormalRegular S K m u n)
    (hv : N07aCanonicalNormalRegular S K m v n) :
    N07aCanonicalNormalRegular S K m (u + v) n := by
  intro a ha b
  obtain ⟨du, hdu⟩ := hu a ha b
  obtain ⟨dv, hdv⟩ := hv a ha b
  exact ⟨du + dv, hdu.add hdv⟩

theorem N07aCanonicalNormalRegular.neg {u : CanonicalL2 S K m} {n : ℕ}
    (hu : N07aCanonicalNormalRegular S K m u n) :
    N07aCanonicalNormalRegular S K m (-u) n := by
  intro a ha b
  obtain ⟨v, hv⟩ := hu a ha b
  exact ⟨-v, hv.neg⟩

theorem N07aCanonicalNormalRegular.sub {u v : CanonicalL2 S K m} {n : ℕ}
    (hu : N07aCanonicalNormalRegular S K m u n)
    (hv : N07aCanonicalNormalRegular S K m v n) :
    N07aCanonicalNormalRegular S K m (u - v) n := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

theorem n07aCanonicalNormalRegular_zero (n : ℕ) :
    N07aCanonicalNormalRegular S K m 0 n :=
  fun a _ b => ⟨0, n07a_weakCanonicalMixed_zero a b⟩

theorem n07aCanonicalNormalRegular_sum {ι : Type*} (s : Finset ι)
    (u : ι → CanonicalL2 S K m) (n : ℕ)
    (hu : ∀ i ∈ s, N07aCanonicalNormalRegular S K m (u i) n) :
    N07aCanonicalNormalRegular S K m (∑ i ∈ s, u i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using n07aCanonicalNormalRegular_zero n
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

/-- A prescribed lower jet inherits all remaining derivatives from the
original field. The construction uses the actual weak suffix identity. -/
theorem N07aCanonicalNormalRegular.derivative
    {u v : CanonicalL2 S K m} {n a b : ℕ}
    (hu : N07aCanonicalNormalRegular S K m u (n + a))
    (hv : N07aWeakCanonicalMixedDerivative S K m u v a b) :
    N07aCanonicalNormalRegular S K m v n := by
  intro c hc d
  obtain ⟨w, hw⟩ := hu (a + c) (by omega) (b + d)
  exact ⟨w, hv.suffix hw⟩

theorem n07aCanonicalNormalRegular_of_first
    {u ur : CanonicalL2 S K m} {n : ℕ}
    (hangle : N07aCanonicalNormalRegular S K m u 0)
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hur : N07aCanonicalNormalRegular S K m ur n) :
    N07aCanonicalNormalRegular S K m u (n + 1) := by
  intro a ha b
  cases a with
  | zero => exact hangle 0 le_rfl b
  | succ a =>
    obtain ⟨v, hv⟩ := hur a (by omega) b
    refine ⟨v, ?_⟩
    simpa only [Nat.zero_add, Nat.one_add] using hr.comp hv

private theorem n07aSmoothCanonicalMul_angularJet (k : ℕ) :
    ∀ (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ),
      Function.Periodic χ (0, Real.pi) → ∀ f : CanonicalL2 S K m,
      N07aCanonicalNormalRegular S K m f 0 →
      ∃ v : CanonicalL2 S K m,
        N07aWeakCanonicalMixedDerivative S K m (n07aSmoothCanonicalMul χ hχ f) v 0 k := by
  induction k with
  | zero =>
    intro χ hχ _ f _
    exact ⟨_, n07a_weakCanonicalMixed_refl _⟩
  | succ k ih =>
    intro χ hχ hχp f hf
    obtain ⟨fθ, hfθ⟩ := hf 0 le_rfl 1
    have hfθreg : N07aCanonicalNormalRegular S K m fθ 0 :=
      hf.derivative hfθ
    obtain ⟨v, hv⟩ := ih χ hχ hχp fθ hfθreg
    obtain ⟨w, hw⟩ := ih (mixedDerivative 0 1 χ) (contDiff_mixedDerivative hχ 0 1)
      (n07a_canonicalCoefficient_derivative_periodic hχp 0 1) f hf
    have hfirst := n07aSmoothCanonicalMul_first_product hχ hχp (1 : Fin 2) hfθ
    refine ⟨v + w, ?_⟩
    simpa [n07aFirstOrder, Nat.add_comm] using
      hfirst.comp (hv.add hw)

theorem n07aSmoothCanonicalMul_angularRegular
    (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχp : Function.Periodic χ (0, Real.pi)) {u : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m u 0) :
    N07aCanonicalNormalRegular S K m (n07aSmoothCanonicalMul χ hχ u) 0 := by
  intro a ha b
  have : a = 0 := Nat.eq_zero_of_le_zero ha
  subst a
  exact n07aSmoothCanonicalMul_angularJet b χ hχ hχp u hu

/-- Smooth periodic coefficient multiplication preserves every finite
normal order and all angular orders of the actual weak jet space. -/
theorem n07aSmoothCanonicalMul_normalRegular (n : ℕ) :
    ∀ (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ),
      Function.Periodic χ (0, Real.pi) → ∀ u : CanonicalL2 S K m,
      N07aCanonicalNormalRegular S K m u n →
      N07aCanonicalNormalRegular S K m (n07aSmoothCanonicalMul χ hχ u) n := by
  induction n with
  | zero =>
    intro χ hχ hχp u hu
    exact n07aSmoothCanonicalMul_angularRegular χ hχ hχp hu
  | succ n ih =>
    intro χ hχ hχp u hu
    obtain ⟨ur, hur⟩ := hu 1 (by omega) 0
    have hurreg : N07aCanonicalNormalRegular S K m ur n := hu.derivative hur
    have hureg : N07aCanonicalNormalRegular S K m u n := hu.mono (by omega)
    have hprod := n07aSmoothCanonicalMul_first_product hχ hχp (0 : Fin 2) hur
    apply n07aCanonicalNormalRegular_of_first
      (n07aSmoothCanonicalMul_angularRegular χ hχ hχp (hu.mono (Nat.zero_le _))) hprod
    exact (ih χ hχ hχp ur hurreg).add
      (ih (mixedDerivative 1 0 χ) (contDiff_mixedDerivative hχ 1 0)
        (n07a_canonicalCoefficient_derivative_periodic hχp 1 0) u hureg)

end ContinuousFlexibility.Analysis
