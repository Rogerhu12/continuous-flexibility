module

public import ContinuousFlexibility.Analysis.N06WeakDivergencePairing
public import ContinuousFlexibility.Analysis.N06CubicMultipliers
public import ContinuousFlexibility.Analysis.N06WeakFiniteGraph

/-!
# The genuine cubic perturbation paired with finite weak Fourier fields

The actual divergence on a compact radial test equals the pairing with
the same five cubic multipliers and the same weighted finite graph fields
already estimated in L2. The radial representatives need only C1, an AC
first derivative, and an L2 second derivative. Coefficients are smooth
only on the open unit strip.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_unitCubic_factor_partials {A : PolarPoint → ℝ} {p : PolarPoint}
    (hA : DifferentiableAt ℝ A p) :
    radialPartial (fun q => cylinderWeight q.1 ^ 3 * A q) p =
        cylinderWeight p.1 ^ 2 *
          (3 * (1 - 2 * p.1) * A p + cylinderWeight p.1 * radialPartial A p) ∧
      angularPartial (fun q => cylinderWeight q.1 ^ 3 * A q) p =
        cylinderWeight p.1 ^ 3 * angularPartial A p := by
  have hd : ContDiff ℝ ∞ (fun q : PolarPoint => cylinderWeight q.1) := by
    change ContDiff ℝ ∞ (fun q : PolarPoint => q.1 * (1 - q.1))
    exact contDiff_fst.mul (contDiff_const.sub contDiff_fst)
  have hdr : radialPartial (fun q => cylinderWeight q.1 ^ 3) p =
      3 * cylinderWeight p.1 ^ 2 * (1 - 2 * p.1) := by
    rw [← deriv_cylinder_radial_slice ((hd.pow 3).differentiable (by simp)) p.1 p.2]
    have hpow := ((cylinderWeight_hasDerivAt p.1).pow 3).deriv
    have heq : (cylinderWeight ^ 3 : ℝ → ℝ) =
        (fun y : ℝ => cylinderWeight y ^ 3) := by
      funext y
      rfl
    rw [heq] at hpow
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using hpow
  have hdt : angularPartial (fun q => cylinderWeight q.1 ^ 3) p = 0 := by
    rw [← deriv_cylinder_angular_slice ((hd.pow 3).differentiable (by simp)) p.1 p.2]
    exact (hasDerivAt_const p.2 (cylinderWeight p.1 ^ 3)).deriv
  constructor
  · rw [radialPartial_mul ((hd.pow 3).differentiable (by simp) p) hA, hdr]
    ring
  · rw [angularPartial_mul ((hd.pow 3).differentiable (by simp) p) hA, hdt,
      zero_mul, zero_add]

/-- The same weighted weak graph fields are exact radial multiples of the
six actual modal partial fields. -/
theorem n06_weakFiniteGraphFields_zero_eq (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (i : Fin 5) (p : PolarPoint) :
    n06WeakFiniteGraphFields s v 0 i p =
      ![cylinderWeight p.1 ^ 2 * n06FiniteMixedField s v 2 0 p,
        (cylinderWeight p.1 ^ 2 * Real.sqrt (cylinderWeight p.1)) *
          n06FiniteMixedField s v 1 1 p,
        cylinderWeight p.1 ^ 3 * n06FiniteMixedField s v 0 2 p,
        cylinderWeight p.1 * n06FiniteMixedField s v 1 0 p,
        (cylinderWeight p.1 * Real.sqrt (cylinderWeight p.1)) *
          n06FiniteMixedField s v 0 1 p] i := by
  fin_cases i <;> simp only [n06WeakFiniteGraphFields, n06WeakFiniteGraphCoefficients,
    n06WeakFiniteGraphShift, n06FiniteMixedField, r11bFiniteSynthesis,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Nat.zero_add, iteratedDeriv_succ, iteratedDeriv_zero, Finset.mul_sum]
  all_goals
    apply Finset.sum_congr rfl
    intro n _
    ring

theorem n06_finiteWeakCubic_expansion_eq_sum
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) {A B C : PolarPoint → ℝ} {p : PolarPoint}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    n06WeakDivergenceExpression
      (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
      (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
      (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
      (n06FiniteMixedField s v 0 2) p =
      ∑ i : Fin 5, n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
        n06WeakFiniteGraphFields s v 0 i p := by
  simp only [n06WeakDivergenceExpression, n06CubicCoefficients]
  rw [(n06_unitCubic_factor_partials hA).1, (n06_unitCubic_factor_partials hB).1,
    (n06_unitCubic_factor_partials hB).2, (n06_unitCubic_factor_partials hC).2]
  simp_rw [n06_weakFiniteGraphFields_zero_eq]
  simp only [n06CubicGraphMultipliers, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', add_zero]
  ring_nf
  simp only [Real.sq_sqrt (cylinderWeight_nonneg hp)]
  <;> ring

/-- The original formal test remains globally smooth despite the coefficient
being defined smoothly only in the open strip. -/
theorem n06_unit_divergence_test_contDiff (L : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ L.a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ L.b (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hc : ContDiffOn ℝ ∞ L.c (Ioo (0 : ℝ) 1 ×ˢ univ))
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    ContDiff ℝ ∞ (divergenceOperator L φ) := by
  have hr := (hφ.n06_radialPartial.n06_contDiff_mul_left ha).add
    (hφ.n06_angularPartial.n06_contDiff_mul_left hb)
  have ht := (hφ.n06_radialPartial.n06_contDiff_mul_left hb).add
    (hφ.n06_angularPartial.n06_contDiff_mul_left hc)
  exact (contDiff_cylinder_radialPartial hr).add (contDiff_cylinder_angularPartial ht)

/-- Exact finite-mode distributional realization of the five estimated
graph fields, with the same cubic multiplier convention and no new constants. -/
theorem n06_finite_weak_cubic_pairing
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC₁ : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)))
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (hφ : n06UnitCanonicalTest φ) :
    (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂cylinderWindowMeasure 0) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
          n06WeakFiniteGraphFields s v 0 i p) * φ p ∂cylinderWindowMeasure 0 := by
  have hd : ContDiff ℝ ∞ (fun q : PolarPoint => cylinderWeight q.1 ^ 3) := by
    change ContDiff ℝ ∞ (fun q : PolarPoint => (q.1 * (1 - q.1)) ^ 3)
    exact (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3
  have hper {F : PolarPoint → ℝ}
      (hF : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), F (p + (0, Real.pi)) = F p) :
      ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
        cylinderWeight (p + (0, Real.pi)).1 ^ 3 * F (p + (0, Real.pi)) =
          cylinderWeight p.1 ^ 3 * F p := by
    intro p hp
    simp only [Prod.fst_add, add_zero, hF p hp]
  have hrow := n06_finiteMixedField_weakH2 s v hC₁ hAC hv hv₁ hv₂
  have hpair := n06_unit_weak_divergence_pairing hrow
    (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
    (hd.contDiffOn.mul hA) (hd.contDiffOn.mul hB) (hd.contDiffOn.mul hC)
    (hper hpA) (hper hpB) (hper hpC) hφ
  calc
    _ = ∫ p, n06WeakDivergenceExpression
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
        (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
        (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
        (n06FiniteMixedField s v 0 2) p * φ p ∂cylinderWindowMeasure 0 := by
      simpa only [n06FiniteMixedField, iteratedDeriv_zero] using hpair
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [n06_unitOpen_ae] with p hp
      rw [n06_finiteWeakCubic_expansion_eq_sum s v
        ((hA.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp))
        ((hB.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp))
        ((hC.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp))
        (mem_Icc_of_Ioo hp.1)]

end ContinuousFlexibility.Analysis
