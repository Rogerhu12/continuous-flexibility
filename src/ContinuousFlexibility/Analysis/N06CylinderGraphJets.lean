module

public import ContinuousFlexibility.Analysis.N06AngularJetParseval
public import ContinuousFlexibility.Analysis.N06CylinderLp
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# The positive-cylinder graph bound at the fixed angular source order

Actual angular differentiation commutes with the two coordinate partials.
The scalar mode estimate can therefore be summed with the genuine finite
jet weight. Its constant is independent of the number of Fourier modes
and of the fixed angular order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_radialPartial_angularJet {U : PolarPoint → ℝ}
    (hU : ContDiff ℝ ∞ U) (k : ℕ) :
    radialPartial (mixedDerivative 0 k U) = mixedDerivative 0 k (radialPartial U) := by
  rw [radialPartial_mixedDerivative hU]
  funext p
  exact (mixedDerivative_radialPartial isOpen_univ hU.contDiffOn 0 k (mem_univ p)).symm

theorem n06_angularPartial_angularJet {U : PolarPoint → ℝ}
    (hU : ContDiff ℝ ∞ U) (k : ℕ) :
    angularPartial (mixedDerivative 0 k U) = mixedDerivative 0 k (angularPartial U) := by
  rw [angularPartial_mixedDerivative hU]
  funext p
  exact (mixedDerivative_angularPartial isOpen_univ hU.contDiffOn 0 k (mem_univ p)).symm

/-- Every radial multiplier commutes with pure angular jets, including
the square-root weights at a degenerate endpoint. -/
theorem n06_angularJet_radial_mul (a : ℝ → ℝ) (U : PolarPoint → ℝ) (k : ℕ) :
    mixedDerivative 0 k (fun p => a p.1 * U p) =
      fun p => a p.1 * mixedDerivative 0 k U p := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero]
  exact iteratedDeriv_const_mul_field _ _

/-- The jets used by coefficient multiplication are precisely the graph
fields controlled by the fixed-order estimate. No endpoint differentiability
of the radial weights is required. -/
theorem n06_cubicGraphFields_angularJet_commute (d : ℝ → ℝ)
    {U : PolarPoint → ℝ} (hU : ContDiff ℝ ∞ U) (k : ℕ) (i : Fin 5) :
    mixedDerivative 0 k (n06CubicGraphFields (fun p => d p.1) U i) =
      n06CubicGraphFields (fun p => d p.1) (mixedDerivative 0 k U) i := by
  have hr := contDiff_cylinder_radialPartial hU
  have ht := contDiff_cylinder_angularPartial hU
  fin_cases i <;>
    simp only [n06CubicGraphFields, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ']
  · rw [n06_angularJet_radial_mul (fun y => d y ^ 2)
      (radialPartial (radialPartial U)) k]
    simp only [n06_radialPartial_angularJet hU k, n06_radialPartial_angularJet hr k]
  · rw [n06_angularJet_radial_mul (fun y => d y ^ 2 * Real.sqrt (d y))
      (angularPartial (radialPartial U)) k]
    simp only [n06_radialPartial_angularJet hU k, n06_angularPartial_angularJet hr k]
  · rw [n06_angularJet_radial_mul (fun y => d y ^ 3)
      (angularPartial (angularPartial U)) k]
    simp only [n06_angularPartial_angularJet hU k, n06_angularPartial_angularJet ht k]
  · rw [n06_angularJet_radial_mul d (radialPartial U) k]
    simp only [n06_radialPartial_angularJet hU k]
  · rw [n06_angularJet_radial_mul (fun y => d y * Real.sqrt (d y)) (angularPartial U) k]
    simp only [n06_angularPartial_angularJet hU k]

theorem n06_angularJet_periodic {U : PolarPoint → ℝ}
    (hp : Function.Periodic U (0, Real.pi)) (k : ℕ) :
    Function.Periodic (mixedDerivative 0 k U) (0, Real.pi) := by
  have hs (y : ℝ) : Function.Periodic (fun θ => U (y, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hp (y, θ)
  rintro ⟨y, θ⟩
  simpa only [Prod.mk_add_mk, add_zero] using
    mixedDerivative_angular_periodic hs 0 k y θ

theorem n06_continuous_angularJet_finiteSynthesis {ι : Type*}
    (s : Finset ι) (u e : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i)) (k : ℕ) :
    Continuous (mixedDerivative 0 k (r11bFiniteSynthesis s u e)) := by
  rw [n06_mixedAngularDerivative_finiteSynthesis s u e he k]
  exact continuous_finsetSum s (fun i hi => ((hu i hi).comp continuous_fst).mul
    ((circleFourier_contDiff_iteratedDeriv (he i hi) k).continuous.comp continuous_snd))

/-- A constant multiplier on each mode factors out of every actual
angular-jet square integral. -/
theorem n06CylinderSquare_angularJet_finite_multiplier {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν A : ι → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (a k : ℕ) :
    n06CylinderSquare a
        (mixedDerivative 0 k (r11bFiniteSynthesis s (fun i y => A i * u i y) e)) =
      ∑ i ∈ s, ν i ^ (2 * k) * A i ^ 2 *
        (∫ y in (0 : ℝ)..1, cylinderWeight y ^ a * u i y ^ 2) := by
  rw [n06CylinderSquare_angularJet_finite s (fun i y => A i * u i y) e o ν
    (fun i hi => continuous_const.mul (hu i hi)) he heorth hoorth hde hdo a k]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ a * (A i * u i y) ^ 2) =
      A i ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ a * u i y ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hi]
  ring

/-- The graph square of an actual angular derivative is the modal graph
square multiplied by the corresponding frequency weight. -/
theorem n06CylinderGraphSquare_angularJet_finite {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (ho : ∀ i ∈ s, ContDiff ℝ ∞ (o i))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (k : ℕ) :
    n06CylinderGraphSquare (mixedDerivative 0 k (r11bFiniteSynthesis s u e)) =
      ∑ i ∈ s, ν i ^ (2 * k) *
        ((∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (u i) y) ^ 2) +
          (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u i y ^ 2) +
          (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (u i)) y) ^ 2) +
          (1 + ν i ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * u i y ^ 2) +
          (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv (u i) y ^ 2)) := by
  have hU := n06_contDiff_finiteSynthesis s u e hu he
  have hUr := contDiff_cylinder_radialPartial hU
  have hUt := contDiff_cylinder_angularPartial hU
  have hu₁ (i : ι) (hi : i ∈ s) : ContDiff ℝ ∞ (deriv (u i)) :=
    (contDiff_infty_iff_deriv.mp (hu i hi)).2
  have hu₂ (i : ι) (hi : i ∈ s) : ContDiff ℝ ∞ (deriv (deriv (u i))) :=
    (contDiff_infty_iff_deriv.mp (hu₁ i hi)).2
  have hr := n06_radialPartial_finiteSynthesis s u e hu he
  have hrr : radialPartial (radialPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i => deriv (deriv (u i))) e := by
    rw [hr, n06_radialPartial_finiteSynthesis s _ e hu₁ he]
  have ht := n06_angularPartial_finiteSynthesis s u e o ν hu he hde
  have htt : angularPartial (angularPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i y => (-ν i ^ 2) * u i y) e := by
    rw [ht, n06_angularPartial_finiteSynthesis s _ o e (fun i => -ν i)
      (fun i hi => contDiff_const.mul (hu i hi)) ho hdo]
    funext p
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrt : angularPartial (radialPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i y => ν i * deriv (u i) y) o := by
    rw [hr, n06_angularPartial_finiteSynthesis s _ e o ν hu₁ he hde]
  have hde' : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (-(-ν i) * o i θ) θ := by
    simpa only [neg_neg] using hde
  unfold n06CylinderGraphSquare
  simp only [n06_radialPartial_angularJet hU k, n06_angularPartial_angularJet hU k,
    n06_radialPartial_angularJet hUr k, n06_angularPartial_angularJet hUr k,
    n06_angularPartial_angularJet hUt k]
  rw [hrr, htt, hrt]
  simp only [ht, hr]
  rw [n06CylinderSquare_angularJet_finite s _ e o ν
      (fun i hi => (hu₁ i hi).continuous) he heorth hoorth hde hdo 2 k,
    n06CylinderSquare_angularJet_finite s u e o ν
      (fun i hi => (hu i hi).continuous) he heorth hoorth hde hdo 3 k,
    n06CylinderSquare_angularJet_finite_multiplier s u o e (fun i => -ν i) ν
      (fun i hi => (hu i hi).continuous) ho hoorth heorth hdo hde' 3 k,
    n06CylinderSquare_angularJet_finite s _ e o ν
      (fun i hi => (hu₂ i hi).continuous) he heorth hoorth hde hdo 4 k,
    n06CylinderSquare_angularJet_finite s u e o ν
      (fun i hi => (hu i hi).continuous) he heorth hoorth hde hdo 6 k,
    n06CylinderSquare_angularJet_finite_multiplier s u o e (fun i => -ν i) ν
      (fun i hi => (hu i hi).continuous) ho hoorth heorth hdo hde' 6 k,
    n06CylinderSquare_angularJet_finite_multiplier s u e o ν (fun i => -ν i ^ 2)
      (fun i hi => (hu i hi).continuous) he heorth hoorth hde hdo 6 k,
    n06CylinderSquare_angularJet_finite s _ e o ν
      (fun i hi => (hu₁ i hi).continuous) he heorth hoorth hde hdo 5 k,
    n06CylinderSquare_angularJet_finite_multiplier s _ o e (fun i => -ν i) ν
      (fun i hi => (hu₁ i hi).continuous) ho hoorth heorth hdo hde' 5 k]
  simp only [(even_two_mul k).neg_pow, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hfirst : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * deriv (u i) y ^ 2) =
      ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (u i) y) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hsecond :
      (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 4 * deriv (deriv (u i)) y ^ 2) =
      ∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (u i)) y) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hfirst, hsecond]
  ring

/-- The graph square at the fixed angular source order. -/
def n06CylinderGraphJetSquare (b : ℕ) (U : PolarPoint → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), n06CylinderGraphSquare (mixedDerivative 0 k U)

/-- The actual finite angular-jet graph estimate, with no derivative
loss and no dependence of the constant on the angular cutoff. -/
theorem n06_finite_cylinder_graph_jet_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u F e o : ι → ℝ → ℝ) (ν : ι → ℝ) (b : ℕ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ν i ^ 2 * c y * u i y + V y * u i y)
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (ho : ∀ i ∈ s, ContDiff ℝ ∞ (o i))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    n06CylinderGraphJetSquare b (r11bFiniteSynthesis s u e) ≤
      16384 * K ^ 10 *
        (n06CylinderJetSquare b (r11bFiniteSynthesis s F e) +
          n06CylinderJetSquare b (r11bFiniteSynthesis s u e)) := by
  have hu₂ (i : ι) (hi : i ∈ s) : ContDiff ℝ 2 (u i) :=
    (hu i hi).of_le (by simp)
  have hFc (i : ι) (hi : i ∈ s) : Continuous (F i) :=
    continuous_forcing ha (hu₂ i hi) hc hV (hF i hi)
  unfold n06CylinderGraphJetSquare
  simp_rw [n06CylinderGraphSquare_angularJet_finite s u e o ν
    hu he ho heorth hoorth hde hdo]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [n06CylinderJetSquare_finite s F e o ν hFc he heorth hoorth hde hdo,
    n06CylinderJetSquare_finite s u e o ν (fun i hi => (hu i hi).continuous)
      he heorth hoorth hde hdo]
  have hw (i : ι) (_hi : i ∈ s) :
      0 ≤ ∑ k ∈ Finset.range (b + 1), ν i ^ (2 * k) :=
    Finset.sum_nonneg (fun k _ => (even_two_mul k).pow_nonneg (ν i))
  have h := n06_finite_weighted_graph_sum s u F ν
    (fun i => ∑ k ∈ Finset.range (b + 1), ν i ^ (2 * k))
    ha hu₂ hc hV hq hF hw hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  simpa only [mul_add, Finset.sum_add_distrib] using h

/-- The actual finite angular-jet L² norm has exactly the normalization
used in the finite Parseval estimate. -/
theorem n06_angularJet_lp_norm_sq_sum {U : PolarPoint → ℝ}
    (hp : Function.Periodic U (0, Real.pi))
    (hU : ∀ k, Continuous (mixedDerivative 0 k U))
    (hLp : ∀ k, MemLp (mixedDerivative 0 k U) 2 (cylinderWindowMeasure 0)) (b : ℕ) :
    (∑ k ∈ Finset.range (b + 1),
      ‖(hLp k).toLp (mixedDerivative 0 k U)‖ ^ 2) =
        Real.pi * n06CylinderJetSquare b U := by
  calc
    _ = ∑ k ∈ Finset.range (b + 1),
        Real.pi * n06CylinderSquare 0 (mixedDerivative 0 k U) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [r11b_norm_toLp_sq]
      simpa only [pow_zero, one_mul] using
        n06_weighted_integral_eq_pi_mul_square 0 _ (hU k) (n06_angularJet_periodic hp k)
    _ = _ := by rw [n06CylinderJetSquare, Finset.mul_sum]

/-- Each actual angular jet supplies the same five weighted L² fields. -/
theorem n06_cubicGraphFields_angularJet_memLp {U : PolarPoint → ℝ}
    (hU : ContDiff ℝ ∞ U) (k : ℕ) (i : Fin 5) :
    MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
      (mixedDerivative 0 k U) i) 2 (cylinderWindowMeasure 0) :=
  n06_cubicGraphFields_memLp (contDiff_mixedDerivative hU 0 k) i

/-- The graph-jet estimate directly controls the sum of the five actual
L² graph fields at every source angular order. -/
theorem n06_cubicGraphFields_angularJet_lp_bound
    {U F : PolarPoint → ℝ} {b : ℕ} {C : ℝ}
    (hU : ContDiff ℝ ∞ U) (hpU : Function.Periodic U (0, Real.pi))
    (hpF : Function.Periodic F (0, Real.pi))
    (hF : ∀ k, Continuous (mixedDerivative 0 k F))
    (hULp : ∀ k, MemLp (mixedDerivative 0 k U) 2 (cylinderWindowMeasure 0))
    (hFLp : ∀ k, MemLp (mixedDerivative 0 k F) 2 (cylinderWindowMeasure 0))
    (hgraph : ∀ k i, MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
      (mixedDerivative 0 k U) i) 2 (cylinderWindowMeasure 0))
    (hbound : n06CylinderGraphJetSquare b U ≤
      C * (n06CylinderJetSquare b F + n06CylinderJetSquare b U)) :
    (∑ k ∈ Finset.range (b + 1), ∑ i,
      ‖(hgraph k i).toLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
        (mixedDerivative 0 k U) i)‖ ^ 2) ≤
      C * ((∑ k ∈ Finset.range (b + 1),
          ‖(hFLp k).toLp (mixedDerivative 0 k F)‖ ^ 2) +
        ∑ k ∈ Finset.range (b + 1), ‖(hULp k).toLp (mixedDerivative 0 k U)‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (b + 1),
        Real.pi * n06CylinderGraphSquare (mixedDerivative 0 k U) := by
      apply Finset.sum_le_sum
      intro k _
      exact n06_cubicGraphFields_norm_sq_le_graph (contDiff_mixedDerivative hU 0 k)
        (n06_angularJet_periodic hpU k) (hgraph k)
    _ = Real.pi * n06CylinderGraphJetSquare b U := by
      rw [n06CylinderGraphJetSquare, Finset.mul_sum]
    _ ≤ Real.pi * (C * (n06CylinderJetSquare b F + n06CylinderJetSquare b U)) :=
      mul_le_mul_of_nonneg_left hbound Real.pi_pos.le
    _ = _ := by
      rw [n06_angularJet_lp_norm_sq_sum hpF hF hFLp,
        n06_angularJet_lp_norm_sq_sum hpU
          (fun k => (contDiff_mixedDerivative hU 0 k).continuous) hULp]
      ring

end ContinuousFlexibility.Analysis
