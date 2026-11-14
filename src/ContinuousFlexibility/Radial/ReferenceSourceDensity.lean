module

public import ContinuousFlexibility.Radial.ReferenceCosineConvergence
public import ContinuousFlexibility.Radial.ReferenceZeroMeanDensity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Density of smooth finite-mode reference sources

Angular orthogonal projections converge in the actual frozen weighted
measure. Each of their finitely many radial coefficients is then
approximated by a smooth compactly supported coefficient. The zero
coefficient keeps its ordinary integral exactly zero, while the scalar
border datum is kept exactly unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem norm_referenceAngularBasis_le_two (n : ℕ) (θ : ℝ) :
    ‖referenceAngularBasis n θ‖ ≤ 2 := by
  cases n with
  | zero => norm_num [referenceAngularBasis]
  | succ n =>
    change ‖Real.sqrt 2 * Real.cos (((2 * (n + 1) : ℕ) : ℝ) * θ)‖ ≤ 2
    rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs]
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)).trans
      (by simpa only [mul_one] using hsqrt)

theorem memLp_referenceRadial_basis {D : ReferenceData} {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) (n : ℕ) :
    MemLp (fun x : PolarPoint => f x.1 * referenceAngularBasis n x.2) 2
      (referenceWeightedMeasure D γ M) := by
  have hfl := memLp_referenceRadial_lift hf
  apply hfl.of_le_mul
    (hfl.aestronglyMeasurable.mul
      ((contDiff_referenceAngularBasis n).continuous.comp continuous_snd).aestronglyMeasurable)
  filter_upwards with x
  calc
    ‖f x.1 * referenceAngularBasis n x.2‖ =
        ‖referenceAngularBasis n x.2‖ * ‖f x.1‖ := by rw [norm_mul, mul_comm]
    _ ≤ 2 * ‖f x.1‖ :=
      mul_le_mul_of_nonneg_right (norm_referenceAngularBasis_le_two n x.2) (norm_nonneg _)

theorem norm_referenceRadial_basis_le_two {D : ReferenceData} {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) (n : ℕ) :
    ‖(memLp_referenceRadial_basis hf n).toLp
      (fun x : PolarPoint => f x.1 * referenceAngularBasis n x.2)‖ ≤
        2 * ‖hf.toLp f‖ := by
  let hfl := memLp_referenceRadial_lift hf
  have hnorm :
      ‖(memLp_referenceRadial_basis hf n).toLp
        (fun x : PolarPoint => f x.1 * referenceAngularBasis n x.2)‖ ≤
      2 * ‖hfl.toLp (fun x : PolarPoint => f x.1)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(memLp_referenceRadial_basis hf n).coeFn_toLp, hfl.coeFn_toLp]
      with x hx hy
    rw [hx, hy, norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_referenceAngularBasis_le_two n x.2)
      (norm_nonneg _)).trans_eq (mul_comm _ _)
  simpa only [hfl, norm_referenceRadial_lift hf] using hnorm

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Radial

/-- An arbitrary compatible source has a smooth compact finite-cosine
approximation of any prescribed positive Hilbert error. -/
theorem SourceMember.exists_smoothFinite_error_lt
    {D : ReferenceData} {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (hD : IsAccumulatingProfile D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : RadialSource, ReferenceSmoothFiniteSource D G ∧ G.2 = F.2 ∧
      SourceMember D γ M G ∧ sourceNormSquare D γ M (G - F) < ε ^ 2 := by
  classical
  have hgeom : RadialProfileGeometry D := by obtain ⟨C, hC⟩ := hD; exact hC.1
  have hpart : RadialPartition D := by obtain ⟨C, hC⟩ := hD; exact hC.2.1
  let hu := hF.memLp_weighted hgeom.2.1.le hpart
  have hproj := referenceCosineProjection_tendsto_L2 hpart hu hF.2.2.1 hF.2.2.2.1
  have herr := tendsto_iff_norm_sub_tendsto_zero.mp hproj
  obtain ⟨N, hN⟩ := ((tendsto_order.1 herr).2 _ (half_pos hε)).exists
  let c (n : ℕ) : ℝ → ℝ := referenceRadialCoefficient F.1 n
  have hc (n : ℕ) : MemLp (c n) 2 (referenceRadialWeightedMeasure D γ M) :=
    memLp_referenceRadialCoefficient hpart hu n
  let δ : ℝ := ε / (4 * ((N : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : ((N : ℝ) + 1) * (2 * δ) = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < (N : ℝ) + 1 by positivity)] <;> ring
  have happrox (n : ℕ) :
      ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        tsupport g ⊆ radialCore D ∧
        (n = 0 → (∫ r in D.a..D.b, g r) = 0) ∧
        ∃ hg : MemLp g 2 (referenceRadialWeightedMeasure D γ M),
          ‖hg.toLp g - (hc n).toLp (c n)‖ < δ := by
    cases n with
    | zero =>
      have hmean : c 0 = fun r => radialAngularMean (fun θ => F.1 (r, θ)) :=
        funext (fun r => referenceRadialCoefficient_zero F.1 r)
      have hi : IntervalIntegrable (c 0) volume D.a D.b := by
        rw [hmean]
        exact hF.2.2.2.2.1
      have hz : (∫ r in D.a..D.b, c 0 r) = 0 := by
        rw [hmean]
        exact hF.2.2.2.2.2
      obtain ⟨g, hg, hgc, hgs, hgz, hgm, hdist⟩ :=
        exists_referenceRadial_zeroMean_approximation hD (hc 0) hi hz hδ
      exact ⟨g, hg, hgc, hgs, fun _ => hgz, hgm, hdist⟩
    | succ n =>
      obtain ⟨g, hg, hgc, hgs, hgm, hdist⟩ :=
        exists_referenceRadial_smooth_approximation hD (hc (n + 1)) hδ
      exact ⟨g, hg, hgc, hgs, fun h => False.elim (Nat.succ_ne_zero n h), hgm, hdist⟩
  choose g hg hgc hgs hgzero hgm hgerr using happrox
  let G : RadialSource :=
    ⟨fun x => ∑ n ∈ Finset.range (N + 1),
      g n x.1 * referenceAngularBasis n x.2, F.2⟩
  have hGsmooth : ReferenceSmoothFiniteSource D G := by
    refine ⟨Finset.range N, g 0, fun n => g (n + 1),
      ⟨hg 0, hgc 0, hgs 0⟩, fun n _ => ⟨hg (n + 1), hgc (n + 1), hgs (n + 1)⟩,
      hgzero 0 rfl, ?_⟩
    intro r θ
    change (∑ n ∈ Finset.range (N + 1), g n r * referenceAngularBasis n θ) = _
    rw [Finset.sum_range_succ']
    simp only [referenceAngularBasis, mul_one]
    exact add_comm _ _
  have hG := hGsmooth.sourceMember hD γ M
  let hGμ := hG.memLp_weighted hgeom.2.1.le hpart
  let P := referenceCosineProjection (Finset.range N) F.1
  let hP := memLp_referenceCosineProjection hpart hu (Finset.range N)
  let e (n : ℕ) : ℝ → ℝ := g n - c n
  have he (n : ℕ) : MemLp (e n) 2 (referenceRadialWeightedMeasure D γ M) :=
    (hgm n).sub (hc n)
  let t (n : ℕ) : Lp ℝ 2 (referenceWeightedMeasure D γ M) :=
    (memLp_referenceRadial_basis (he n) n).toLp
      (fun x : PolarPoint => e n x.1 * referenceAngularBasis n x.2)
  have hPpoint (x : PolarPoint) :
      referenceCosineProjection (Finset.range N) F.1 x =
        ∑ n ∈ Finset.range (N + 1), c n x.1 * referenceAngularBasis n x.2 := by
    change angularCosineProjection (Finset.range N) (fun θ => F.1 (x.1, θ)) x.2 = _
    rw [angularCosineProjection_range_eq]
    rfl
  have hdiff :
      hGμ.toLp G.1 - hP.toLp P = ∑ n ∈ Finset.range (N + 1), t n := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (hGμ.toLp G.1) (hP.toLp P), hGμ.coeFn_toLp,
      hP.coeFn_toLp, Lp.coeFn_fun_finsetSum (Finset.range (N + 1)) t,
      ae_all_iff.mpr (fun n => (memLp_referenceRadial_basis (he n) n).coeFn_toLp)]
      with x hsub hgx hpx hsum ht
    rw [hsub]
    change (hGμ.toLp G.1 : PolarPoint → ℝ) x - (hP.toLp P : PolarPoint → ℝ) x =
      ((∑ n ∈ Finset.range (N + 1), t n : Lp ℝ 2 (referenceWeightedMeasure D γ M)) :
        PolarPoint → ℝ) x
    rw [hgx, hpx, hsum, hPpoint]
    change (∑ n ∈ Finset.range (N + 1), g n x.1 * referenceAngularBasis n x.2) -
      (∑ n ∈ Finset.range (N + 1), c n x.1 * referenceAngularBasis n x.2) =
      ∑ n ∈ Finset.range (N + 1), t n x
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [ht n]
    change g n x.1 * referenceAngularBasis n x.2 - c n x.1 * referenceAngularBasis n x.2 =
      (g n x.1 - c n x.1) * referenceAngularBasis n x.2
    ring
  have htbound (n : ℕ) : ‖t n‖ ≤ 2 * δ := by
    have heδ : ‖(he n).toLp (e n)‖ ≤ δ := by
      change ‖((hgm n).sub (hc n)).toLp (g n - c n)‖ ≤ δ
      rw [MemLp.toLp_sub (hgm n) (hc n)]
      exact (hgerr n).le
    exact (norm_referenceRadial_basis_le_two (he n) n).trans
      (mul_le_mul_of_nonneg_left heδ (by norm_num))
  have hfirst : ‖hGμ.toLp G.1 - hP.toLp P‖ ≤ ε / 2 := by
    rw [hdiff]
    calc
      ‖∑ n ∈ Finset.range (N + 1), t n‖ ≤
          ∑ n ∈ Finset.range (N + 1), ‖t n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range (N + 1), (2 : ℝ) * δ :=
        Finset.sum_le_sum (fun n _ => htbound n)
      _ = ε / 2 := by
        simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one] using hδeq
  have hlast : ‖hP.toLp P - hu.toLp F.1‖ < ε / 2 := hN
  have htotal : ‖hGμ.toLp G.1 - hu.toLp F.1‖ < ε := by
    calc
      ‖hGμ.toLp G.1 - hu.toLp F.1‖ ≤
          ‖hGμ.toLp G.1 - hP.toLp P‖ + ‖hP.toLp P - hu.toLp F.1‖ := by
            simpa only [dist_eq_norm] using
              dist_triangle (hGμ.toLp G.1) (hP.toLp P) (hu.toLp F.1)
      _ < ε := by linarith
  have hsub := referenceSource_sub hD hG hF
  have hsquare : sourceNormSquare D γ M (G - F) =
      ‖hGμ.toLp G.1 - hu.toLp F.1‖ ^ 2 := by
    change (F.2 - F.2) ^ 2 + (∑' m, sourceCellSquare D γ M (G.1 - F.1) m) = _
    rw [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
      ← integral_sq_referenceWeightedMeasure_eq (f := G.1 - F.1)
        hgeom.2.1.le hpart hsub.1 hsub.2.1,
      ← reference_memLp_norm_sq_eq_integral (hGμ.sub hu),
      MemLp.toLp_sub hGμ hu]
  refine ⟨G, hGsmooth, rfl, hG, ?_⟩
  rw [hsquare]
  nlinarith [norm_nonneg (hGμ.toLp G.1 - hu.toLp F.1)]

/-- Smooth compact finite even-cosine sources form a dense core for the
actual weighted source norm, with the scalar datum unchanged and exact
ordinary zero-mode compatibility at every term. -/
theorem SourceMember.exists_smoothFinite_approximation
    {D : ReferenceData} {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (hD : IsAccumulatingProfile D) :
    ∃ Fₙ : ℕ → RadialSource,
      (∀ n, ReferenceSmoothFiniteSource D (Fₙ n)) ∧
      (∀ n, (Fₙ n).2 = F.2) ∧
      (∀ n, SourceMember D γ M (Fₙ n)) ∧
      Tendsto (fun n => sourceNormSquare D γ M (Fₙ n - F)) atTop (𝓝 0) := by
  classical
  have happ (n : ℕ) := hF.exists_smoothFinite_error_lt hD
    (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
  choose Fₙ hsmooth hscalar hmember herror using happ
  refine ⟨Fₙ, hsmooth, hscalar, hmember, ?_⟩
  have hgeom : RadialProfileGeometry D := by obtain ⟨C, hC⟩ := hD; exact hC.1
  apply squeeze_zero (g := fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2)
  · intro n
    have hd := referenceSource_sub hD (hmember n) hF
    exact add_nonneg (sq_nonneg _) (tsum_nonneg (fun m =>
      sourceCellSquare_nonneg hgeom.2.1.le γ M hd.1 m))
  · exact fun n => (herror n).le
  · simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

end ContinuousFlexibility.Statements
