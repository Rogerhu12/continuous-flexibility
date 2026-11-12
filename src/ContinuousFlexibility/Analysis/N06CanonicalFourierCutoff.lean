import ContinuousFlexibility.Analysis.N06CylinderFourierCutoff

/-!
# Strong Fourier truncation of the exact canonical weak jet row

Every stored weak jet is approximated by the corresponding actual derivative
of one finite Fourier polynomial of the zeroth field. The convergence is in
the original canonical measure and the complete finite sum of L² jet norms.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_canonicalL2_memLp_prod
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) :
    MemLp (f : PolarPoint → ℝ) 2
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) :=
  (congrArg (fun μ : Measure PolarPoint => MemLp (f : PolarPoint → ℝ) 2 μ)
    (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mp (Lp.memLp f)

theorem n06_canonicalFourierCut_angularJet_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) (s : Finset ℤ) (j : ℕ) :
    MemLp (mixedDerivative 0 j (n06CylinderFourierCut s f)) 2 (canonicalMeasure S K m) :=
  (congrArg (fun μ : Measure PolarPoint =>
    MemLp (mixedDerivative 0 j (n06CylinderFourierCut s f)) 2 μ)
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr
        (n06CylinderFourierCut_angularJet_memLp (n06_canonicalL2_memLp_prod f) s j)

theorem n06_canonicalFourierCut_error_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) :
    Tendsto (fun N => ∫ p,
      (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2
        ∂canonicalMeasure S K m) atTop (𝓝 0) := by
  have h := n06CylinderFourierCut_error_tendsto (n06_canonicalL2_memLp_prod f)
  have heq (N : ℕ) :
      (∫ p, (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2
        ∂canonicalMeasure S K m) =
      ∫ p, (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2
        ∂(volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure :=
    congrArg (fun μ : Measure PolarPoint =>
      ∫ p, (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2 ∂μ)
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)
  exact h.congr' (Eventually.of_forall (fun N => (heq N).symm))

/-- Differentiating a cutoff of the original field agrees almost everywhere
with cutting off its stored weak derivative, in the same canonical measure. -/
theorem WeakCanonicalAngularDerivative.n06_fourierCut_angularJet_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    (s : Finset ℤ) (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) :
    mixedDerivative 0 j (n06CylinderFourierCut s f)
      =ᵐ[canonicalMeasure S K m] n06CylinderFourierCut s g := by
  let μ : Measure ℝ := volume.restrict (Ioo (K.left m) (K.right m))
  have hsymbols : ∀ᵐ r ∂μ, ∀ n : ℤ,
      circleFourierCoeff (fun θ => g (r, θ)) n =
        (2 * Complex.I * (n : ℂ)) ^ j * circleFourierCoeff (fun θ => f (r, θ)) n :=
    ae_all_iff.mpr (fun n => hfg.n06_fourierCoeff_ae n)
  have hsections : ∀ᵐ r ∂μ,
      (fun θ => mixedDerivative 0 j (n06CylinderFourierCut s f) (r, θ)) =ᵐ[angleMeasure]
        (fun θ => n06CylinderFourierCut s g (r, θ)) := by
    filter_upwards [hsymbols, n06_canonicalL2_angular_sections f,
      n06_canonicalL2_angular_sections g] with r hr hfr hgr
    have hcoeff (n : ℤ) :
        circleFourierCoeff (hgr.toLp (fun θ => g (r, θ))) n =
          (2 * Complex.I * (n : ℂ)) ^ j *
            circleFourierCoeff (hfr.toLp (fun θ => f (r, θ))) n := by
      rw [congrFun (circleFourierCoeff_congr_ae hgr.coeFn_toLp) n,
        congrFun (circleFourierCoeff_congr_ae hfr.coeFn_toLp) n]
      exact hr n
    have hcut := n06_circleFourierJetCut_eq_of_symbols s hs j hcoeff
    let hLj : MemLp (iteratedDeriv j (n06CircleFourierCut s (fun θ => f (r, θ)))) 2
        angleMeasure := memLp_angleMeasure_iteratedDeriv_of_contDiff
          (n06CircleFourierCut_contDiff s (fun θ => f (r, θ))) j
    let hL0 : MemLp (n06CircleFourierCut s (fun θ => g (r, θ))) 2 angleMeasure :=
      memLp_angleMeasure_of_continuous
        (n06CircleFourierCut_contDiff s (fun θ => g (r, θ))).continuous
    have hclass :
        hLj.toLp (iteratedDeriv j (n06CircleFourierCut s (fun θ => f (r, θ)))) =
          hL0.toLp (n06CircleFourierCut s (fun θ => g (r, θ))) := by
      calc
        _ = circleFourierJetCutFun s j (hfr.toLp (fun θ => f (r, θ))) :=
          n06CircleFourierCut_toLp hfr s j
        _ = circleFourierJetCutFun s 0 (hgr.toLp (fun θ => g (r, θ))) := hcut
        _ = _ := by
          simpa only [iteratedDeriv_zero] using (n06CircleFourierCut_toLp hgr s 0).symm
    have hae : iteratedDeriv j (n06CircleFourierCut s (fun θ => f (r, θ)))
        =ᵐ[angleMeasure] n06CircleFourierCut s (fun θ => g (r, θ)) := by
      calc
        _ =ᵐ[angleMeasure] (hLj.toLp
            (iteratedDeriv j (n06CircleFourierCut s (fun θ => f (r, θ)))) : ℝ → ℝ) :=
          hLj.coeFn_toLp.symm
        _ =ᵐ[angleMeasure]
            (hL0.toLp (n06CircleFourierCut s (fun θ => g (r, θ))) : ℝ → ℝ) :=
          Eventually.of_forall (fun θ => congrArg (fun v : AngleL2 => v θ) hclass)
        _ =ᵐ[angleMeasure] _ := hL0.coeFn_toLp
    simpa only [mixedDerivative, iteratedDeriv_zero, n06CylinderFourierCut] using hae
  have hprod : mixedDerivative 0 j (n06CylinderFourierCut s f)
      =ᵐ[μ.prod angleMeasure] n06CylinderFourierCut s g :=
    r11b_memLp_ae_eq_of_sections
      (n06CylinderFourierCut_angularJet_memLp (n06_canonicalL2_memLp_prod f) s j)
      (n06CylinderFourierCut_memLp (n06_canonicalL2_memLp_prod g) s) hsections
  exact (congrArg (fun ν : Measure PolarPoint =>
    mixedDerivative 0 j (n06CylinderFourierCut s f) =ᵐ[ν] n06CylinderFourierCut s g)
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr hprod

theorem WeakCanonicalAngularDerivative.n06_fourierCut_jet_error_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j) :
    Tendsto (fun N => ∫ p,
      (mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) f) p - g p) ^ 2
        ∂canonicalMeasure S K m) atTop (𝓝 0) := by
  have heq (N : ℕ) :
      (∫ p, (mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) f) p - g p) ^ 2
        ∂canonicalMeasure S K m) =
      ∫ p, (n06CylinderFourierCut (n06FourierCutoff N) g p - g p) ^ 2
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hfg.n06_fourierCut_angularJet_ae _ (n06FourierCutoff_neg N)] with p hp
    rw [hp]
  exact (n06_canonicalFourierCut_error_tendsto g).congr'
    (Eventually.of_forall (fun N => (heq N).symm))

/-- One finite Fourier cutoff of the zeroth canonical field reconstructs
the entire stored weak jet row in its exact sum of L² squared errors. -/
theorem n06_canonicalFourierCut_jetRow_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (v : Fin (b + 1) → CanonicalL2 S K m)
    (hv : ∀ k, WeakCanonicalAngularDerivative S K m (v 0) (v k) k.val) :
    ∃ hJ : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
        (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) 2
          (canonicalMeasure S K m),
      Tendsto (fun N => ∑ k : Fin (b + 1),
        ‖(hJ N k).toLp
          (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) - v k‖ ^ 2)
        atTop (𝓝 0) := by
  let hJ (N : ℕ) (k : Fin (b + 1)) :=
    n06_canonicalFourierCut_angularJet_memLp (v 0) (n06FourierCutoff N) k.val
  have hlim (k : Fin (b + 1)) : Tendsto (fun N =>
      ‖(hJ N k).toLp
        (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) - v k‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have heq (N : ℕ) :
        ‖(hJ N k).toLp
          (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) - v k‖ ^ 2 =
        ∫ p, (mixedDerivative 0 k.val
          (n06CylinderFourierCut (n06FourierCutoff N) (v 0)) p - v k p) ^ 2
            ∂canonicalMeasure S K m := by
      simpa only [Lp.toLp_coeFn] using r11b_norm_toLp_sub_sq (hJ N k) (Lp.memLp (v k))
    exact (hv k).n06_fourierCut_jet_error_tendsto.congr'
      (Eventually.of_forall (fun N => (heq N).symm))
  refine ⟨hJ, ?_⟩
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun k _ => hlim k)

end ContinuousFlexibility.Statements
