import ContinuousFlexibility.Analysis.N06CurrentTestTensorGreen

/-!
# Weighted radial Green against the actual current test

The positive reference operator has a nonconstant radial coefficient.
Its boundary term is the weighted flux, not the ordinary derivative.
The actual current height test is smooth on the open strip and has the
closed Lipschitz traces constructed from the forward chart. Multiplying
its represented radial jet by the smooth radial weight gives an AC flux,
so the genuine closed Green formula applies without an endpoint inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual open radial flux has the usual product expansion. -/
theorem n06_currentHeight_weighted_radial_expansion
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q) p =
      deriv a p.1 * radialPartial (canonicalHeight S K z m φ) p +
        a p.1 * radialPartial (radialPartial (canonicalHeight S K z m φ)) p := by
  have hW := (n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  have hWr := contDiffAt_radialPartial hW (m := ∞) (by simp)
  have had : DifferentiableAt ℝ (fun q : PolarPoint => a q.1) p :=
    (ha.comp contDiff_fst).differentiable (by simp) p
  rw [radialPartial_mul had (hWr.differentiableAt (by simp))]
  rw [show radialPartial (fun q : PolarPoint => a q.1) p = deriv a p.1 from
    radialPartial_radialHeightField (ha.differentiable (by simp) p.1)]

/-- The weighted radial expression of the actual test is L2. Only fixed
piece bounds are used here; no uniform coefficient estimate is claimed. -/
theorem n06_currentHeight_weighted_radial_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    MemLp (radialPartial (fun q => a q.1 *
      radialPartial (canonicalHeight S K z m φ) q)) 2 (canonicalMeasure S K m) := by
  have hWr := (n06_current_canonicalHeight_directionalJets_memLp
    h04 hz hs m (1, 0) (1, 0) hφ).1
  have hWrr := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).1
  have hda : Continuous (deriv a) := by
    simpa only [iteratedDeriv_one] using
      (circleFourier_contDiff_iteratedDeriv ha 1).continuous
  apply (memLp_congr_ae ?_).mpr
    ((n06_canonical_radialWeight_mul_memLp hda hWr).add
      (n06_canonical_radialWeight_mul_memLp ha.continuous hWrr))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact n06_currentHeight_weighted_radial_expansion h04 hz hs hφ ha
    ⟨hp.1, mem_univ _⟩

/-- A genuine represented flux has the same derivative as the open
weighted radial expression on every interior slice. -/
theorem N06CurrentHeightTestTraces.weighted_radial_deriv
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    {y θ : ℝ} (hy : y ∈ Ioo (K.left m) (K.right m))
    (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    deriv (fun t => a t * P.radial (t, θ)) y =
      radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q)
        (y, θ) := by
  have hW : ContDiffAt ℝ ∞ (canonicalHeight S K z m φ) (y, θ) :=
    (n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hy, mem_univ θ⟩)
  have hWr := contDiffAt_radialPartial hW (m := ∞) (by simp)
  have hd := ((ha.comp contDiff_fst).contDiffAt.mul hWr).differentiableAt (by simp)
  have he : (fun t => a t * P.radial (t, θ)) =ᶠ[𝓝 y]
      (fun t => a t * radialPartial (canonicalHeight S K z m φ) (t, θ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    rw [P.radial_eq ⟨ht, hθ⟩]
  exact ((hasDerivAt_radialSlice hd).congr_of_eventuallyEq he).deriv

/-- Weighted radial Green retains the two actual endpoint fluxes. The
mode only needs C1 regularity and an AC first derivative. -/
theorem N06CurrentHeightTestTraces.weighted_radial_slice_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a v : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hv : ContDiff ℝ 1 v)
    (hvd : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    (∫ y in K.left m..K.right m,
      deriv (fun t => a t * deriv v t) y * canonicalHeight S K z m φ (y, θ) -
        v y * radialPartial (fun q => a q.1 *
          radialPartial (canonicalHeight S K z m φ) q) (y, θ)) =
      a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
        v (K.right m) * P.radial (K.right m, θ)) -
      a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
        v (K.left m) * P.radial (K.left m, θ)) := by
  have hab : K.left m ≤ K.right m := (h04.1.referenceBounds m).2.1.le
  have hvalAC := n06_lipschitz_radial_slice_ac P.value_lipschitz θ (K.left m) (K.right m)
  have hradAC := n06_lipschitz_radial_slice_ac P.radial_lipschitz θ (K.left m) (K.right m)
  have haAC : AbsolutelyContinuousOnInterval a (K.left m) (K.right m) :=
    (ha.of_le (show (1 : ℕ∞) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hpu : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      a y * P.radial (y, θ) = a y * deriv (fun t => P.value (t, θ)) y :=
    n06_ae_uIcc_of_forall_Ioo hab (fun y hy => by
      rw [P.radial_deriv h04 hz hs hφ hy hθ])
  have hpf : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      deriv (fun t => a t * P.radial (t, θ)) y =
        radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q)
          (y, θ) := n06_ae_uIcc_of_forall_Ioo hab
            (fun y hy => P.weighted_radial_deriv h04 hz hs hφ ha hy hθ)
  have hg := integral_green_of_absolutelyContinuous_flux
    (w := a) (u := fun y => P.value (y, θ)) (v := v)
    (p := fun y => a y * P.radial (y, θ)) (q := fun y => a y * deriv v y)
    (f := fun y => radialPartial (fun q => a q.1 *
      radialPartial (canonicalHeight S K z m φ) q) (y, θ))
    (g := deriv (fun y => a y * deriv v y))
    hvalAC hv.contDiffOn.absolutelyContinuousOnInterval (haAC.fun_mul hradAC)
    (haAC.fun_mul hvd) hpu (Eventually.of_forall (fun _ _ => rfl)) hpf
    (Eventually.of_forall (fun _ _ => rfl))
  calc
    _ = ∫ y in K.left m..K.right m,
        P.value (y, θ) * deriv (fun t => a t * deriv v t) y -
          v y * radialPartial (fun q => a q.1 *
            radialPartial (canonicalHeight S K z m φ) q) (y, θ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro y hy
      dsimp only
      rw [P.value_eq ⟨hy, hθ⟩, mul_comm (deriv (fun t => a t * deriv v t) y)]
    _ = _ := by rw [hg]; ring

/-- Fubini upgrades the true weighted radial slice identity to the
original canonical half-period measure. -/
theorem N06CurrentHeightTestTraces.tensor_weighted_radial_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a v e : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hC : ContDiff ℝ 1 v)
    (hAC : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hflux : MemLp (deriv (fun y => a y * deriv v y)) 2
      (volume.restrict (Ioo (K.left m) (K.right m)))) (he : Continuous e) :
    (∫ p, (deriv (fun y => a y * deriv v y) p.1 * e p.2) *
      canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, (v p.1 * e p.2) * radialPartial (fun q => a q.1 *
        radialPartial (canonicalHeight S K z m φ) q) p ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)) -
        a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ))) := by
  have hab : K.left m ≤ K.right m := (h04.1.referenceBounds m).2.1.le
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hfluxW := n06_currentHeight_weighted_radial_memLp h04 hz hs hφ ha (m := m)
  have hI : Integrable (fun p : PolarPoint =>
      (deriv (fun y => a y * deriv v y) p.1 * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hflux he).integrable_mul hW
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q) p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hv he).integrable_mul hfluxW
  rw [← integral_sub hI hJ]
  have hIJ : Integrable (fun p : PolarPoint =>
      (deriv (fun y => a y * deriv v y) p.1 * e p.2) * canonicalHeight S K z m φ p -
        (v p.1 * e p.2) * radialPartial (fun q => a q.1 *
          radialPartial (canonicalHeight S K z m φ) q) p)
      (canonicalMeasure S K m) := hI.sub hJ
  rw [n06_canonicalMeasure_eq_radial_prod] at hIJ ⊢
  rw [integral_prod_symm _ hIJ, intervalIntegral.integral_of_le Real.pi_pos.le]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change (∫ y in Ioo (K.left m) (K.right m),
    (deriv (fun t => a t * deriv v t) y * e θ) * canonicalHeight S K z m φ (y, θ) -
      (v y * e θ) * radialPartial (fun q => a q.1 *
        radialPartial (canonicalHeight S K z m φ) q) (y, θ)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  calc
    _ = e θ * (∫ y in K.left m..K.right m,
        deriv (fun t => a t * deriv v t) y * canonicalHeight S K z m φ (y, θ) -
          v y * radialPartial (fun q => a q.1 *
            radialPartial (canonicalHeight S K z m φ) q) (y, θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = _ := by rw [P.weighted_radial_slice_green h04 hz hs hφ ha hC hAC hθ]

end ContinuousFlexibility.Statements
