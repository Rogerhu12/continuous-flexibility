module

public import ContinuousFlexibility.Analysis.N06CurrentPositiveFiniteGreen

/-!
# Actual positive Green formulas with a C1 radial coefficient

The reference leading coefficient is the genuine C1 representative of
its open-cylinder values. Its ordinary derivative is continuous, so the
weighted test flux lies in L2 and its closed represented flux is absolutely
continuous. The same actual endpoint Green formulas therefore apply on
the original interval without requiring a smooth extension of that coefficient.
-/

@[expose] public section

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
theorem n06_currentHeight_weighted_radial_expansion_C1
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
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
theorem n06_currentHeight_weighted_radial_memLp_C1
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) :
    MemLp (radialPartial (fun q => a q.1 *
      radialPartial (canonicalHeight S K z m φ) q)) 2 (canonicalMeasure S K m) := by
  have hWr := (n06_current_canonicalHeight_directionalJets_memLp
    h04 hz hs m (1, 0) (1, 0) hφ).1
  have hWrr := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).1
  have hda : Continuous (deriv a) := ha.continuous_deriv le_rfl
  apply (memLp_congr_ae ?_).mpr
    ((n06_canonical_radialWeight_mul_memLp hda hWr).add
      (n06_canonical_radialWeight_mul_memLp ha.continuous hWrr))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact n06_currentHeight_weighted_radial_expansion_C1 h04 hz hs hφ ha
    ⟨hp.1, mem_univ _⟩

/-- A genuine represented flux has the same derivative as the open
weighted radial expression on every interior slice. -/
theorem N06CurrentHeightTestTraces.weighted_radial_deriv_C1
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    {y θ : ℝ} (hy : y ∈ Ioo (K.left m) (K.right m))
    (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    deriv (fun t => a t * P.radial (t, θ)) y =
      radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q)
        (y, θ) := by
  have hW : ContDiffAt ℝ ∞ (canonicalHeight S K z m φ) (y, θ) :=
    (n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hy, mem_univ θ⟩)
  have hWr := contDiffAt_radialPartial hW (m := ∞) (by simp)
  have had : DifferentiableAt ℝ (fun q : PolarPoint => a q.1) (y, θ) :=
    (ha.differentiable_one y).comp (y, θ) differentiableAt_fst
  have hd := had.mul (hWr.differentiableAt (by simp))
  have he : (fun t => a t * P.radial (t, θ)) =ᶠ[𝓝 y]
      (fun t => a t * radialPartial (canonicalHeight S K z m φ) (t, θ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    rw [P.radial_eq ⟨ht, hθ⟩]
  exact ((hasDerivAt_radialSlice hd).congr_of_eventuallyEq he).deriv

/-- Weighted radial Green retains the two actual endpoint fluxes. The
mode only needs C1 regularity and an AC first derivative. -/
theorem N06CurrentHeightTestTraces.weighted_radial_slice_green_C1
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a v : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
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
    ha.contDiffOn.absolutelyContinuousOnInterval
  have hpu : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      a y * P.radial (y, θ) = a y * deriv (fun t => P.value (t, θ)) y :=
    n06_ae_uIcc_of_forall_Ioo hab (fun y hy => by
      rw [P.radial_deriv h04 hz hs hφ hy hθ])
  have hpf : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      deriv (fun t => a t * P.radial (t, θ)) y =
        radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q)
          (y, θ) := n06_ae_uIcc_of_forall_Ioo hab
            (fun y hy => P.weighted_radial_deriv_C1 h04 hz hs hφ ha hy hθ)
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
theorem N06CurrentHeightTestTraces.tensor_weighted_radial_green_C1
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a v e : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
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
  have hfluxW := n06_currentHeight_weighted_radial_memLp_C1 h04 hz hs hφ ha (m := m)
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
    _ = _ := by rw [P.weighted_radial_slice_green_C1 h04 hz hs hφ ha hC hAC hθ]

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem integral_neg_sub_add {μ : Measure PolarPoint} {f g h : PolarPoint → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ p, -f p - g p + h p ∂μ) = -(∫ p, f p ∂μ) - (∫ p, g p ∂μ) + ∫ p, h p ∂μ := by
  have hneg : Integrable (fun p => -f p) μ := hf.neg
  have hsub : Integrable (fun p => -f p - g p) μ := hneg.sub hg
  rw [integral_add hsub hh, integral_sub hneg hg, integral_neg]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The positive radial-coefficient test operator is L2 on each actual
piece, by the true forward-chart test jet bounds. -/
theorem n06_currentHeight_positiveOperator_memLp_C1
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a c V : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V) :
    MemLp (n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ))
      2 (canonicalMeasure S K m) := by
  have hflux := n06_currentHeight_weighted_radial_memLp_C1 h04 hz hs hφ ha (m := m)
  have hθθ := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).2
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  exact (hflux.neg.sub (n06_canonical_radialWeight_mul_memLp hc hθθ)).add
    (n06_canonical_radialWeight_mul_memLp hV hW)

/-- One actual C1/AC radial mode satisfies the full positive Green
identity against a current physical test. The potential cancels exactly. -/
theorem N06CurrentHeightTestTraces.tensor_positive_green_C1
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {a c V v e : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hc : Continuous c) (hV : Continuous V) (hC : ContDiff ℝ 1 v)
    (hAC : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hflux : MemLp (deriv (fun y => a y * deriv v y)) 2
      (volume.restrict (Ioo (K.left m) (K.right m))))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e Real.pi) :
    (∫ p, (-deriv (fun y => a y * deriv v y) p.1 * e p.2 -
        (c p.1 * v p.1) * iteratedDeriv 2 e p.2 + (V p.1 * v p.1) * e p.2) *
          canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, (v p.1 * e p.2) *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ))) := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hfluxW := n06_currentHeight_weighted_radial_memLp_C1 h04 hz hs hφ ha (m := m)
  have hθθ := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).2
  have hcv := n06_interval_memLp_mul_continuous hv hc
  have hVv := n06_interval_memLp_mul_continuous hv hV
  have hA : Integrable (fun p : PolarPoint =>
      (deriv (fun y => a y * deriv v y) p.1 * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hflux he.continuous).integrable_mul hW
  have hB : Integrable (fun p : PolarPoint =>
      ((c p.1 * v p.1) * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hcv
        (circleFourier_contDiff_iteratedDeriv he 2).continuous).integrable_mul hW
  have hZ : Integrable (fun p : PolarPoint =>
      ((V p.1 * v p.1) * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hVv he.continuous).integrable_mul hW
  have hR : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hv he.continuous).integrable_mul hfluxW
  have hT : Integrable (fun p : PolarPoint => ((c p.1 * v p.1) * e p.2) *
      angularPartial (angularPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hcv he.continuous).integrable_mul hθθ
  have hleft :
      (∫ p, (-deriv (fun y => a y * deriv v y) p.1 * e p.2 -
          (c p.1 * v p.1) * iteratedDeriv 2 e p.2 + (V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      -(∫ p, (deriv (fun y => a y * deriv v y) p.1 * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, ((c p.1 * v p.1) * iteratedDeriv 2 e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) +
      ∫ p, ((V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
    rw [← integral_neg_sub_add hA hB hZ]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hright :
      (∫ p, (v p.1 * e p.2) *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      -(∫ p, (v p.1 * e p.2) * radialPartial (fun q => a q.1 *
        radialPartial (canonicalHeight S K z m φ) q) p ∂canonicalMeasure S K m) -
      (∫ p, ((c p.1 * v p.1) * e p.2) *
        angularPartial (angularPartial (canonicalHeight S K z m φ)) p
          ∂canonicalMeasure S K m) +
      ∫ p, ((V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
    rw [← integral_neg_sub_add hR hT hZ]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [n06UnitReferenceTestOperator]
    ring
  have hr := P.tensor_weighted_radial_green_C1 h04 hz hs hφ ha hC hAC hv hflux he.continuous
  have ht := n06_currentHeight_tensor_angular_green h04 hz hs hφ hφp hcv he hep
  have hsign : (∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)))) =
      -(∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)) -
        a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hleft, hright, hsign]
  linarith only [hr, ht]

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- Summing the genuine modal equations gives the finite positive Green
identity with its actual L2 forcing. Both endpoint derivatives are the
ordinary derivatives of the same finite C1 reconstruction. -/
theorem N06CurrentHeightTestTraces.finite_positive_green_C1
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V)
    (s : Finset ℕ) (v f : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s,
      AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      -deriv (fun t => a t * deriv (v i) t) y +
        (((2 * i : ℕ) : ℝ)) ^ 2 * c y * v i y + V y * v i y = f i y) :
    (∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * canonicalHeight S K z m φ p
      ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.left m) * (P.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) := by
  let Q (i : ℕ) (p : PolarPoint) : ℝ :=
    -deriv (fun t => a t * deriv (v i) t) p.1 * referenceAngularBasis i p.2 -
      (c p.1 * v i p.1) * iteratedDeriv 2 (referenceAngularBasis i) p.2 +
        (V p.1 * v i p.1) * referenceAngularBasis i p.2
  let U (i : ℕ) (p : PolarPoint) : ℝ := v i p.1 * referenceAngularBasis i p.2
  let B (i : ℕ) (θ : ℝ) : ℝ := referenceAngularBasis i θ *
    (a (K.left m) * (P.value (K.left m, θ) * deriv (v i) (K.left m) -
      v i (K.left m) * P.radial (K.left m, θ)) -
    a (K.right m) * (P.value (K.right m, θ) * deriv (v i) (K.right m) -
      v i (K.right m) * P.radial (K.right m, θ)))
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_positiveOperator_memLp_C1 h04 hz hs hφ ha hc hV (m := m)
  have hflux (i : ℕ) (hi : i ∈ s) :=
    n06_positive_modal_flux_memLp hc hV (hv i hi) (hf i hi) (hode i hi)
  have hQeq (i : ℕ) (hi : i ∈ s) : Q i =ᵐ[canonicalMeasure S K m]
      (fun p : PolarPoint => f i p.1 * referenceAngularBasis i p.2) := by
    have hp : ∀ᵐ p : PolarPoint ∂canonicalMeasure S K m,
        -deriv (fun t => a t * deriv (v i) t) p.1 +
          (((2 * i : ℕ) : ℝ)) ^ 2 * c p.1 * v i p.1 + V p.1 * v i p.1 = f i p.1 := by
      rw [n06_canonicalMeasure_eq_radial_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (hode i hi)
    filter_upwards [hp] with p hp
    dsimp only [Q]
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, iteratedDeriv_zero, deriv_deriv_referenceAngularBasis]
    linear_combination (referenceAngularBasis i p.2) * hp
  have hI (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p)
        (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp (hf i hi)
      (contDiff_referenceAngularBasis i).continuous).integrable_mul hW
  have hJ (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p)
        (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp (hv i hi)
      (contDiff_referenceAngularBasis i).continuous).integrable_mul hPW
  have hB (i : ℕ) : IntervalIntegrable (B i) volume 0 Real.pi := by
    have hvalr : Continuous (fun θ => P.value (K.right m, θ)) :=
      P.value_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hvall : Continuous (fun θ => P.value (K.left m, θ)) :=
      P.value_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hradr : Continuous (fun θ => P.radial (K.right m, θ)) :=
      P.radial_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hradl : Continuous (fun θ => P.radial (K.left m, θ)) :=
      P.radial_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((contDiff_referenceAngularBasis i).continuous.mul
      ((continuous_const.mul ((hvall.mul continuous_const).sub (continuous_const.mul hradl))).sub
        (continuous_const.mul ((hvalr.mul continuous_const).sub
          (continuous_const.mul hradr))))).intervalIntegrable _ _
  have he : ∀ i ∈ s, ContDiff ℝ 1 (referenceAngularBasis i) :=
    fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp)
  have hBpoint (θ : ℝ) : (∑ i ∈ s, B i θ) =
      a (K.left m) * (P.value (K.left m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) -
      a (K.right m) * (P.value (K.right m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) := by
    rw [n06_radialPartial_finiteSynthesis_one s v referenceAngularBasis hC he]
    simp only [B, r11bFiniteSynthesis, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hleft :
      (∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m := by
    simp only [r11bFiniteSynthesis, Finset.sum_mul]
    exact integral_finsetSum s hI
  have hright :
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m := by
    simp only [r11bFiniteSynthesis, Finset.sum_mul]
    exact integral_finsetSum s hJ
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ s, ∫ θ in (0 : ℝ)..Real.pi, B i θ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hg := P.tensor_positive_green_C1 h04 hz hs hφ hφp ha hc hV
        (hC i hi) (hAC i hi) (hv i hi) (hflux i hi)
        (contDiff_referenceAngularBasis i) (referenceAngularBasis_periodic i)
      have hforce : (∫ p, Q i p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
          ∫ p, (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p
            ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hQeq i hi] with p hp
        rw [hp]
      change (∫ p, Q i p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
        (∫ p, U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) = ∫ θ in (0 : ℝ)..Real.pi, B i θ at hg
      rw [hforce] at hg
      exact hg
    _ = ∫ θ in (0 : ℝ)..Real.pi, ∑ i ∈ s, B i θ :=
      (intervalIntegral.integral_finsetSum (fun i _ => hB i)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hBpoint θ

end ContinuousFlexibility.Statements
