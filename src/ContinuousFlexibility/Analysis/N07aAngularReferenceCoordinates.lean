import ContinuousFlexibility.Analysis.N07aAngularPhysicalGraph
import ContinuousFlexibility.Statements.N07aCanonicalGeometry

/-!
# Angular projection through the actual reference coordinates

The reference chart preserves the angle.  Its actual Fréchet Jacobian is
therefore radial, as are the height and source multipliers.  Finite angular
projection commutes with the true coordinate transforms on their open
domains.  No commutation property of an inverse is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology

theorem n07a_planeJacobian_radial {a b : ℝ} {F : PolarPoint → PolarPoint}
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ univ))
    (hshape : ∀ p ∈ Ioo a b ×ˢ univ, F p = ((F (p.1, 0)).1, p.2))
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    planeJacobian F p = deriv (fun r => (F (r, 0)).1) p.1 := by
  let ρ : ℝ → ℝ := fun r => (F (r, 0)).1
  have hF₀ : ContDiffAt ℝ ∞ F (p.1, 0) :=
    (hF (p.1, 0) ⟨hp.1, mem_univ _⟩).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp.1, mem_univ _⟩)
  have hFρ : DifferentiableAt ℝ (fun r => F (r, 0)) p.1 :=
    (hF₀.differentiableAt (by simp)).comp p.1
      (differentiableAt_id.prodMk (differentiableAt_const (0 : ℝ)))
  have hρ : DifferentiableAt ℝ ρ p.1 := hFρ.fst
  have hD : HasFDerivAt (fun q : PolarPoint => (ρ q.1, q.2))
      ((deriv ρ p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have hr : HasFDerivAt (fun q : PolarPoint => ρ q.1)
        (deriv ρ p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      simpa only [Function.comp_def] using
        hρ.hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
    exact hr.prodMk hasFDerivAt_snd
  have he : F =ᶠ[𝓝 p] fun q : PolarPoint => (ρ q.1, q.2) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hshape q hq
  simp only [planeJacobian, (hD.congr_of_eventuallyEq he).fderiv,
    ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    mul_one, mul_zero, sub_zero, ρ]

theorem n07a_referenceBasisProjection_rowFormula (I : Finset ℕ)
    {f g : PolarPoint → ℝ} {r ρ A : ℝ}
    (hrow : ∀ θ, g (r, θ) = A * f (ρ, θ)) (θ : ℝ) :
    referenceBasisProjection I g (r, θ) = A * referenceBasisProjection I f (ρ, θ) := by
  have he : (fun α => g (r, α)) = fun α => A * f (ρ, α) := funext hrow
  simp only [referenceBasisProjection, angularBasisProjection, he,
    referenceAngularCoefficient_const_mul, Finset.mul_sum, mul_assoc]

theorem n07a_referenceBasisProjection_affineRow (I : Finset ℕ)
    {f g : PolarPoint → ℝ} {r ρ A c : ℝ}
    (hrow : ∀ θ, g (r, θ) = A * f (ρ, θ) + c)
    (hg : MemLp (fun θ => g (r, θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (θ : ℝ) :
    referenceBasisProjection I g (r, θ) =
      A * referenceBasisProjection I f (ρ, θ) + (if 0 ∈ I then c else 0) := by
  have hc : MemLp (fun _ : ℝ => c) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    memLp_referenceAngular_interval_of_continuous continuous_const
  have haf : MemLp (fun α => A * f (ρ, α)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (memLp_congr_ae (Eventually.of_forall fun α => by
      dsimp only [Pi.sub_apply]
      rw [hrow]
      ring)).mp (hg.sub hc)
  have he : (fun α => g (r, α)) = fun α => A * f (ρ, α) + c := funext hrow
  change angularBasisProjection I (fun α => g (r, α)) θ = _
  rw [he, angularBasisProjection_add haf hc I, n07a_angularBasisProjection_const]
  simp only [referenceBasisProjection, angularBasisProjection,
    referenceAngularCoefficient_const_mul, Finset.mul_sum, mul_assoc]

variable {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}

theorem n07a_reference_planeJacobian (hR : ReferenceRadial S C K) (m : ℕ)
    (hF : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    {r : ℝ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) (θ : ℝ) :
    planeJacobian (K.chart (C.referenceState, 0) m) (r, θ) =
      planeJacobian (K.chart (C.referenceState, 0) m) (r, 0) :=
  (n07a_planeJacobian_radial hF (fun p hp => (hR.1 m p hp).1)
    (p := (r, θ)) ⟨hr, mem_univ _⟩).trans
    (n07a_planeJacobian_radial hF (fun p hp => (hR.1 m p hp).1)
      (p := (r, 0)) ⟨hr, mem_univ _⟩).symm

theorem n07a_reference_inverseRadius_mem (_hR : ReferenceRadial S C K) (m : ℕ)
    (hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    {r : ℝ} (hr : r ∈ Ioo (K.left m) (K.right m)) :
    (K.inverseChart (C.referenceState, 0) m (r, 0)).1 ∈
      Ioo (K.physicalLeft m) (K.physicalRight m) :=
  (hmap ⟨hr, mem_univ _⟩).1

/-- The actual transformed height is a radial multiplier and radial pullback. -/
theorem n07a_canonicalHeight_reference_row (hR : ReferenceRadial S C K) (m : ℕ)
    (hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (u : PolarPoint → ℝ) {r : ℝ} (hr : r ∈ Ioo (K.left m) (K.right m)) (θ : ℝ) :
    canonicalHeight S K (C.referenceState, 0) m u (r, θ) =
      (K.height (C.referenceState, 0) m
        ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, 0))⁻¹ *
          u ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, θ) := by
  have hx := n07a_reference_inverseRadius_mem hR m hmap hr
  rw [canonicalHeight, hR.2 m (r, θ) ⟨hr, mem_univ _⟩]
  dsimp only
  rw [(hR.1 m ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, θ)
    ⟨hx, mem_univ _⟩).2, div_eq_mul_inv, mul_comm]

/-- The source formula uses the actual Jacobian, whose radiality is proved above. -/
theorem n07a_canonicalSource_reference_row (hR : ReferenceRadial S C K) (m : ℕ)
    (hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (hF : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (f : PolarPoint → ℝ) {r : ℝ} (hr : r ∈ Ioo (K.left m) (K.right m)) (θ : ℝ) :
    canonicalSource S K (C.referenceState, 0) m f (r, θ) =
      (K.height (C.referenceState, 0) m
        ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, 0) /
        |planeJacobian (K.chart (C.referenceState, 0) m)
          ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, 0)|) *
            f ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, θ) := by
  have hx := n07a_reference_inverseRadius_mem hR m hmap hr
  rw [canonicalSource, hR.2 m (r, θ) ⟨hr, mem_univ _⟩]
  dsimp only
  rw [(hR.1 m ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, θ)
    ⟨hx, mem_univ _⟩).2, n07a_reference_planeJacobian hR m hF hx θ]
  ring

theorem n07a_canonicalHeight_reference_projection (hR : ReferenceRadial S C K) (m : ℕ)
    (hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (u : PolarPoint → ℝ) (I : Finset ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    referenceBasisProjection I (canonicalHeight S K (C.referenceState, 0) m u) p =
      canonicalHeight S K (C.referenceState, 0) m (referenceBasisProjection I u) p := by
  rw [n07a_canonicalHeight_reference_row hR m hmap _ hp.1 p.2]
  exact n07a_referenceBasisProjection_rowFormula I
    (n07a_canonicalHeight_reference_row hR m hmap u hp.1) p.2

theorem n07a_canonicalSource_reference_projection (hR : ReferenceRadial S C K) (m : ℕ)
    (hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (hF : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (f : PolarPoint → ℝ) (I : Finset ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    referenceBasisProjection I (canonicalSource S K (C.referenceState, 0) m f) p =
      canonicalSource S K (C.referenceState, 0) m (referenceBasisProjection I f) p := by
  rw [n07a_canonicalSource_reference_row hR m hmap hF _ hp.1 p.2]
  exact n07a_referenceBasisProjection_rowFormula I
    (n07a_canonicalSource_reference_row hR m hmap hF f hp.1) p.2

end ContinuousFlexibility.Statements
