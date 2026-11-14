module

public import ContinuousFlexibility.Analysis.N06CurrentTestTraces
public import ContinuousFlexibility.Analysis.N06NegativeCurrentTestLp
public import ContinuousFlexibility.Radial.RadialGreenBoundary

/-!
# AC Green calculus for the actual current test traces

The Lipschitz representatives constructed from N04 have the actual first
and second radial derivatives on the open interval. Their radial slices
are AC on the closed interval. The genuine AC Green formula therefore
applies against an H2 mode, with both endpoint values retained and with
the original transformed test in the bulk integrals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- Endpoints have zero Lebesgue measure, so an interior assertion holds
almost everywhere on the same closed interval. -/
theorem n06_ae_uIcc_of_forall_Ioo {a b : ℝ} (hab : a ≤ b) {P : ℝ → Prop}
    (hP : ∀ x ∈ Ioo a b, P x) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b → P x := by
  have hi : ∀ᵐ x ∂volume.restrict (Ioo a b), P x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hP x hx
  rw [restrict_Ioo_eq_restrict_Icc] at hi
  simpa only [uIcc_of_le hab] using (ae_restrict_iff' measurableSet_Icc).mp hi

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The closed value representative has the actual represented radial
jet at every interior radius, including the upper angular seam. -/
theorem N06CurrentHeightTestTraces.radial_deriv
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {y θ : ℝ}
    (hy : y ∈ Ioo (K.left m) (K.right m)) (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    deriv (fun t => P.value (t, θ)) y = P.radial (y, θ) := by
  have hW := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  have hdiff : DifferentiableAt ℝ (canonicalHeight S K z m φ) (y, θ) :=
    (hW.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hy, mem_univ _⟩)).differentiableAt (by simp)
  have he : (fun t => P.value (t, θ)) =ᶠ[𝓝 y]
      (fun t => canonicalHeight S K z m φ (t, θ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact P.value_eq ⟨ht, hθ⟩
  exact ((hasDerivAt_radialSlice hdiff).congr_of_eventuallyEq he).deriv.trans
    (P.radial_eq ⟨hy, hθ⟩).symm

/-- Differentiating the represented first radial jet gives the actual
second radial derivative of the open transformed test. -/
theorem N06CurrentHeightTestTraces.radial_second
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {y θ : ℝ}
    (hy : y ∈ Ioo (K.left m) (K.right m)) (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    deriv (fun t => P.radial (t, θ)) y =
      radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ) := by
  have hW := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  have hdiff : DifferentiableAt ℝ (radialPartial (canonicalHeight S K z m φ)) (y, θ) :=
    (contDiffAt_radialPartial (hW.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hy, mem_univ _⟩)) (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun t => P.radial (t, θ)) =ᶠ[𝓝 y]
      (fun t => radialPartial (canonicalHeight S K z m φ) (t, θ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact P.radial_eq ⟨ht, hθ⟩
  exact ((hasDerivAt_radialSlice hdiff).congr_of_eventuallyEq he).deriv

/-- The actual current physical test satisfies closed radial Green
against every genuine C1/AC mode. The boundary terms use the represented
jets, whose actual physical values were derived from N04. -/
theorem N06CurrentHeightTestTraces.radial_slice_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hvd : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) Real.pi) :
    (∫ y in K.left m..K.right m,
      deriv (deriv v) y * canonicalHeight S K z m φ (y, θ) -
        v y * radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ)) =
      (P.value (K.right m, θ) * deriv v (K.right m) -
        v (K.right m) * P.radial (K.right m, θ)) -
      (P.value (K.left m, θ) * deriv v (K.left m) -
        v (K.left m) * P.radial (K.left m, θ)) := by
  have hab : K.left m ≤ K.right m := (h04.1.referenceBounds m).2.1.le
  have hvalAC := n06_lipschitz_radial_slice_ac P.value_lipschitz θ (K.left m) (K.right m)
  have hradAC := n06_lipschitz_radial_slice_ac P.radial_lipschitz θ (K.left m) (K.right m)
  have hpu : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      P.radial (y, θ) = (1 : ℝ) * deriv (fun t => P.value (t, θ)) y :=
    n06_ae_uIcc_of_forall_Ioo hab (fun y hy => by
      rw [one_mul, P.radial_deriv h04 hz hs hφ hy hθ])
  have hpf : ∀ᵐ y ∂volume, y ∈ uIcc (K.left m) (K.right m) →
      deriv (fun t => P.radial (t, θ)) y =
        radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ) :=
    n06_ae_uIcc_of_forall_Ioo hab (fun y hy => P.radial_second h04 hz hs hφ hy hθ)
  have hg := integral_green_of_absolutelyContinuous_flux
    (w := fun _ => (1 : ℝ)) (u := fun y => P.value (y, θ)) (v := v)
    (p := fun y => P.radial (y, θ)) (q := deriv v)
    (f := fun y => radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ))
    (g := deriv (deriv v)) hvalAC hv.contDiffOn.absolutelyContinuousOnInterval hradAC hvd
    hpu (Eventually.of_forall (fun _ _ => (one_mul _).symm)) hpf
    (Eventually.of_forall (fun _ _ => rfl))
  calc
    _ = ∫ y in K.left m..K.right m,
        P.value (y, θ) * deriv (deriv v) y -
          v y * radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro y hy
      dsimp only
      rw [P.value_eq ⟨hy, hθ⟩, mul_comm (deriv (deriv v) y)]
    _ = _ := hg

end ContinuousFlexibility.Statements
