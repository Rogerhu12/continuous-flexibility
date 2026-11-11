import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Symmetry of the actual canonical source

The inverse chart inherits angular translation from the genuine chart
identities. Differentiating that local equivariance gives the same period
for the actual Jacobian. These facts prove periodicity and reflection of
the source formula on the canonical open piece. No property is asserted
about the arbitrary totalized inverse outside that piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology

/-- Local translation equivariance makes the actual Jacobian translation
invariant. Totalized derivatives suffice; no extra differentiability
assumption is needed. -/
theorem n07b_planeJacobian_add_of_equivariantOn
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → PolarPoint}
    {v c : PolarPoint} (hF : ∀ x ∈ U, F (x + v) = F x + c)
    {p : PolarPoint} (hp : p ∈ U) :
    planeJacobian F (p + v) = planeJacobian F p := by
  have he : (fun x => F (x + v)) =ᶠ[𝓝 p] (fun x => F x + c) :=
    (hU.mem_nhds hp).mono fun x hx => hF x hx
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_add_right, fderiv_add_const] at hd
  simp only [planeJacobian, hd]

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  (hK : Blueprint.N04PartA D S C K base ε)
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)

include hK hz hsector

theorem n07b_canonicalInverse_add (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
  have hc := hK.2.2.2.2.2.2.2.1 z hz hsector m
  exact inverseChart_periodic_of_chart_periodic hc.2.1 hc.2.2.1 hc.2.2.2.1
    (fun x hx => (hc.2.2.2.2.2.2.2 x hx).2.2.1) hp

theorem n07b_canonicalJacobian_add (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    planeJacobian (K.chart z m) (p + (0, Real.pi)) =
      planeJacobian (K.chart z m) p := by
  have hc := hK.2.2.2.2.2.2.2.1 z hz hsector m
  exact n07b_planeJacobian_add_of_equivariantOn
    (show IsOpen (physicalPieceOpen S K m) from isOpen_Ioo.prod isOpen_univ)
    (fun x hx => (hc.2.2.2.2.2.2.2 x hx).2.2.1) hp

/-- The actual source transformation preserves angular translation on its
canonical piece. -/
theorem n07b_canonicalSource_add (f : PolarPoint → ℝ)
    (hf : Function.Periodic f (0, Real.pi)) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p + (0, Real.pi)) = canonicalSource S K z m f p := by
  have hc := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hx := hc.2.1 hp
  have hh := (hc.2.2.2.2.2.2.2 (K.inverseChart z m p) hx).2.2.2
  simp only [canonicalSource]
  rw [n07b_canonicalInverse_add hK hz hsector m hp, hh, hf,
    n07b_canonicalJacobian_add hK hz hsector m hx]

/-- At every interior canonical radius the actual source is a genuine
periodic function of the angular variable. -/
theorem n07b_canonicalSource_periodic (f : PolarPoint → ℝ)
    (hf : Function.Periodic f (0, Real.pi)) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (K.left m) (K.right m)) :
    Function.Periodic (fun θ => canonicalSource S K z m f (r, θ)) Real.pi := by
  intro θ
  have h := n07b_canonicalSource_add hK hz hsector f hf m
    (show (r, θ) ∈ canonicalOpen S K m from ⟨hr, mem_univ _⟩)
  simpa only [Prod.mk_add_mk, add_zero] using h

/-- Reflection follows from the actual inverse, height, and Jacobian
identities in PartA. -/
theorem n07b_canonicalSource_neg (f : PolarPoint → ℝ)
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p.1, -p.2) = canonicalSource S K z m f p := by
  have hc := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hx := hc.2.1 hp
  have hs := hK.2.2.2.2.2.2.2.2.2.1 z hz hsector m (K.inverseChart z m p) hx
  have hi := hK.2.2.2.2.2.2.2.2.2.2 z hz hsector m p hp
  simp only [canonicalSource]
  rw [hi, hs.2.1, hs.2.2, hf]

/-- The reflection used in the canonical weak jet graph is `π - θ`. -/
theorem n07b_canonicalSource_reflection (f : PolarPoint → ℝ)
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi)) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p.1, Real.pi - p.2) = canonicalSource S K z m f p := by
  calc
    canonicalSource S K z m f (p.1, Real.pi - p.2) =
        canonicalSource S K z m f (p.1, -p.2 + Real.pi) :=
      congrArg (fun θ => canonicalSource S K z m f (p.1, θ)) (by ring)
    _ = canonicalSource S K z m f (p.1, -p.2) :=
      n07b_canonicalSource_periodic hK hz hsector f hperiod m hp.1 (-p.2)
    _ = canonicalSource S K z m f p := n07b_canonicalSource_neg hK hz hsector f heven m hp

theorem n07b_canonicalSource_reflection_ae (f : PolarPoint → ℝ)
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi)) (m : ℕ) :
    (fun p : PolarPoint => canonicalSource S K z m f (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f := by
  have hm : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hm] with p hp
  exact n07b_canonicalSource_reflection hK hz hsector f heven hperiod m
    ⟨hp.1, mem_univ _⟩

/-- In particular, every actual physical source supplies the reflection
input of the canonical source lift without an additional symmetry hypothesis. -/
theorem n07b_physicalSource_canonical_reflection_ae {T : MaterialData}
    (hS : IsPhysicalSpaces D T S) (f : S.Source) (m : ℕ) :
    (fun p : PolarPoint => canonicalSource S K z m
      ((S.height (3 / 4 : ℝ)).decode f.val) (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  have hf := (hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val
  exact n07b_canonicalSource_reflection_ae hK hz hsector _ hf.2.1 hf.2.2.1 m

end ContinuousFlexibility.Analysis
