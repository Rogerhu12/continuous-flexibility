import ContinuousFlexibility.Analysis.N06NegativeWeakModes
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation
import ContinuousFlexibility.Analysis.N06MaterialJetRows

/-!
# The actual negative principal forcing has the original even symmetry

Reflection preserves the exact canonical half-period measure and commutes
with `d_yy - y d_theta_theta`. Therefore the weak equation of an even L2
height determines an even L2 forcing, by separation with the original
canonical test class. No symmetry of the actual potential is assumed.

For N05 the height's symmetry follows from its literal VolumeMember clause.
Consequently the forcing extracted from the same graph can be reconstructed
by the existing cosine cutoffs rather than only by their even projection.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private def angularReflectionEquiv : PolarPoint ≃ᵐ PolarPoint where
  toFun p := (p.1, Real.pi - p.2)
  invFun p := (p.1, Real.pi - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_const.sub measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_const.sub measurable_snd)

private theorem reflection_contDiff :
    ContDiff ℝ ∞ (fun p : PolarPoint => (p.1, Real.pi - p.2)) :=
  contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)

/-- Reflection exchanges the two factors of the transformed pairing.
This is the genuine measure-preserving change of variables, with no
regularity premise on either factor. -/
theorem n06_canonical_reflection_pairing
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f g : PolarPoint → ℝ) :
    (∫ p, f (p.1, Real.pi - p.2) * g p ∂canonicalMeasure S K m) =
      ∫ p, f p * g (p.1, Real.pi - p.2) ∂canonicalMeasure S K m := by
  have he := (n06_measurePreserving_canonicalAngularReflection
    (S := S) (K := K) (m := m)).integral_comp
    angularReflectionEquiv.measurableEmbedding
    (fun p : PolarPoint => f p * g (p.1, Real.pi - p.2))
  simpa only [angularReflectionEquiv, sub_sub_cancel, Prod.eta] using he

private theorem radialPartial_reflection {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    radialPartial (fun p : PolarPoint => φ (p.1, Real.pi - p.2)) =
      fun p => radialPartial φ (p.1, Real.pi - p.2) := by
  have hf := hφ.comp reflection_contDiff
  funext p
  have hleft : deriv (fun r => φ (r, Real.pi - p.2)) p.1 =
      radialPartial (fun q : PolarPoint => φ (q.1, Real.pi - q.2)) p := by
    simpa only [Function.comp_def] using
      deriv_cylinder_radial_slice (hf.differentiable (by simp)) p.1 p.2
  exact hleft.symm.trans
    (deriv_cylinder_radial_slice (hφ.differentiable (by simp)) p.1 (Real.pi - p.2))

private theorem angularPartial_reflection {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    angularPartial (fun p : PolarPoint => φ (p.1, Real.pi - p.2)) =
      fun p => -angularPartial φ (p.1, Real.pi - p.2) := by
  have hf := hφ.comp reflection_contDiff
  funext p
  have hleft : deriv (fun θ => φ (p.1, Real.pi - θ)) p.2 =
      angularPartial (fun q : PolarPoint => φ (q.1, Real.pi - q.2)) p := by
    simpa only [Function.comp_def] using
      deriv_cylinder_angular_slice (hf.differentiable (by simp)) p.1 p.2
  calc
    _ = deriv (fun θ => φ (p.1, Real.pi - θ)) p.2 := hleft.symm
    _ = -deriv (fun θ => φ (p.1, θ)) (Real.pi - p.2) :=
      deriv_comp_const_sub (fun θ => φ (p.1, θ)) Real.pi p.2
    _ = _ := congrArg Neg.neg
      (deriv_cylinder_angular_slice (hφ.differentiable (by simp)) p.1 (Real.pi - p.2))

private theorem angularPartial_fun_neg (f : PolarPoint → ℝ) :
    angularPartial (fun p => -f p) = fun p => -angularPartial f p := by
  funext p
  simp only [angularPartial, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

/-- The true negative principal test operator commutes with the actual
reflection, including both second derivatives. -/
theorem n06_negativePrincipal_reflection {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    n06NegativePrincipalTest (fun p : PolarPoint => φ (p.1, Real.pi - p.2)) =
      fun p => n06NegativePrincipalTest φ (p.1, Real.pi - p.2) := by
  have hrr : radialPartial (radialPartial
      (fun p : PolarPoint => φ (p.1, Real.pi - p.2))) =
      fun p => radialPartial (radialPartial φ) (p.1, Real.pi - p.2) := by
    rw [radialPartial_reflection hφ,
      radialPartial_reflection (contDiff_cylinder_radialPartial hφ)]
  have htt : angularPartial (angularPartial
      (fun p : PolarPoint => φ (p.1, Real.pi - p.2))) =
      fun p => angularPartial (angularPartial φ) (p.1, Real.pi - p.2) := by
    rw [angularPartial_reflection hφ, angularPartial_fun_neg,
      angularPartial_reflection (contDiff_cylinder_angularPartial hφ)]
    simp only [neg_neg]
  funext p
  simp only [n06NegativePrincipalTest, hrr, htt]

theorem n06_canonicalTest_reflection
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (fun p : PolarPoint => φ (p.1, Real.pi - p.2)) := by
  refine ⟨hφ.1.comp reflection_contDiff, ?_, ?_⟩
  · intro p
    have he := hφ.2.1 (p.1, -p.2)
    simp only [Prod.mk_add_mk, add_zero] at he
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    change φ (p.1, Real.pi - (p.2 + Real.pi)) = φ (p.1, Real.pi - p.2)
    rw [show Real.pi - (p.2 + Real.pi) = -p.2 by ring]
    rw [show -p.2 + Real.pi = Real.pi - p.2 by ring] at he
    exact he.symm
  · obtain ⟨J, hJ, hJsub, hzero⟩ := hφ.2.2
    exact ⟨J, hJ, hJsub, fun r hr θ => hzero r hr (Real.pi - θ)⟩

/-- Test separation transfers the even symmetry of the original height
to its actual principal forcing. -/
theorem n06_negative_principal_forcing_reflection
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U G : CanonicalL2 S K m)
    (hU : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
        ∫ p, G p * φ p ∂canonicalMeasure S K m) :
    (fun p : PolarPoint => G (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (G : PolarPoint → ℝ) := by
  let GR : CanonicalL2 S K m :=
    Lp.compMeasurePreserving (fun p : PolarPoint => (p.1, Real.pi - p.2))
      n06_measurePreserving_canonicalAngularReflection G
  have hGR : (GR : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => G (p.1, Real.pi - p.2) :=
    Lp.coeFn_compMeasurePreserving G n06_measurePreserving_canonicalAngularReflection
  have heq : GR = G := by
    apply n06_canonicalL2_test_ext
    intro φ hφ
    calc
      (∫ p, GR p * φ p ∂canonicalMeasure S K m) =
          ∫ p, G (p.1, Real.pi - p.2) * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hGR] with p hp
        rw [hp]
      _ = ∫ p, G p * φ (p.1, Real.pi - p.2) ∂canonicalMeasure S K m :=
        n06_canonical_reflection_pairing G φ
      _ = ∫ p, U p * n06NegativePrincipalTest
          (fun q : PolarPoint => φ (q.1, Real.pi - q.2)) p ∂canonicalMeasure S K m :=
        (hweak _ (n06_canonicalTest_reflection hφ)).symm
      _ = ∫ p, U p * n06NegativePrincipalTest φ (p.1, Real.pi - p.2)
          ∂canonicalMeasure S K m := by rw [n06_negativePrincipal_reflection hφ.1]
      _ = ∫ p, U (p.1, Real.pi - p.2) * n06NegativePrincipalTest φ p
          ∂canonicalMeasure S K m :=
        (n06_canonical_reflection_pairing U (n06NegativePrincipalTest φ)).symm
      _ = ∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hU] with p hp
        rw [hp]
      _ = ∫ p, G p * φ p ∂canonicalMeasure S K m := hweak φ hφ
  rw [heq] at hGR
  exact hGR.symm

/-- The literal zero-order VolumeMember clause of the same N05 graph
already gives reflection of every original height component. -/
theorem n06N05_height_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K V b}
    (h05 : N05Properties D T S C K V b B) (u : B.Space) (m : ℕ) :
    (fun p : PolarPoint => u.val.1.1 m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (u.val.1.1 m : PolarPoint → ℝ) := by
  have hV : IsVolumeModel T S K V := h05.2.1
  have hrel := (h05.2.2.2.2.2.2.1 u.val).mp u.property
  obtain ⟨W, hW⟩ := hrel.1
  have hgraph : W.val ∈ canonicalVolumeGraph S K 0 := by
    rw [← hV.1 (3 / 4 : ℝ) (-B.lossMaterial) 0]
    exact W.property
  have he := n06MaterialJetRow_reflection (T := T)
    (3 / 4 : ℝ) (-B.lossMaterial) W.val hgraph m
  rw [n06MaterialJetRow_zero_eq_forget hV (3 / 4 : ℝ) (-B.lossMaterial) 0 W m] at he
  rw [congrFun hW m] at he
  exact he

/-- Any L2 representative of the actual N05 negative principal forcing
has the necessary reflection symmetry. No separate potential or forcing
symmetry is assumed. -/
theorem n06N05_negative_principalSource_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false) (G : CanonicalL2 S K m)
    (hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06NegativePrincipalForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m) :
    (fun p : PolarPoint => G (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (G : PolarPoint → ℝ) := by
  apply n06_negative_principal_forcing_reflection (u.val.1.1 m) G
    (n06N05_height_reflection h.2 u m)
  intro φ hφ
  refine (n06N05_negative_principal_pairing hT hS h u m hm hφ).trans ?_
  apply integral_congr_ae
  filter_upwards [hG] with p hp
  rw [hp]

end ContinuousFlexibility.Analysis
