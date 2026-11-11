import ContinuousFlexibility.Analysis.N06ReferenceWeakIdentity
import ContinuousFlexibility.Analysis.N06ReferenceNuColumn
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Radial.R11bTestPairing

/-!
# The actual perturbed relation at the reference state

The original N05 graph supplies its own physical height and source
representatives. The corrected reference operator and the actual nu column
have the original radial weak pairings. Restoring the psi column therefore
gives `PerturbedCanonicalRelation` on the same graph. The proof keeps the
original representatives, including the height tail using `S.chiLeft`;
it makes no identification of that cutoff with `D.chiLeft`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Restoring an integrable scalar column in the original full-period
physical pairing. Integrability of both terms is used before splitting. -/
theorem n06_radialMean_pairing_restore
    {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g φ : PolarPoint → ℝ} {c : ℝ}
    (hsub : Integrable (fun p => (f p - c * g p) * φ p) (radialPhysicalMeasure D))
    (hg : Integrable (fun p => g p * φ p) (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      (f (r, θ) - c * g (r, θ)) * φ (r, θ))) +
      c * (∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * φ (r, θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ)) := by
  have hf : Integrable (fun p => f p * φ p) (radialPhysicalMeasure D) := by
    apply (hsub.add (hg.const_mul c)).congr
    filter_upwards with p
    dsimp only [Pi.add_apply]
    ring
  rw [r11b_integral_angularMean_eq hab hsub, r11b_integral_angularMean_eq hab hg,
    r11b_integral_angularMean_eq hab hf, n06_integral_sub_mul hf hg c]
  ring

/-- The actual nonlinear nu derivative has exactly the reference border
pairing, for the full angular period used by the weak graph. -/
theorem n06_referenceNu_weak_pairing
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hgeom : RadialProfileGeometry D) (hb : RadialTrueBorder D)
    (href : referenceStateConditions D S C) (φ : PolarPoint → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      nuColumnField D S C (C.referenceState, 0) (r, θ) * φ (r, θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * φ (r, θ)) := by
  apply intervalIntegral.integral_congr_Ioo_of_le hgeom.2.1.le
  intro r hr
  have hr0 : r ≠ 0 := (hgeom.1.trans hr.1).ne'
  apply n06_radialAngularMean_congr_ae
  exact Eventually.of_forall fun θ =>
    congrArg (fun t : ℝ => t * φ (r, θ))
      (n06_nuColumn_reference hgeom.2.2.1.1 hb.1 hgeom.2.2.2.1.1 href hr0)

/-- The same physical representatives of a reference canonical relation
satisfy the actual corrected relation at the reference state. -/
theorem n06_referenceCanonicalRelation_perturbed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss : ℕ} {ε γ M₀ M₁ lossMaterial : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ lossMaterial U F) :
    PerturbedCanonicalRelation D S C K L (C.referenceState, 0) U F := by
  obtain ⟨_, η, f, hrep, hgraph⟩ := hrel
  refine ⟨η, f, hrep, hgraph.2.2.1, ?_⟩
  intro φ hφ
  have h01 : N01Properties D T S C base loss ε := h.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have hψ : Continuous ((S.height (3 / 4 : ℝ)).decode S.psi) :=
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) S.psi).1.continuous
  have hψI : Integrable
      (fun p => (S.height (3 / 4 : ℝ)).decode S.psi p * φ p)
      (radialPhysicalMeasure D) :=
    (r11b_continuous_memLp (D := D) hψ).integrable_mul
      (r11b_continuous_memLp (D := D) hφ.1.continuous)
  have hgI : Integrable
      (fun p => (f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p) * φ p)
      (radialPhysicalMeasure D) :=
    r11b_source_radialTest_pairing_integrable hD hgraph.2.1 hφ
  have heq := hgraph.2.2.2 φ hφ
  rw [n06_correctedReference_weak_pairing hT hS h η hφ.1,
    n06_referenceNu_weak_pairing hgeom hb h01.2.2.1 φ, heq]
  exact n06_radialMean_pairing_restore hgeom.2.1.le hgI hψI

/-- Every element of the original N05 closed graph satisfies the corrected
reference relation with its actual graph projection as the source. -/
theorem n06_reference_relation_of_graph
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K V b}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) :
    PerturbedCanonicalRelation D S C K L (C.referenceState, 0) u.val.1
      (V.forget (3 / 4 : ℝ) 0 b u.val.2) := by
  have h05 : N05Properties D T S C K V b B := h.2
  exact n06_referenceCanonicalRelation_perturbed hT hS h.1.1
    ((h05.2.2.2.2.2.2.1 u.val).mp u.property)

/-- In particular, the selected N05 inverse has the original source in
the actual perturbed relation at the reference state. -/
theorem n06_reference_relation_inverse
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K V b}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    PerturbedCanonicalRelation D S C K L (C.referenceState, 0) (B.inverse F).val.1
      (V.forget (3 / 4 : ℝ) 0 b F) := by
  have h05 : N05Properties D T S C K V b B := h.2
  have hrel := n06_reference_relation_of_graph hT hS h (B.inverse F)
  have hright : (B.inverse F).val.2 = F := h05.2.2.2.2.2.2.2.1 F
  simpa only [hright] using hrel

end ContinuousFlexibility.Statements
