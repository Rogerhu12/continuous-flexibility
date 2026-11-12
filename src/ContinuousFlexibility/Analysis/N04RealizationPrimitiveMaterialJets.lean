import ContinuousFlexibility.Analysis.N04RealizationPrimitiveJetAlgebra
import ContinuousFlexibility.Analysis.N04RealizationPrimitiveIdentities
import ContinuousFlexibility.Analysis.N04RealizationMaterialScalarJets

/-!
# Material primitive jets from the actual factor envelopes

The material direction components use the original vector field and
the actual reciprocal material scale. Its density drift uses the exact
reciprocal density, on the same open material piece. The normalizer and
reference multipliers keep their actual factors. All finite algebra
preserves the common coefficient weight and evaluation index.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The finite algebra for the exact density drift uses one additional
density jet and the jets of its actual reciprocal. -/
theorem n04Realization_envelope_densityDrift_jets
    {X : Type*} {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → PolarPoint)
    (V₁ V₂ Ω : X → PolarPoint → ℝ)
    (hV₁ : ∀ x, ContDiffAt ℝ ∞ (V₁ x) (p x))
    (hV₂ : ∀ x, ContDiffAt ℝ ∞ (V₂ x) (p x))
    (hΩ : ∀ x, ContDiffAt ℝ ∞ (Ω x) (p x))
    (hne : ∀ x, Ω x (p x) ≠ 0) (n : ℕ)
    (hV₁j : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V₁ x) (p x)‖))
    (hV₂j : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V₂ x) (p x)‖))
    (hΩj : ∀ j, j ≤ n + 1 → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Ω x) (p x)‖))
    (hIj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => (Ω x y)⁻¹) (p x)‖)) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n
      (fun y => -(V₁ x y * radialPartial (Ω x) y +
        V₂ x y * angularPartial (Ω x) y) / (2 * Ω x y)) (p x)‖) := by
  let d : PolarPoint → X → PolarPoint → ℝ := fun v x y => fderiv ℝ (Ω x) y v
  have hd (v : PolarPoint) (x : X) : ContDiffAt ℝ ∞ (d v x) (p x) :=
    ((hΩ x).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hdj (v : PolarPoint) (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (d v x) (p x)‖) :=
    n04Realization_envelope_directional_jets hW p Ω (fun _ => v) hΩ j
      (hasPositiveEnvelope_const W hW ‖v‖) (hΩj (j + 1) (by omega))
  let A : X → PolarPoint → ℝ := fun x y =>
    V₁ x y * d (1, 0) x y + V₂ x y * d (0, 1) x y
  have hA (x : X) : ContDiffAt ℝ ∞ (A x) (p x) :=
    ((hV₁ x).mul (hd _ x)).add ((hV₂ x).mul (hd _ x))
  have hAj (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (A x) (p x)‖) := by
    have h₁ := n04Realization_envelope_mul_jets hW p V₁ (d (1, 0)) hV₁ (hd _) j
      (fun k hk => hV₁j k (hk.trans hj)) (fun k hk => hdj _ k (hk.trans hj))
    have h₂ := n04Realization_envelope_mul_jets hW p V₂ (d (0, 1)) hV₂ (hd _) j
      (fun k hk => hV₂j k (hk.trans hj)) (fun k hk => hdj _ k (hk.trans hj))
    exact n04Realization_envelope_add_jets hW p
      (fun x y => V₁ x y * d (1, 0) x y) (fun x y => V₂ x y * d (0, 1) x y)
      (fun x => (hV₁ x).mul (hd _ x)) (fun x => (hV₂ x).mul (hd _ x)) j h₁ h₂
  have hI (x : X) : ContDiffAt ℝ ∞ (fun y => (Ω x y)⁻¹) (p x) :=
    (hΩ x).inv (hne x)
  have hAI (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => A x y * (Ω x y)⁻¹) (p x)‖) :=
    n04Realization_envelope_mul_jets hW p A (fun x y => (Ω x y)⁻¹) hA hI j
      (fun k hk => hAj k (hk.trans hj)) (fun k hk => hIj k (hk.trans hj))
  have hscale := n04Realization_envelope_mul_jets hW p
    (fun _ _ => (-1 / 2 : ℝ)) (fun x y => A x y * (Ω x y)⁻¹)
    (fun _ => contDiffAt_const) (fun x => (hA x).mul (hI x)) n
    (fun j _ => n04Realization_envelope_const_jets p (fun _ => (-1 / 2 : ℝ))
      (hasPositiveEnvelope_const W hW ‖(-1 / 2 : ℝ)‖) j) hAI
  apply n04Realization_envelope_jets_congr p
    (fun x y => (-1 / 2 : ℝ) * (A x y * (Ω x y)⁻¹))
    (fun x y => -(V₁ x y * radialPartial (Ω x) y +
      V₂ x y * angularPartial (Ω x) y) / (2 * Ω x y)) n hscale
  intro x
  exact Eventually.of_forall (fun y => by
    simp only [A, d, radialPartial, angularPartial, div_eq_mul_inv, mul_inv_rev]
    ring)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- A single arbitrary physical vector field gives all three actual
material fields. The geometry supplies the genuine open-piece identity
used before the drift derivatives are transferred. -/
theorem n04Realization_materialDirection_envelopes
    {X : Type*} (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hE : ∀ x, T.E0 (T.radius (p x).1) ≤ W x)
    (Y : X → PolarPoint → PolarPoint)
    (hY : ∀ x, ContDiffAt ℝ ∞ (Y x) (n07bMaterialRadiusChart T (p x))) (n : ℕ)
    (hYj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Y x ∘ n07bMaterialRadiusChart T) (p x)‖))
    (hΩj : ∀ j, j ≤ n + 1 → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalMaterialJacobian T K (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖))
    (hIj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (fun y => (canonicalMaterialJacobian T K (z x) (m x)
          (n07bMaterialRadiusChart T y))⁻¹) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV1 T (Y x)) (p x)‖) ∧
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV2 T (Y x)) (p x)‖) ∧
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n
        (n07bMaterialDirectionDrift T K (z x) (m x) (Y x)) (p x)‖) := by
  have hR := n07bMaterialRadiusChart_contDiff hT
  have hYm (x : X) : ContDiffAt ℝ ∞ (Y x ∘ n07bMaterialRadiusChart T) (p x) :=
    (hY x).comp (p x) hR.contDiffAt
  have hell : ContDiff ℝ ∞ (fun y : PolarPoint => T.ell (T.radius y.1)) :=
    (hT.1 T.ell (by simp)).comp_contDiff
      ((hT.2.2.2.2.2.2.1).comp contDiff_fst)
      (fun y => (hT.2.2.2.2.2.2.2.1 y.1).1)
  have hellInv : ContDiff ℝ ∞ (fun y : PolarPoint => (T.ell (T.radius y.1))⁻¹) :=
    hell.inv (fun y => (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 y.1).1).1.ne')
  let V₁ : X → PolarPoint → ℝ := fun x => n07bMaterialDirectionV1 T (Y x)
  let V₂ : X → PolarPoint → ℝ := fun x => n07bMaterialDirectionV2 T (Y x)
  have hV₁ (x : X) : ContDiffAt ℝ ∞ (V₁ x) (p x) :=
    (hYm x).fst.div hell.contDiffAt
      (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 (p x).1).1).1.ne'
  have hV₂ (x : X) : ContDiffAt ℝ ∞ (V₂ x) (p x) := (hYm x).snd
  have hproj (A : PolarPoint →L[ℝ] ℝ) (j : ℕ) (hj : j ≤ n) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ j
        (A ∘ Y x ∘ n07bMaterialRadiusChart T) (p x)‖) :=
    n04Realization_envelope_clm_comp_jets hW p (fun _ => A)
      (fun x => Y x ∘ n07bMaterialRadiusChart T) hYm j
      (hasPositiveEnvelope_const W hW ‖A‖) (hYj j hj)
  have hV₁j (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V₁ x) (p x)‖) := by
    have h := n04Realization_envelope_mul_jets hW p
      (fun x y => (Y x (n07bMaterialRadiusChart T y)).1)
      (fun _ y => (T.ell (T.radius y.1))⁻¹)
      (fun x => (hYm x).fst) (fun _ => hellInv.contDiffAt) j
      (fun k hk => by
        simpa only [Function.comp_def, ContinuousLinearMap.coe_fst'] using
          (hproj (ContinuousLinearMap.fst ℝ ℝ ℝ) k (hk.trans hj)))
      (fun k _ => n04Realization_materialEllInverse_envelope hT hW p hE k)
    have he (x : X) :
        (fun y => (Y x (n07bMaterialRadiusChart T y)).1 *
          (T.ell (T.radius y.1))⁻¹) = V₁ x := by
      funext y
      simp only [V₁, n07bMaterialDirectionV1, n07bDirectionMaterialVector,
        n07bMaterialRadiusChart, div_eq_mul_inv]
    simp_rw [he] at h
    exact h
  have hV₂j (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V₂ x) (p x)‖) := by
    have h := hproj (ContinuousLinearMap.snd ℝ ℝ ℝ) j hj
    have he (x : X) :
        (ContinuousLinearMap.snd ℝ ℝ ℝ ∘ Y x ∘ n07bMaterialRadiusChart T) = V₂ x := by
      funext y
      simp only [V₂, n07bMaterialDirectionV2, n07bDirectionMaterialVector,
        Function.comp_apply, ContinuousLinearMap.coe_snd']
    simp_rw [he] at h
    exact h
  let Ω : X → PolarPoint → ℝ := fun x =>
    canonicalMaterialJacobian T K (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hΩ (x : X) : ContDiffAt ℝ ∞ (Ω x) (p x) :=
    (n07bSourceMaterialJacobian_contDiffAt hT hgeom (hz x) (hs x) (m x) (hp x)).comp
      (p x) hR.contDiffAt
  have hΩne (x : X) : Ω x (p x) ≠ 0 :=
    (n07bSourceMaterialJacobian_pos hT hgeom (hz x) (hs x) (m x) (hp x)).ne'
  have hd := n04Realization_envelope_densityDrift_jets hW p V₁ V₂ Ω hV₁ hV₂ hΩ hΩne
    n hV₁j hV₂j hΩj hIj
  refine ⟨hV₁j n le_rfl, hV₂j n le_rfl, ?_⟩
  apply n04Realization_envelope_jets_congr p
    (fun x y => -(V₁ x y * radialPartial (Ω x) y +
      V₂ x y * angularPartial (Ω x) y) / (2 * Ω x y))
    (fun x => n07bMaterialDirectionDrift T K (z x) (m x) (Y x)) n hd
  intro x
  filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
    (hp x)] with y hy
  exact (n04Realization_materialDirectionDrift_eqOn hT hgeom
    (hz x) (hs x) (m x) (Y x) hy).symm

/-- The common normalizer keeps the same height-ratio power under every
derivative. Only the reciprocal value of the positive density is needed
for the square-root composition. -/
theorem n04Realization_materialNormalizer_envelope
    {X : Type*} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hRatio : HasPositiveEnvelope W
      (fun x => T.H (T.radius (p x).1) / T.H (T.sample (K.cell (m x))))) (n : ℕ)
    (hΩj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalMaterialJacobian T K (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖))
    (hI : HasPositiveEnvelope W
      (fun x => (canonicalMaterialJacobian T K (z x) (m x)
        (n07bMaterialRadiusChart T (p x)))⁻¹)) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n
      (canonicalMaterialNormalizer T K (z x) (m x) (3 / 4 : ℝ) ∘
        n07bMaterialRadiusChart T) (p x)‖) := by
  let Ω : X → PolarPoint → ℝ := fun x =>
    canonicalMaterialJacobian T K (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hΩ (x : X) : ContDiffAt ℝ ∞ (Ω x) (p x) :=
    (n07bSourceMaterialJacobian_contDiffAt hT hgeom (hz x) (hs x) (m x) (hp x)).comp
      (p x) (n07bMaterialRadiusChart_contDiff hT).contDiffAt
  have hΩpos (x : X) : 0 < Ω x (p x) :=
    n07bSourceMaterialJacobian_pos hT hgeom (hz x) (hs x) (m x) (hp x)
  have hsample (x : X) : 0 < T.H (T.sample (K.cell (m x))) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell (m x)))).2.1
  have hH : ContDiff ℝ ∞ (fun y : PolarPoint => T.H (T.radius y.1)) :=
    (hT.1 T.H (by simp)).comp_contDiff
      ((hT.2.2.2.2.2.2.1).comp contDiff_fst)
      (fun y => (hT.2.2.2.2.2.2.2.1 y.1).1)
  let H : X → PolarPoint → ℝ := fun x y =>
    (T.H (T.radius y.1) / T.H (T.sample (K.cell (m x)))) ^ (3 / 4 : ℝ)
  have hHs (x : X) : ContDiffAt ℝ ∞ (H x) (p x) :=
    (hH.contDiffAt.div contDiffAt_const (hsample x).ne').rpow_const_of_ne
      (div_pos (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 (p x).1).1).2.1 (hsample x)).ne'
  have hj := n04Realization_envelope_mul_jets hW p
    (fun x => Real.sqrt ∘ Ω x) H
    (fun x => (hΩ x).sqrt (hΩpos x).ne') hHs n
    (fun j hj => n04Realization_envelope_sqrt_jets hW p Ω hΩ hΩpos j
      (fun k hk => hΩj k (hk.trans hj)) hI)
    (fun j _ => n04Realization_materialHeightRatio_envelope hT hW p
      (fun x => T.sample (K.cell (m x))) hsample hRatio (by norm_num : (0 : ℝ) < 3 / 4) j)
  have he (x : X) :
      (fun y => (Real.sqrt ∘ Ω x) y * H x y) =
        canonicalMaterialNormalizer T K (z x) (m x) (3 / 4 : ℝ) ∘
          n07bMaterialRadiusChart T := by
    funext y
    simp only [Ω, H, canonicalMaterialNormalizer, canonicalMaterialHeightRatio,
      Function.comp_apply, n07bMaterialRadiusChart]
  simp_rw [he] at hj
  exact hj

/-- The reference multipliers use the same reference point as the chart
transition. Compact profile jets cost no state order and no angle value. -/
theorem n04Realization_materialReferenceMultiplier_envelope
    {X : Type*} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (i : X → Fin 3) (n : ℕ)
    (hΘj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖))
    (hBj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalReferenceSourceFactor C K (z x) (m x) ∘ n07bMaterialRadiusChart T)
        (p x)‖)) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n
      (canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inr (i x))) ∘
        n07bMaterialRadiusChart T) (p x)‖) := by
  let Θ : X → PolarPoint → PolarPoint := fun x =>
    canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T
  let B : X → PolarPoint → ℝ := fun x =>
    canonicalReferenceSourceFactor C K (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hΘ (x : X) : ContDiffAt ℝ ∞ (Θ x) (p x) :=
    ((n07b_canonicalReferencePoint_contDiffOn hgeom href hsref (hz x) (hs x) (m x)).contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))).comp
        (p x) (n07bMaterialRadiusChart_contDiff hT).contDiffAt
  have hB (x : X) : ContDiffAt ℝ ∞ (B x) (p x) :=
    ((n07b_canonicalReferenceSourceFactor_contDiffOn hgeom href hsref (hz x) (hs x)
      (m x)).contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))).comp
        (p x) (n07bMaterialRadiusChart_contDiff hT).contDiffAt
  have hpoint (x : X) : (Θ x (p x)).1 ∈ Icc D.a D.b := by
    have hx₀ := n07b_canonicalReferencePoint_mapsTo hgeom href hsref
      (hz x) (hs x) (m x) (hp x)
    have hc := ((hgeom.domains (C.referenceState, 0) href hsref (m x)).2.2.1 hx₀).1
    exact ⟨hc.1.le, hc.2.le⟩
  let f : X → ℝ → ℝ := fun x r =>
    if i x = 0 then deriv D.w r else if i x = 1 then D.w r else deriv D.w r / r
  have hf (x : X) : ContDiff ℝ ∞ (f x) :=
    n04Realization_referenceProfile_contDiff hD.choose_spec.1.1 hD.choose_spec.1.2.2.1 (i x)
  have hrad (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => (Θ x y).1) (p x)‖) := by
    have h := n04Realization_envelope_clm_comp_jets hW p
      (fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ) Θ hΘ j
      (hasPositiveEnvelope_const W hW ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖) (hΘj j hj hjn)
    simpa only [Function.comp_def, ContinuousLinearMap.coe_fst'] using h
  have hprofile (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => f x (Θ x y).1) (p x)‖) :=
    n04Realization_envelope_comp_jets hW p f (fun x y => (Θ x y).1)
      (fun x => (hf x).contDiffAt) (fun x => (hΘ x).fst) j
      (fun k _ => n04Realization_referenceProfile_envelope
        hD.choose_spec.1.1 hD.choose_spec.1.2.2.1 hW
        (fun x => (Θ x (p x)).1) hpoint i k)
      (fun k hk hkj => hrad k hk (hkj.trans hj))
  have hprod := n04Realization_envelope_mul_jets hW p B
    (fun x y => f x (Θ x y).1) hB
    (fun x => (hf x).contDiffAt.comp (p x) (hΘ x).fst) n hBj hprofile
  apply n04Realization_envelope_jets_congr p
    (fun x y => B x y * f x (Θ x y).1)
    (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inr (i x))) ∘
      n07bMaterialRadiusChart T) n hprod
  intro x
  exact Eventually.of_forall (fun y => by
    simp only [B, Θ, f, Function.comp_apply,
      n07b_canonicalPrimitiveField_reference_multiplier, n07bReferenceSeedMultiplier]
    split_ifs <;> rfl)

end ContinuousFlexibility.Analysis
