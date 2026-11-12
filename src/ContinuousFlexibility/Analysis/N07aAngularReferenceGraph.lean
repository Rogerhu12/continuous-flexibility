import ContinuousFlexibility.Analysis.N07aAngularAffineBand
import ContinuousFlexibility.Analysis.N07aAngularCanonicalProjection

/-!
# Angular bands preserve the genuine canonical reference relation

The projected physical source is reconstructed from its compatible part
and the actual radial auxiliary column.  The actual height and source
coordinate formulas identify these representatives with the canonical
Hilbert projections.  All weak equations and endpoint classes come from
the existing physical reference graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}

/-- Primitive reference geometry suffices to preserve the actual N05 relation. -/
theorem n07a_referenceCanonicalRelation_band
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hV : IsVolumeModel T S K V) (hK : ∀ m, K.left m < K.right m)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hmap : ∀ m, MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (hsm : ∀ m, ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    {γ M₀ M₁ loss : ℝ} (hγ : 0 < γ)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ loss U F) (n : ℕ) :
    ReferenceCanonicalRelation D T S C K V γ M₀ M₁ loss
      (n07aAngularUnknownBand hK n U) (n07aAngularSequenceBand hK n F) := by
  obtain ⟨hVol, η, f, hRep, hgraph⟩ := hrel
  let ψ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode S.psi
  let g : PolarPoint → ℝ := fun p => f p - U.2.2.2 * ψ p
  let η' : PolarPoint → ℝ := referenceBasisProjection {n} η
  let lprime : ℝ := if 0 = n then U.2.2.2 else 0
  let f' : PolarPoint → ℝ := fun p => referenceBasisProjection {n} g p + lprime * ψ p
  have hψ (p : PolarPoint) : ψ p = ψ (p.1, 0) := hAux.1 p
  obtain ⟨aL, hη⟩ := hgraph.1
  have hpη (r : ℝ) : Function.Periodic (fun θ => η (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hη.2.2.1 (r, θ)
  have heη (r : ℝ) : Function.Even (fun θ => η (r, θ)) := hη.2.2.2 r
  have hpg (r : ℝ) : Function.Periodic (fun θ => g (r, θ)) Real.pi := by
    intro θ
    simpa only [g, ψ, Prod.mk_add_mk, add_zero] using hgraph.2.1.2.2.1 (r, θ)
  have heg (r : ℝ) : Function.Even (fun θ => g (r, θ)) := hgraph.2.1.2.2.2.1 r
  have hmem (m : ℕ) : ∀ᵐ p ∂canonicalMeasure S K m,
      p.1 ∈ Ioo (K.left m) (K.right m) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact hp.1
  have hVol' : VolumeMember S K V (3 / 4 : ℝ) (-loss) 0
      (fun m => (n07aAngularUnknownBand hK n U).1 m) := by
    change VolumeMember S K V (3 / 4 : ℝ) (-loss) 0
      (n07aAngularSequenceBand hK n (fun m => U.1 m))
    exact n07aAngularSequenceBand_volumeMember hV hK hVol n
  refine ⟨hVol', η', f', ?_, ?_⟩
  · constructor
    · intro m
      let ρ : ℝ → ℝ := fun r => (K.inverseChart (C.referenceState, 0) m (r, 0)).1
      let A : ℝ → ℝ := fun r => (K.height (C.referenceState, 0) m (ρ r, 0))⁻¹
      let c : ℝ → ℝ := fun r => -(U.2.1) * S.chiLeft (ρ r) * A r
      have hrow (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) (θ : ℝ) :
          canonicalHeight S K (C.referenceState, 0) m
            (fun p => η p - U.2.1 * S.chiLeft p.1) (r, θ) =
          A r * η (ρ r, θ) + c r := by
        rw [n07a_canonicalHeight_reference_row hR m (hmap m) _ hr θ]
        dsimp only [A, ρ, c]
        ring
      have hband := n07aAngularBand_affineRow m (hK m) A ρ c hrow hpη heη (hRep.1 m) n
      simp only [n07aAngularUnknownBand_field, n07aAngularUnknownBand_left]
      refine hband.trans ?_
      filter_upwards [hmem m] with p hp
      rw [n07a_canonicalHeight_reference_row hR m (hmap m) _ hp p.2]
      dsimp only [η', A, ρ, c]
      by_cases hn : 0 = n <;> simp only [hn, ite_true, ite_false] <;> ring
    · intro m
      let ρ : ℝ → ℝ := fun r => (K.inverseChart (C.referenceState, 0) m (r, 0)).1
      let A : ℝ → ℝ := fun r => K.height (C.referenceState, 0) m (ρ r, 0) /
        |planeJacobian (K.chart (C.referenceState, 0) m) (ρ r, 0)|
      let c : ℝ → ℝ := fun r => U.2.2.2 * A r * ψ (ρ r, 0)
      have hrow (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) (θ : ℝ) :
          canonicalSource S K (C.referenceState, 0) m f (r, θ) =
            A r * g (ρ r, θ) + c r := by
        rw [n07a_canonicalSource_reference_row hR m (hmap m) (hsm m) f hr θ]
        dsimp only [A, ρ, c, g]
        rw [hψ]
        ring
      have hband := n07aAngularBand_affineRow m (hK m) A ρ c hrow hpg heg (hRep.2 m) n
      simp only [n07aAngularSequenceBand_apply]
      refine hband.trans ?_
      filter_upwards [hmem m] with p hp
      rw [n07a_canonicalSource_reference_row hR m (hmap m) (hsm m) _ hp p.2]
      dsimp only [f', A, ρ, c, lprime]
      rw [hψ ((K.inverseChart (C.referenceState, 0) m (p.1, 0)).1, p.2)]
      by_cases hn : 0 = n <;> simp only [hn, ite_true, ite_false] <;> ring
  · simp only [n07aAngularUnknownBand_border, n07aAngularUnknownBand_auxiliary]
    have hsource : (fun p => f' p - (if 0 = n then U.2.2.2 else 0) * ψ p) =
        referenceBasisProjection {n} g := by
      funext p
      dsimp only [f', lprime]
      ring
    change ReferenceGraph D γ M₀ M₁ (η', if 1 = n then U.2.2.1 else 0)
      ((fun p => f' p - (if 0 = n then U.2.2.2 else 0) * ψ p), 0)
    rw [hsource]
    simpa only [Finset.mem_singleton, ite_self] using
      n07a_referenceGraph_basisProjection hD hborder hγ hgraph {n}

end ContinuousFlexibility.Statements
