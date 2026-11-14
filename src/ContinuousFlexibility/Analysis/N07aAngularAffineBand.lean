module

public import ContinuousFlexibility.Analysis.N07aAngularPhysicalBand
public import ContinuousFlexibility.Analysis.N07aAngularReferenceCoordinates

/-!
# Actual bands of an affine radial pullback

The original canonical class already supplies all required integrability.
A radial additive term is retained precisely in angular band zero.  This
single statement handles both the left asymptotic height and the fixed
compatibility column in the canonical reference graph.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Radial

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aAngularBand_affineRow (m : ℕ) (hm : K.left m < K.right m)
    {u : CanonicalL2 S K m} {f g : PolarPoint → ℝ} (A ρ c : ℝ → ℝ)
    (hrow : ∀ r ∈ Ioo (K.left m) (K.right m), ∀ θ,
      g (r, θ) = A r * f (ρ r, θ) + c r)
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r, Function.Even (fun θ => f (r, θ)))
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g) (n : ℕ) :
    (n07aAngularBand m hm n u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => A p.1 * referenceBasisProjection {n} f (ρ p.1, p.2) +
        if 0 = n then c p.1 else 0 := by
  have hgp : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Periodic (fun θ => g (r, θ)) Real.pi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro θ
    dsimp only
    rw [hrow r hr (θ + Real.pi), hrow r hr θ]
    exact congrArg (fun x => A r * x + c r) (hp (ρ r) θ)
  have hge : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Even (fun θ => g (r, θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro θ
    dsimp only
    rw [hrow r hr (-θ), hrow r hr θ]
    exact congrArg (fun x => A r * x + c r) (he (ρ r) θ)
  have hfull := n07aCanonical_memLp_full_of_periodic ((memLp_congr_ae hu).mp (Lp.memLp u)) hgp
  refine (n07aAngularBand_eq_reference_of_periodic m hm hgp hge hu n).trans ?_
  rw [n07aCanonicalMeasure_eq_prod]
  have hs : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      r ∈ Ioo (K.left m) (K.right m) ∧
      MemLp (fun θ => g (r, θ)) 2
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (ae_restrict_mem measurableSet_Ioo).and (memLp_two_prod_sections hfull)
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioo (K.left m) (K.right m))) (ν := angleMeasure)).ae hs] with p hp
  simpa only [Finset.mem_singleton] using
    n07a_referenceBasisProjection_affineRow {n} (hrow p.1 hp.1) hp.2 p.2

end ContinuousFlexibility.Statements
