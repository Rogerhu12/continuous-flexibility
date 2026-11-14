module

public import ContinuousFlexibility.Analysis.N06FullCanonicalPairing
public import ContinuousFlexibility.Analysis.N06PhysicalReconstruction

/-!
# The actual affine height in the full physical pairing

The canonical height represents the remainder after subtracting the
literal space cutoff. Both angular halves are integrable by the actual
canonical L2 pairings. The cutoff term is integrable by the genuine
current height transform of `S.chiLeft`. Only after these facts are
proved do we split the physical pairing into its canonical part and
the affine scalar term. The paired function need not be periodic.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The original smooth radial cutoff pairs integrably with any of the
actual transformed L2 tests supported on the same finite set of pieces. -/
theorem n06_chiLeft_half_pairing_integrable
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {g : PolarPoint → ℝ}
    (hg : ∀ m, MemLp (canonicalSource S K z m g) 2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, g (r, θ) = 0) :
    IntegrableOn (fun p : PolarPoint => S.chiLeft p.1 * g p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hχ (m : ℕ) : MemLp
      (canonicalHeight S K z m (fun p : PolarPoint => S.chiLeft p.1))
      2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m
      (hS.2.2.1.1.continuous.comp continuous_fst).continuousOn
  exact (n06_finitePhysicalPartition_integral h04 hz hs measurableSet_Ioc hfinite
    (g := fun p : PolarPoint => S.chiLeft p.1 * g p)
    (fun r hr θ => by rw [hsupport r hr θ, mul_zero])
    (fun m _ => (n06_current_pairing_integrable h04 hz hs m (hχ m) (hg m)).1)).1

/-- The named current reconstruction has exactly the finite canonical
full-period pairing plus its original left-cutoff scalar term. No N05,
transmission, or coefficient regularity premise is used. -/
theorem n06_physicalHeight_affine_pairing
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (W : CanonicalL2Sequence S K) (aL : ℝ)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {g : PolarPoint → ℝ}
    (h₀ : ∀ m, MemLp (canonicalSource S K z m g) 2 (canonicalMeasure S K m))
    (h₁ : ∀ m, MemLp (canonicalSource S K z m (fun q => g (q + (0, Real.pi))))
      2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, g (r, θ) = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalHeight K z (fun m => (W m : PolarPoint → ℝ)) aL (r, θ) * g (r, θ))) =
      (Real.pi⁻¹ * ∑ m ∈ hfinite.toFinset,
        ∫ p, W m p * canonicalSource S K z m (n06_radialTestAverage g) p
          ∂canonicalMeasure S K m) +
      aL * ∫ r in D.a..D.b, radialAngularMean (fun θ => S.chiLeft r * g (r, θ)) := by
  let η : PolarPoint → ℝ :=
    n06PhysicalHeight K z (fun m => (W m : PolarPoint → ℝ)) aL
  let χ : PolarPoint → ℝ := fun p => S.chiLeft p.1
  let R : PolarPoint → ℝ := fun p => η p - aL * χ p
  let Q : Set PolarPoint := radialCore D ×ˢ Ioc (0 : ℝ) Real.pi
  have hab : D.a ≤ D.b := by
    obtain ⟨x, hxL, hxR⟩ := exists_between (h04.1.referenceBounds 0).1
    have hx := (h04.1.referenceBounds 0).2.2 ⟨hxL, hxR⟩
    exact (hx.1.trans hx.2).le
  have hnamed := n06_physical_representation h04 hz hs
    (W, aL, 0, 0) (0 : CanonicalSequence S K)
  have hrep : ∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m R := hnamed.1.1
  have hηperiod : Function.Periodic η (0, Real.pi) := hnamed.2
  have hχperiod : Function.Periodic χ (0, Real.pi) := by
    intro p
    simp only [χ, Prod.fst_add, add_zero]
  have hRperiod : Function.Periodic R (0, Real.pi) := by
    intro p
    change η (p + (0, Real.pi)) - aL * χ (p + (0, Real.pi)) = η p - aL * χ p
    rw [hηperiod p, hχperiod p]
  have hshiftSupport : ∀ r, r ∉ J → ∀ θ,
      g ((r, θ) + (0, Real.pi)) = 0 := by
    intro r hr θ
    simpa only [Prod.mk_add_mk, add_zero] using hsupport r hr (θ + Real.pi)
  have hR₀ := n06_finiteCanonical_height_pairing h04 hz hs hfinite
    (fun m => W m) hrep h₀ hsupport
  have hR₁ := n06_finiteCanonical_height_pairing h04 hz hs hfinite
    (fun m => W m) hrep h₁ hshiftSupport
  have hχ₀ : IntegrableOn (fun p => χ p * g p) Q :=
    n06_chiLeft_half_pairing_integrable hS h04 hz hs hfinite h₀ hsupport
  have hχ₁ : IntegrableOn (fun p => χ p * g (p + (0, Real.pi))) Q :=
    n06_chiLeft_half_pairing_integrable hS h04 hz hs hfinite h₁ hshiftSupport
  have hη₀ : IntegrableOn (fun p => η p * g p) Q := by
    have hi : IntegrableOn (fun p => R p * g p + aL * (χ p * g p)) Q :=
      hR₀.1.add (hχ₀.const_mul aL)
    have he : (fun p => R p * g p + aL * (χ p * g p)) =
        (fun p => η p * g p) := by
      funext p
      dsimp only [R]
      ring
    exact hi.congr_fun_ae (Filter.Eventually.of_forall (congrFun he))
  have hη₁ : IntegrableOn (fun p => η p * g (p + (0, Real.pi))) Q := by
    have hi : IntegrableOn (fun p => R p * g (p + (0, Real.pi)) +
        aL * (χ p * g (p + (0, Real.pi)))) Q :=
      hR₁.1.add (hχ₁.const_mul aL)
    have he : (fun p => R p * g (p + (0, Real.pi)) +
        aL * (χ p * g (p + (0, Real.pi)))) =
        (fun p => η p * g (p + (0, Real.pi))) := by
      funext p
      dsimp only [R]
      ring
    exact hi.congr_fun_ae (Filter.Eventually.of_forall (congrFun he))
  have hηfull := n06_fullPhysical_pairing_of_two_halves hab hηperiod hη₀ hη₁
  have hχfull := n06_fullPhysical_pairing_of_two_halves hab hχperiod hχ₀ hχ₁
  have hRfull := n06_fullPhysical_pairing_of_two_halves hab hRperiod hR₀.1 hR₁.1
  have hsplit :
      (∫ p in Q, η p * n06_radialTestAverage g p) =
        (∫ p in Q, R p * n06_radialTestAverage g p) +
          aL * ∫ p in Q, χ p * n06_radialTestAverage g p := by
    calc
      _ = ∫ p in Q, R p * n06_radialTestAverage g p +
          aL * (χ p * n06_radialTestAverage g p) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => by dsimp only [R]; ring)
      _ = _ := by
        have he := integral_add hRfull.1 (hχfull.1.const_mul aL)
        simpa only [Pi.add_apply, integral_const_mul] using he
  have hcanonical := n06_fullCanonical_height_pairing hab h04 hz hs hfinite
    (fun m => W m) hrep hRperiod h₀ h₁ hsupport
  calc
    _ = Real.pi⁻¹ * ∫ p in Q, η p * n06_radialTestAverage g p := hηfull.2
    _ = Real.pi⁻¹ * (∫ p in Q, R p * n06_radialTestAverage g p) +
        aL * (Real.pi⁻¹ * ∫ p in Q, χ p * n06_radialTestAverage g p) := by
      rw [hsplit]
      ring
    _ = (∫ r in D.a..D.b, radialAngularMean (fun θ => R (r, θ) * g (r, θ))) +
        aL * ∫ r in D.a..D.b, radialAngularMean (fun θ => χ (r, θ) * g (r, θ)) := by
      rw [← hRfull.2, ← hχfull.2]
    _ = _ := by rw [hcanonical]

end ContinuousFlexibility.Statements
