module

public import ContinuousFlexibility.Analysis.N06RadialReferenceGeometry
public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# The actual canonical operator in the radial weak PDE

The reference coefficient identities determine the formal test operator
used by the weak modal construction. This file carries those identities
through the genuine divergence and through its pairing in the original
canonical measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem n06_divergence_radial_coefficients_germ
    {A : SymmetricCoefficients} {a c : ℝ → ℝ}
    {φ : PolarPoint → ℝ} {p : PolarPoint}
    (ha : A.a =ᶠ[𝓝 p] fun q => a q.1)
    (hb : A.b =ᶠ[𝓝 p] fun _ => 0)
    (hc : A.c =ᶠ[𝓝 p] fun q => c q.1)
    (hcd : DifferentiableAt ℝ c p.1) (hφ : ContDiff ℝ ∞ φ) :
    divergenceOperator A φ p =
      radialPartial (fun q => a q.1 * radialPartial φ q) p +
        c p.1 * angularPartial (angularPartial φ) p := by
  let A0 : SymmetricCoefficients :=
    ⟨fun q => a q.1, fun _ => 0, fun q => c q.1⟩
  have he : divergenceOperator A φ p = divergenceOperator A0 φ p :=
    n06_divergenceOperator_congr_germ φ ha hb hc
  have hcf : DifferentiableAt ℝ (fun q : PolarPoint => c q.1) p :=
    hcd.comp p differentiableAt_fst
  have hφθ : DifferentiableAt ℝ (angularPartial φ) p :=
    (contDiffAt_angularPartial hφ.contDiffAt (m := ∞) (by simp)).differentiableAt (by simp)
  have hprod : angularPartial (fun q : PolarPoint => c q.1 * angularPartial φ q) p =
      angularPartial (fun q : PolarPoint => c q.1) p * angularPartial φ p +
        c p.1 * angularPartial (angularPartial φ) p :=
    angularPartial_mul hcf hφθ
  have hct : angularPartial (fun q : PolarPoint => c q.1) p = 0 :=
    Radial.angularPartial_radialHeightField hcd
  rw [he]
  simp only [A0, divergenceOperator, zero_mul, add_zero, zero_add]
  rw [hprod, hct, zero_mul, zero_add]

/-- The positive type sign in the actual N04 operator identity is the
minus sign in the unit-cylinder weak test operator. -/
theorem n06_canonicalOperator_eq_unitReferenceTestOperator
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hB : N04PartB S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ} {φ : PolarPoint → ℝ} {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (ha : (K.coefficients z m).a =ᶠ[𝓝 p] fun q => a q.1)
    (hb : (K.coefficients z m).b =ᶠ[𝓝 p] fun _ => 0)
    (hc : (K.coefficients z m).c =ᶠ[𝓝 p] fun q => c q.1)
    (hV : K.potential z m p = V p.1)
    (hcd : DifferentiableAt ℝ c p.1) (hφ : ContDiff ℝ ∞ φ) :
    canonicalOperator S K L z m φ p = n06UnitReferenceTestOperator a c V φ p := by
  rw [hB.2.2.1 z hz hs m φ hφ p hp, hm, if_pos rfl,
    n06_divergence_radial_coefficients_germ ha hb hc hcd hφ, hV]
  unfold n06UnitReferenceTestOperator
  ring

/-- Pointwise radial identities on the open canonical piece give the
coefficient germs needed by the actual differential operator. -/
theorem n06_canonicalOperator_eq_unitReferenceTestOperator_of_eqOn
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hB : N04PartB S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ}
    (ha : EqOn (K.coefficients z m).a (fun q => a q.1) (canonicalOpen S K m))
    (hb : EqOn (K.coefficients z m).b (fun _ => 0) (canonicalOpen S K m))
    (hc : EqOn (K.coefficients z m).c (fun q => c q.1) (canonicalOpen S K m))
    (hV : EqOn (K.potential z m) (fun q => V q.1) (canonicalOpen S K m))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hcd : DifferentiableAt ℝ c p.1) :
    canonicalOperator S K L z m φ p = n06UnitReferenceTestOperator a c V φ p := by
  have hOpen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hnear := hOpen.mem_nhds hp
  have hea : (K.coefficients z m).a =ᶠ[𝓝 p] fun q => a q.1 := by
    filter_upwards [hnear] with q hq
    exact ha hq
  have heb : (K.coefficients z m).b =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hnear] with q hq
    exact hb hq
  have hec : (K.coefficients z m).c =ᶠ[𝓝 p] fun q => c q.1 := by
    filter_upwards [hnear] with q hq
    exact hc hq
  exact n06_canonicalOperator_eq_unitReferenceTestOperator hB hz hs hm hp
    hea heb hec (hV hp) hcd hφ

/-- The same identity holds in the genuine canonical pairing, for an
arbitrary L2 representative U or any other real function. -/
theorem n06_canonicalOperator_pairing_eq_unitReference
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hB : N04PartB S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ}
    (ha : EqOn (K.coefficients z m).a (fun q => a q.1) (canonicalOpen S K m))
    (hb : EqOn (K.coefficients z m).b (fun _ => 0) (canonicalOpen S K m))
    (hc : EqOn (K.coefficients z m).c (fun q => c q.1) (canonicalOpen S K m))
    (hV : EqOn (K.potential z m) (fun q => V q.1) (canonicalOpen S K m))
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (U : PolarPoint → ℝ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ p, U p * canonicalOperator S K L z m φ p ∂canonicalMeasure S K m) =
      ∫ p, U p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  rw [n06_canonicalOperator_eq_unitReferenceTestOperator_of_eqOn hB hz hs hm
    ha hb hc hV hφ ⟨hp.1, mem_univ _⟩ (hcd p.1 hp.1)]

end ContinuousFlexibility.Analysis
