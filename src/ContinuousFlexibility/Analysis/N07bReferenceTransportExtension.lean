import ContinuousFlexibility.Analysis.N07bTransportWeightComparison
import ContinuousFlexibility.Analysis.N07bTransportMaterialBounds
import ContinuousFlexibility.Analysis.N07bReferenceTransport

/-!
# The actual flat reference transport remainder

Pure geometric bounds on the image weights and the first two transport
jets give a genuine global C² zero extension. This module records its
actual jets, symmetries, and interior values. Adding the prescribed left
cutoff yields a reference representative with the same physical row, by
the already proved a.e. identity for the geometric reference transport.

Only the final row theorem uses the dynamic atlas. Its geometric inputs
are the actual reference-to-current chart and height transition formulas.
No source norm, graph membership, or prescribed decay conclusion is an
input to the construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

/-- The actual remainder, extended by zero at both physical endpoints. -/
def n07bReferenceTransportRemainder (D : ReferenceData)
    (τ : PolarPoint → PolarPoint) (q u : PolarPoint → ℝ) : PolarPoint → ℝ :=
  (annularOpen D).indicator (fun x => q x * u (τ x))

theorem n07bReferenceTransportRemainder_on
    {D : ReferenceData} (τ : PolarPoint → PolarPoint) (q u : PolarPoint → ℝ)
    {x : PolarPoint} (hx : x ∈ annularOpen D) :
    n07bReferenceTransportRemainder D τ q u x = q x * u (τ x) :=
  indicator_of_mem hx _

theorem n07bReferenceTransportRemainder_off
    {D : ReferenceData} (τ : PolarPoint → PolarPoint) (q u : PolarPoint → ℝ)
    {x : PolarPoint} (hx : x.1 ∉ Ioo D.a D.b) :
    n07bReferenceTransportRemainder D τ q u x = 0 :=
  indicator_of_notMem (fun hx' => hx hx'.1) _

/-- Interior equality is equality of germs, hence of every actual jet. -/
theorem n07bReferenceTransportRemainder_iteratedFDeriv_on
    {D : ReferenceData} (τ : PolarPoint → PolarPoint) (q u : PolarPoint → ℝ)
    (n : ℕ) {x : PolarPoint} (hx : x ∈ annularOpen D) :
    iteratedFDeriv ℝ n (n07bReferenceTransportRemainder D τ q u) x =
      iteratedFDeriv ℝ n (fun y => q y * u (τ y)) x := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have heq : n07bReferenceTransportRemainder D τ q u =ᶠ[𝓝 x]
      (fun y => q y * u (τ y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact n07bReferenceTransportRemainder_on τ q u hy
  exact (heq.iteratedFDeriv ℝ n).eq_of_nhds

/-- The zero extension preserves the actual global angular period. -/
theorem n07bReferenceTransportRemainder_periodic
    {D : ReferenceData} {τ : PolarPoint → PolarPoint} {q u : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi))
    (hq : Function.Periodic q (0, Real.pi))
    (hu : Function.Periodic u (0, Real.pi)) :
    Function.Periodic (n07bReferenceTransportRemainder D τ q u) (0, Real.pi) := by
  intro p
  by_cases hp : p.1 ∈ Ioo D.a D.b
  · have hp' : p + (0, Real.pi) ∈ annularOpen D :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp, mem_univ _⟩
    rw [n07bReferenceTransportRemainder_on τ q u (x := p + (0, Real.pi)) hp',
      n07bReferenceTransportRemainder_on τ q u (x := p) ⟨hp, mem_univ _⟩,
      hq p, hτ p, hu (τ p)]
  · have hp' : (p + (0, Real.pi)).1 ∉ Ioo D.a D.b := by
      simpa only [Prod.fst_add, add_zero] using hp
    rw [n07bReferenceTransportRemainder_off τ q u (x := p + (0, Real.pi)) hp',
      n07bReferenceTransportRemainder_off τ q u (x := p) hp]

/-- The zero extension preserves the actual global even symmetry. -/
theorem n07bReferenceTransportRemainder_even
    {D : ReferenceData} {τ : PolarPoint → PolarPoint} {q u : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2))
    (hq : ∀ r θ, q (r, -θ) = q (r, θ))
    (hu : ∀ r θ, u (r, -θ) = u (r, θ)) :
    ∀ r θ, n07bReferenceTransportRemainder D τ q u (r, -θ) =
      n07bReferenceTransportRemainder D τ q u (r, θ) := by
  intro r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · rw [n07bReferenceTransportRemainder_on τ q u (x := (r, -θ)) ⟨hr, mem_univ _⟩,
      n07bReferenceTransportRemainder_on τ q u (x := (r, θ)) ⟨hr, mem_univ _⟩]
    simp only [hτ (r, θ), hq, hu]
  · rw [n07bReferenceTransportRemainder_off τ q u (x := (r, -θ)) hr,
      n07bReferenceTransportRemainder_off τ q u (x := (r, θ)) hr]

/-- Ratio bounds and finite transport-jet bounds supply the full actual
C² extension, its flat endpoint jets, and its interior material jet bound.
The positive exponent δ may be any exponent strictly below β. -/
theorem n07bReferenceTransportRemainder_regular
    {D : ReferenceData} {T : MaterialData} {β δ A B CQ CT CW AW : ℝ}
    {u q : PolarPoint → ℝ} {τ : PolarPoint → PolarPoint}
    (hT : IsMaterialData D T) (hu : HeightMember D T β u)
    (hδ : 0 < δ) (hδβ : δ < β)
    (hq : ContDiffOn ℝ 3 q (annularOpen D))
    (hτ : ContDiffOn ℝ 3 τ (annularOpen D))
    (hmap : MapsTo τ (annularOpen D) (annularOpen D))
    (hCQ : 0 ≤ CQ) (hCT : 0 ≤ CT) (hCW : 0 ≤ CW) (hB : 0 ≤ B)
    (hqjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n q x‖ ≤ CQ * T.M x.1 ^ A)
    (hτjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n τ x‖ ≤ CT * T.M x.1 ^ B)
    (hHratio : ∀ x ∈ annularOpen D,
      T.H (τ x).1 / T.H x.1 ≤ CW * T.E0 x.1 ^ AW)
    (hMratio : ∀ x ∈ annularOpen D,
      T.M (τ x).1 / T.M x.1 ≤ CW * T.E0 x.1 ^ AW) :
    ContDiff ℝ 2 (n07bReferenceTransportRemainder D τ q u) ∧
      (∀ n : ℕ, n ≤ 2 → ∀ x : PolarPoint, x.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n (n07bReferenceTransportRemainder D τ q u) x = 0) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, n ≤ 2 → ∀ x ∈ annularOpen D,
        ‖iteratedFDeriv ℝ n (n07bReferenceTransportRemainder D τ q u) x‖ ≤
          K * T.H x.1 ^ δ * T.M x.1 ^ (A + 2 * B) := by
  obtain ⟨C, hC, hweight⟩ := n07b_transport_weight_bound_of_ratios hT hmap
    (hδ.trans hδβ) hδβ hCW hCW hHratio hMratio
  obtain ⟨hreg, hflat⟩ := n07b_transport_height_c2_flat_extension hT hu hδ hq hτ hmap
    hCQ hCT hC.le hB hqjet hτjet hweight
  obtain ⟨K, hK, hjet⟩ := n07b_transport_height_material_jet_bound hT hu
    (hq.of_le (by norm_num)) (hτ.of_le (by norm_num)) hmap
    hCQ hCT hC.le hB hqjet hτjet hweight
  refine ⟨hreg, hflat, K, hK, ?_⟩
  intro n hn x hx
  rw [n07bReferenceTransportRemainder_iteratedFDeriv_on τ q u n (x := x) hx]
  exact hjet n hn x hx

/-- The prescribed left constant is added after the remainder is extended. -/
def n07bReferenceTransportExtension (D : ReferenceData) (S : PhysicalSpacesData)
    (τ : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (a : ℝ)
    (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  a * S.chiLeft p.1 + n07bReferenceTransportRemainder D τ q u p

theorem n07bReferenceTransportExtension_contDiff
    {D : ReferenceData} {S : PhysicalSpacesData}
    {τ : PolarPoint → PolarPoint} {q u : PolarPoint → ℝ}
    (hχ : ContDiff ℝ 2 S.chiLeft)
    (hR : ContDiff ℝ 2 (n07bReferenceTransportRemainder D τ q u)) (a : ℝ) :
    ContDiff ℝ 2 (n07bReferenceTransportExtension D S τ q a u) :=
  (contDiff_const.mul (hχ.comp contDiff_fst)).add hR

theorem n07bReferenceTransportExtension_periodic
    {D : ReferenceData} {S : PhysicalSpacesData}
    {τ : PolarPoint → PolarPoint} {q u : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi))
    (hq : Function.Periodic q (0, Real.pi))
    (hu : Function.Periodic u (0, Real.pi)) (a : ℝ) :
    Function.Periodic (n07bReferenceTransportExtension D S τ q a u) (0, Real.pi) := by
  intro p
  simp only [n07bReferenceTransportExtension, Prod.fst_add, add_zero,
    n07bReferenceTransportRemainder_periodic hτ hq hu p]

theorem n07bReferenceTransportExtension_even
    {D : ReferenceData} {S : PhysicalSpacesData}
    {τ : PolarPoint → PolarPoint} {q u : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2))
    (hq : ∀ r θ, q (r, -θ) = q (r, θ))
    (hu : ∀ r θ, u (r, -θ) = u (r, θ)) (a : ℝ) :
    ∀ r θ, n07bReferenceTransportExtension D S τ q a u (r, -θ) =
      n07bReferenceTransportExtension D S τ q a u (r, θ) := by
  intro r θ
  simp only [n07bReferenceTransportExtension,
    n07bReferenceTransportRemainder_even hτ hq hu r θ]

/-- The extended field is the actual reference transport at every core
point for the original height u+aχ. -/
theorem n07bReferenceTransportExtension_on
    {D : ReferenceData} (S : PhysicalSpacesData)
    (τ : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (a : ℝ)
    (u : PolarPoint → ℝ) {x : PolarPoint} (hx : x ∈ annularOpen D) :
    n07bReferenceTransportExtension D S τ q a u x =
      n07bReferenceTransport S τ q a (fun y => u y + a * S.chiLeft y.1) x := by
  dsimp only [n07bReferenceTransportExtension, n07bReferenceTransport]
  rw [n07bReferenceTransportRemainder_on τ q u hx]
  ring

/-- The two representatives agree on the entire physical a.e. class,
including the full angular period used by the reference row. -/
theorem n07bReferenceTransportExtension_ae
    {D : ReferenceData} (S : PhysicalSpacesData)
    (τ : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (a : ℝ)
    (u : PolarPoint → ℝ) :
    n07bReferenceTransportExtension D S τ q a u =ᵐ[radialPhysicalMeasure D]
      n07bReferenceTransport S τ q a (fun y => u y + a * S.chiLeft y.1) := by
  have hmem : ∀ᵐ x ∂radialPhysicalMeasure D,
      x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with x hx
  exact n07bReferenceTransportExtension_on S τ q a u ⟨hx.1, mem_univ _⟩

/-- Actual chart and height transition formulas preserve the reference
row after the genuine C² endpoint extension. No integrability or row
identity is required as an additional premise. -/
theorem n07bReferenceTransportExtension_referenceRow
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    (hτpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = K.inverseChart z m (K.chart (C.referenceState, 0) m p))
    (hqpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      q p = K.height (C.referenceState, 0) m p / K.height z m (τ p))
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a : ℝ) (u : PolarPoint → ℝ) :
    referenceRow D (n07bReferenceTransportExtension D S τ q a u) =
      referenceRow D (fun y => u y + a * S.chiLeft y.1) :=
  (n07b_referenceRow_congr_ae hab
    (n07bReferenceTransportExtension_ae S τ q a u)).trans
      (n07bReferenceTransport_referenceRow hτpiece hqpiece hK hab hz hs a
        (fun y => u y + a * S.chiLeft y.1))

end ContinuousFlexibility.Analysis
