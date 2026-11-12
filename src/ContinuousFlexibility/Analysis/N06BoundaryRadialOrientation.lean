import ContinuousFlexibility.Analysis.N06BoundaryAngularImage
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Radial endpoint orientation of the actual current chart

The true inverse takes the canonical open interval to the correct side
of a physical root circle. Its endpoint derivative and the forward root
first jets are reciprocal. Their signs therefore agree, even when the
other boundary of a negative piece is a moving cut. This uses only the
one-sided location of the actual domain, without an inward radial collar
or monotonicity of a physical slice.

The final identity converts the physical outward sign and the signed
radial Jacobian into the canonical outward sign in the Green formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One selector for both endpoints of an interval. -/
def n06Endpoint (a b : ℝ) (upper : Bool) : ℝ := if upper then b else a

/-- The ordinary outward sign in the interval Green formula. -/
def n06EndpointSign (upper : Bool) : ℝ := if upper then 1 else -1

/-- The actual one-sided slope has the orientation of the two endpoint
choices. A nonzero derivative upgrades its limiting weak sign to a strict
sign, without any monotonicity assumption on the function. -/
theorem n06_hasDerivAt_endpoint_orientation
    {a b c d s : ℝ} {f : ℝ → ℝ} (physicalUpper canonicalUpper : Bool)
    (hab : a < b) (hmap : MapsTo f (Ioo a b) (Ioo c d))
    (hvalue : f (n06Endpoint a b physicalUpper) = n06Endpoint c d canonicalUpper)
    (hd : HasDerivAt f s (n06Endpoint a b physicalUpper)) (hs : s ≠ 0) :
    0 < n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * s := by
  have hnot : n06Endpoint a b physicalUpper ∉ Ioo a b := by
    cases physicalUpper <;> simp [n06Endpoint]
  have hclosure : n06Endpoint a b physicalUpper ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    cases physicalUpper <;> simp [n06Endpoint, hab.le]
  haveI : NeBot (𝓝[Ioo a b] (n06Endpoint a b physicalUpper)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (slope f (n06Endpoint a b physicalUpper))
      (𝓝[Ioo a b] (n06Endpoint a b physicalUpper)) (𝓝 s) :=
    (hasDerivWithinAt_iff_tendsto_slope' hnot).mp hd.hasDerivWithinAt
  have hslopes : ∀ᶠ t in 𝓝[Ioo a b] (n06Endpoint a b physicalUpper),
      0 ≤ n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper *
        slope f (n06Endpoint a b physicalUpper) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hf := hmap ht
    rw [slope_def_field, hvalue]
    cases physicalUpper <;> cases canonicalUpper
    · simpa [n06EndpointSign, n06Endpoint] using
        (div_pos (sub_pos.mpr hf.1) (sub_pos.mpr ht.1)).le
    · simpa [n06EndpointSign, n06Endpoint] using
        (neg_pos.mpr (div_neg_of_neg_of_pos (sub_neg.mpr hf.2) (sub_pos.mpr ht.1))).le
    · simpa [n06EndpointSign, n06Endpoint] using
        (neg_pos.mpr (div_neg_of_pos_of_neg (sub_pos.mpr hf.1) (sub_neg.mpr ht.2))).le
    · simpa [n06EndpointSign, n06Endpoint] using
        (div_pos_of_neg_of_neg (sub_neg.mpr hf.2) (sub_neg.mpr ht.2)).le
  have hnonneg : 0 ≤ n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * s :=
    ge_of_tendsto (hlim.const_mul _) hslopes
  have hsignP : n06EndpointSign physicalUpper ≠ 0 := by
    cases physicalUpper <;> norm_num [n06EndpointSign]
  have hsignC : n06EndpointSign canonicalUpper ≠ 0 := by
    cases canonicalUpper <;> norm_num [n06EndpointSign]
  exact lt_of_le_of_ne hnonneg (mul_ne_zero (mul_ne_zero hsignP hsignC) hs).symm

/-- The physical outward sign times the actual radial orientation is
exactly the canonical outward sign. This is the sign used in the closed
Green boundary terms on either endpoint. -/
theorem n06_endpoint_sign_div_abs
    (physicalUpper canonicalUpper : Bool) {s : ℝ}
    (h : 0 < n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * s) :
    n06EndpointSign physicalUpper * (s / |s|) = n06EndpointSign canonicalUpper := by
  cases physicalUpper <;> cases canonicalUpper
  · have hs : 0 < s := by simpa [n06EndpointSign] using h
    simp [n06EndpointSign, abs_of_pos hs, hs.ne']
  · have hs : s < 0 := by simpa [n06EndpointSign] using h
    simp [n06EndpointSign, abs_of_neg hs, hs.ne]
  · have hs : s < 0 := by simpa [n06EndpointSign] using h
    simp [n06EndpointSign, abs_of_neg hs, hs.ne]
  · have hs : 0 < s := by simpa [n06EndpointSign] using h
    simp [n06EndpointSign, abs_of_pos hs, hs.ne']

/-- The true closed inverse identity determines its radial derivative
from the forward first jets. Equality is differentiated within the
nondegenerate closed canonical interval. -/
theorem N06RootFirstJets.inverse_radial_firstJet
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {r y σ a b : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets F h r y σ β H ρ κ Hr)
    (hab : a < b) (hy : y ∈ Icc a b) (θ : ℝ)
    (hG : DifferentiableAt ℝ G (y, β θ))
    (hGF : G (y, β θ) = (r, θ))
    (hFG : ∀ t ∈ Icc a b, F (G (t, β θ)) = (t, β θ)) :
    HasDerivAt (fun t => (G (t, β θ)).1)
        (fderiv ℝ G (y, β θ) (1, 0)).1 y ∧
      (σ * ρ θ) * (fderiv ℝ G (y, β θ) (1, 0)).1 = 1 := by
  let v : PolarPoint := fderiv ℝ G (y, β θ) (1, 0)
  have hpath : HasDerivAt (fun t => G (t, β θ)) v y :=
    hG.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y (β θ)))
  have hradial : HasDerivAt (fun t => (G (t, β θ)).1) v.1 y :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt y hpath
  have hF : DifferentiableAt ℝ F (G (y, β θ)) := by
    rw [hGF]
    exact J.chart_differentiable θ
  have hcomp : HasDerivAt (fun t => F (G (t, β θ)))
      (fderiv ℝ F (G (y, β θ)) v) y :=
    hF.hasFDerivAt.comp_hasDerivAt y hpath
  have hcomp₁ : HasDerivAt (fun t => (F (G (t, β θ))).1)
      (fderiv ℝ F (G (y, β θ)) v).1 y :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt y hcomp
  have hrow : (fderiv ℝ F (r, θ) v).1 = (σ * ρ θ) * v.1 := by
    have he := polarCLM_apply_decompose
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F (r, θ))) v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      J.chart_radial θ, J.chart_angular θ, mul_zero, zero_mul, add_zero, mul_comm] using he
  have hderiv : HasDerivAt (fun t => (F (G (t, β θ))).1) ((σ * ρ θ) * v.1) y := by
    simpa only [hGF, hrow] using hcomp₁
  have hid : HasDerivWithinAt (fun t => (F (G (t, β θ))).1) 1 (Icc a b) y :=
    (hasDerivAt_id y).hasDerivWithinAt.congr_of_mem
      (fun t ht => congrArg Prod.fst (hFG t ht)) hy
  exact ⟨hradial,
    (hderiv.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab y hy)).symm.trans
      (hid.derivWithin (uniqueDiffOn_Icc hab y hy))⟩

private theorem n06_orientation_of_inverse_orientation
    (physicalUpper canonicalUpper : Bool) {s t : ℝ} (hunit : s * t = 1)
    (ht : 0 < n06EndpointSign canonicalUpper * n06EndpointSign physicalUpper * t) :
    0 < n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * s := by
  have hsign : (n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper) *
      (n06EndpointSign canonicalUpper * n06EndpointSign physicalUpper) = 1 := by
    cases physicalUpper <;> cases canonicalUpper <;> norm_num [n06EndpointSign]
  have hproduct : (n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * s) *
      (n06EndpointSign canonicalUpper * n06EndpointSign physicalUpper * t) = 1 := by
    calc
      _ = ((n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper) *
        (n06EndpointSign canonicalUpper * n06EndpointSign physicalUpper)) * (s * t) := by ring
      _ = 1 := by rw [hsign, hunit, one_mul]
  exact (mul_pos_iff_of_pos_right ht).mp (by rw [hproduct]; norm_num)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The true root circle and the actual domain's one-sided location fix
the radial first-jet sign. The one-sided location follows from the fixed
positive domain or the original component containing a negative half;
it does not assert that a moving-cut half is a rectangle. -/
theorem n06_current_boundary_radial_orientation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
    (physicalUpper canonicalUpper : Bool)
    {σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m)
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper)
      (n06Endpoint (K.left m) (K.right m) canonicalUpper) σ β H ρ κ Hr)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hx : ∀ θ : ℝ,
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper, θ) ∈
        physicalPieceClosed S K z m)
    (hside : ∀ p ∈ physicalPieceOpen S K z m,
      if physicalUpper then p.1 < K.physicalRight m else K.physicalLeft m < p.1)
    (θ : ℝ) :
    0 < n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * (σ * ρ θ) ∧
      n06EndpointSign physicalUpper * ((σ * ρ θ) / |σ * ρ θ|) =
        n06EndpointSign canonicalUpper := by
  let r := n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper
  let y := n06Endpoint (K.left m) (K.right m) canonicalUpper
  let a : ℝ := if physicalUpper then D.a else r
  let b : ℝ := if physicalUpper then r else D.b
  have hy : y ∈ Icc (K.left m) (K.right m) := by
    cases canonicalUpper <;> simp [y, n06Endpoint, (h04.1.referenceBounds m).2.1.le]
  have hb := h04.1.boundary z hz hs m
  have hG := (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m
    (p := (y, β θ)) ⟨hy, mem_univ _⟩).differentiableAt (by simp)
  have hGF : K.inverseChart z m (y, β θ) = (r, θ) := by
    have hvalue : K.chart z m (r, θ) = (y, β θ) := J.chart_value θ
    calc
      K.inverseChart z m (y, β θ) = K.inverseChart z m (K.chart z m (r, θ)) :=
        congrArg (K.inverseChart z m) hvalue.symm
      _ = (r, θ) := hb.2.2.1 (r, θ) (hx θ)
  have hj := J.inverse_radial_firstJet (h04.1.referenceBounds m).2.1 hy θ hG hGF
    (fun t ht => hb.2.2.2.1 (t, β θ) ⟨ht, mem_univ _⟩)
  have htne : (fderiv ℝ (K.inverseChart z m) (y, β θ) (1, 0)).1 ≠ 0 := by
    have hprod : (σ * ρ θ) *
        (fderiv ℝ (K.inverseChart z m) (y, β θ) (1, 0)).1 ≠ 0 := by
      rw [hj.2]
      exact one_ne_zero
    exact (mul_ne_zero_iff.mp hprod).2
  have hmap : MapsTo (fun t : ℝ => (K.inverseChart z m (t, β θ)).1)
      (Ioo (K.left m) (K.right m)) (Ioo a b) := by
    intro t ht
    have htc : (t, β θ) ∈ canonicalOpen S K m := ⟨ht, mem_univ _⟩
    have hp := (h04.1.charts z hz hs m).2.1 htc
    have hpD := (h04.1.domains z hz hs m).2.2.1 hp
    have hpSide := hside _ hp
    cases physicalUpper
    · exact ⟨hpSide, hpD.1.2⟩
    · exact ⟨hpD.1.1, hpSide⟩
  have he : n06Endpoint a b physicalUpper = r := by
    cases physicalUpper <;> rfl
  have hvalue : (K.inverseChart z m (y, β θ)).1 = n06Endpoint a b physicalUpper :=
    (congrArg Prod.fst hGF).trans he.symm
  have hinverse := n06_hasDerivAt_endpoint_orientation canonicalUpper physicalUpper
    (h04.1.referenceBounds m).2.1 hmap hvalue hj.1 htne
  have hp := n06_orientation_of_inverse_orientation physicalUpper canonicalUpper hj.2 hinverse
  exact ⟨hp, n06_endpoint_sign_div_abs physicalUpper canonicalUpper hp⟩

end ContinuousFlexibility.Statements
