import ContinuousFlexibility.Analysis.N06BoundaryAngularImage
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Radial endpoint orientation of the actual current chart

A chart takes the physical open interval into the canonical open
interval. At either recorded endpoint its actual nonzero radial first
jet must therefore have the sign determined by the two endpoint choices.
This follows by taking the one-sided limit of the true scalar slopes;
monotonicity of a radial slice is not an input.

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

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The original chart map and closed Jacobian fix the endpoint sign of
its true radial first jet. This one statement covers all four choices of
physical and canonical endpoint; no extra orientation hypothesis occurs. -/
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
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (θ : ℝ) :
    0 < n06EndpointSign physicalUpper * n06EndpointSign canonicalUpper * (σ * ρ θ) ∧
      n06EndpointSign physicalUpper * ((σ * ρ θ) / |σ * ρ θ|) =
        n06EndpointSign canonicalUpper := by
  let r := n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper
  let y := n06Endpoint (K.left m) (K.right m) canonicalUpper
  have hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases physicalUpper <;> simp [r, n06Endpoint, (h04.2.2.2.1 m).1.le]
  have hmap : MapsTo (fun x : ℝ => (K.chart z m (x, θ)).1)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) (Ioo (K.left m) (K.right m)) :=
    fun _ hx => ((h04.2.2.2.2.2.2.2.1 z hz hs m).1 ⟨hx, mem_univ _⟩).1
  have hvalue : (K.chart z m (r, θ)).1 = y := congrArg Prod.fst (J.chart_value θ)
  have hline : HasDerivAt (fun x : ℝ => (x, θ)) (1, 0) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have hd : HasDerivAt (fun x : ℝ => (K.chart z m (x, θ)).1) (σ * ρ θ) r := by
    have he := (J.chart_differentiable θ).hasFDerivAt.fst.comp_hasDerivAt r hline
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', J.chart_radial θ] using he
  have hJ := (h04.2.2.2.2.2.2.2.2.1 z hz hs m (r, θ) hr).2.2.1
  change planeJacobian (K.chart z m)
    (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper, θ) ≠ 0 at hJ
  rw [J.jacobian θ] at hJ
  have hscale : σ * ρ θ ≠ 0 := (mul_ne_zero_iff.mp
    (show (σ * ρ θ) * deriv β θ ≠ 0 from hJ)).1
  have hp := n06_hasDerivAt_endpoint_orientation physicalUpper canonicalUpper
    (h04.2.2.2.1 m).1 hmap hvalue hd hscale
  exact ⟨hp, n06_endpoint_sign_div_abs physicalUpper canonicalUpper hp⟩

end ContinuousFlexibility.Statements
