import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelGlue
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsEnvelope

/-!
# Actual inverse kernel jets on the physical component

The forward polynomial integral bounds apply at the actual inverse
preimage, which stays in the same physical component. The denominator
is the displayed positive radial lower bound. All inverse derivatives
are therefore estimated from numerical forward material, with constants
chosen before the component, coefficient vector and evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

private theorem abs_le_endpoint_sum {l r x : ℝ} (hx : x ∈ Icc l r) :
    |x| ≤ |l| + |r| := by
  apply abs_le.mpr
  constructor
  · exact (by linarith only [abs_nonneg r] : -(|l| + |r|) ≤ -|l|).trans
      ((neg_abs_le l).trans hx.1)
  · exact hx.2.trans ((le_abs_self r).trans (le_add_of_nonneg_left (abs_nonneg l)))

/-- The same displayed widths give the middle-mass reciprocal envelope;
no independent width is chosen for the inverse estimates. -/
theorem n04PositiveGeometry_radialKernel_middleMass_envelope
    {I : Type*} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (l r c d κ M : I → ℝ)
    (hlc : ∀ i, l i < c i) (hcd : ∀ i, c i < d i) (hdr : ∀ i, d i < r i)
    (hκ : ∀ i, 0 < κ i) (hM : ∀ i, 0 ≤ M i)
    (hspan : ∀ side : Bool, HasPositiveEnvelope W
      (fun i => |((if side then r i else c i) - (if side then d i else l i))⁻¹|))
    (side : Bool) :
    HasPositiveEnvelope W (fun i =>
      |(positiveReferenceMiddleMass (if side then d i else l i)
        (if side then r i else c i)
        (endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i) side))⁻¹|) := by
  apply ((hasPositiveEnvelope_const W hW 2).mul hW (hspan side)
    (fun _ => abs_nonneg _)).mono
  intro i
  let η := endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i)
  have hgeom := n04PositiveGeometry_radialKernel_geometry n
    (hlc i) (hcd i) (hdr i) (hκ i) (hM i)
  have hquarter : η side ≤ ((if side then r i else c i) -
      (if side then d i else l i)) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfour : 4 * η side ≤ (if side then r i else c i) -
      (if side then d i else l i) := by linarith only [hquarter]
  have hpos : 0 < positiveReferenceMiddleMass (if side then d i else l i)
      (if side then r i else c i) (η side) :=
    integral_positiveEndpointCutoff_complement_pos (hgeom.1 side) (hgeom.2.1 side)
  rw [abs_of_pos (inv_pos.mpr hpos)]
  apply (positiveReferenceMiddleMass_inv_le (hgeom.1 side) hfour).trans
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)

/-- Every ordinary jet of the literal radial inverse has a uniform
component envelope on its full finite coefficient box and physical slab.
All inputs concern the displayed forward material. -/
theorem n04PositiveGeometry_radialKernel_inverse_bounds
    {I : Type} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (l r c d κ M : I → ℝ)
    (hlc : ∀ i, l i < c i) (hcd : ∀ i, c i < d i) (hdr : ∀ i, d i < r i)
    (hκ : ∀ i, 0 < κ i) (hM : ∀ i, 0 ≤ M i)
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hc : HasPositiveEnvelope W (fun i => |c i|))
    (hd : HasPositiveEnvelope W (fun i => |d i|))
    (hMcost : HasPositiveEnvelope W M)
    (hwidth : ∀ side, HasPositiveEnvelope W (fun i =>
      |(endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i) side)⁻¹|))
    (hspan : ∀ side : Bool, HasPositiveEnvelope W
      (fun i => |((if side then r i else c i) - (if side then d i else l i))⁻¹|))
    (hlower : HasPositiveEnvelope W (fun i =>
      |(endpointFiberLower n (l i) (r i) (c i) (d i) (κ i) (M i))⁻¹|)) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ i (a : N04PositiveRadialCoefficients n),
        a ∈ n04PositiveGeometry_radialCoefficientDomain n (κ i) (M i) →
      ∀ x ∈ Icc (l i) (r i),
        ‖iteratedFDeriv ℝ k
          (fun q : N04PositiveRadialCoefficients n × ℝ =>
            Function.invFun (fun t => n04PositiveGeometry_radialKernel n
              (l i) (r i) (c i) (d i)
              (endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i)) (q.1, t)) q.2)
          (a, x)‖ ≤ C * W i ^ Q := by
  let P := N04PositiveRadialCoefficients n
  let η : I → Bool → ℝ := fun i =>
    endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i)
  let V : I → Set P := fun i => n04PositiveGeometry_radialCoefficientDomain n (κ i) (M i)
  let F : I → P × ℝ → ℝ := fun i =>
    n04PositiveGeometry_radialKernel n (l i) (r i) (c i) (d i) (η i)
  let G : I → P × ℝ → ℝ := fun i q => Function.invFun (fun t => F i (q.1, t)) q.2
  let Ω : I → Set (P × ℝ) := fun i => V i ×ˢ Icc (l i) (r i)
  let J := {z : I × (P × ℝ) // z.2 ∈ Ω z.1}
  let e : J → I := fun z => z.1.1
  let p : J → P × ℝ := fun z => (z.1.2.1, G (e z) z.1.2)
  have hgeom (i : I) := n04PositiveGeometry_radialKernel_geometry n
    (hlc i) (hcd i) (hdr i) (hκ i) (hM i)
  have hpre (z : J) : G (e z) z.1.2 ∈ Icc (l (e z)) (r (e z)) :=
    n04PositiveGeometry_radialKernel_inverse_mem n (hlc (e z)) (hcd (e z))
      (hdr (e z)) (hκ (e z)) (hM (e z)) z.2.1 z.2.2
  have hp : HasPositiveEnvelope (fun z : J => W (e z)) (fun z => ‖p z‖) := by
    apply n04PositiveGeometry_envelope_reindex ((hMcost.add hW hl).add hW hr) e |>.mono
    intro z
    have ha : ‖z.1.2.1‖ ≤ M (e z) := by
      apply (pi_norm_le_iff_of_nonneg (hM (e z))).mpr
      intro side
      apply (pi_norm_le_iff_of_nonneg (hM (e z))).mpr
      intro j
      simpa only [Real.norm_eq_abs] using ((z.2.1 side).2 j).le
    have hx := abs_le_endpoint_sum (hpre z)
    rw [Prod.norm_def, Real.norm_eq_abs]
    apply max_le
    · exact ha.trans (by linarith only [abs_nonneg (l (e z)), abs_nonneg (r (e z))])
    · exact hx.trans (by linarith only [hM (e z)])
  have hmiddle (side : Bool) := n04PositiveGeometry_radialKernel_middleMass_envelope
    hW n l r c d κ M hlc hcd hdr hκ hM hspan side
  have hforward := n04PositiveGeometry_radialKernel_bounds
    (fun z : J => hW (e z)) n p
    (fun z => l (e z)) (fun z => r (e z)) (fun z => c (e z)) (fun z => d (e z))
    (fun z => η (e z)) (fun z => hcd (e z))
    (fun z => (hgeom (e z)).1) (fun z => (hgeom (e z)).2.1) hp
    (n04PositiveGeometry_envelope_reindex hl e) (n04PositiveGeometry_envelope_reindex hr e)
    (n04PositiveGeometry_envelope_reindex hc e) (n04PositiveGeometry_envelope_reindex hd e)
    (fun side => n04PositiveGeometry_envelope_reindex (hwidth side) e)
    (fun side => n04PositiveGeometry_envelope_reindex (hspan side) e)
    (fun side => n04PositiveGeometry_envelope_reindex (hmiddle side) e)
  have hF (i : I) : ContDiffOn ℝ ∞ (F i) (V i ×ˢ univ) :=
    (n04PositiveGeometry_radialKernel_contDiff n (l i) (r i) (c i) (d i)
      (hcd i) (η i) (hgeom i).1 (hgeom i).2.1).contDiffOn
  have hpositive (i : I) (a : P) (ha : a ∈ V i) (t : ℝ) :
      0 < deriv (fun u => F i (a, u)) t :=
    (hgeom i).2.2.1.trans_le ((hgeom i).2.2.2 a ha t)
  have hsurj (i : I) (a : P) (ha : a ∈ V i) : Function.Surjective (fun t => F i (a, t)) :=
    (bijective_of_deriv_lower_bound (hgeom i).2.2.1 ((hgeom i).2.2.2 a ha)).2
  have hslope : ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧ ∀ i q, q ∈ Ω i →
      |(deriv (fun t => F i (q.1, t)) (G i q))⁻¹| ≤ A * W i ^ Q := by
    obtain ⟨A, Q, hA, hQ, hb⟩ := hlower
    refine ⟨A, Q, hA.le, hQ.le, ?_⟩
    intro i q hq
    have hpos := hpositive i q.1 hq.1 (G i q)
    rw [abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_anti₀ (hgeom i).2.2.1 ((hgeom i).2.2.2 q.1 hq.1 (G i q))).trans
      ((le_abs_self _).trans (hb i))
  have hraw (k : ℕ) (_hk : 1 ≤ k) : ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i q, q ∈ Ω i → ‖iteratedFDeriv ℝ k (F i) (q.1, G i q)‖ ≤ A * W i ^ Q := by
    obtain ⟨A, Q, hA, hQ, hb⟩ := hforward.jets k
    exact ⟨A, Q, hA.le, hQ.le, fun i q hq => hb ⟨(i, q), hq⟩⟩
  intro k
  cases k with
  | zero =>
    obtain ⟨C, Q, hC, hQ, hb⟩ := hl.add hW hr
    refine ⟨C, Q, hC, hQ.le, ?_⟩
    intro i a ha x hx
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (abs_le_endpoint_sum
      (n04PositiveGeometry_radialKernel_inverse_mem n (hlc i) (hcd i) (hdr i)
        (hκ i) (hM i) ha hx)).trans (hb i)
  | succ k =>
    obtain ⟨C, Q, hC, hQ, hb⟩ := n04PositiveGeometry_scalarInverse_polynomial_bound W hW V
      (fun i => n04PositiveGeometry_radialCoefficientDomain_isOpen n (κ i) (M i))
      F hF hpositive hsurj Ω (fun _ _ hq => ⟨hq.1, mem_univ _⟩)
      hslope hraw (k + 1) (Nat.succ_pos k)
    exact ⟨C, Q, hC, hQ, fun i a ha x hx => hb i (a, x) ⟨ha, hx⟩⟩

end ContinuousFlexibility.Analysis
