module

public import ContinuousFlexibility.Analysis.RadialTaylorSliceJetEnvelope
public import ContinuousFlexibility.Analysis.PositiveReferenceTaylorPrescribedWidth
public import ContinuousFlexibility.Analysis.PositiveReferenceSlopeAllOrderJets
public import ContinuousFlexibility.Analysis.PositiveReferenceHeightAllOrderJets

/-!
# All orders at the same displayed reference Taylor width

The finite degree and its actual width are fixed from the low endpoint
data. A later derivative order enlarges only a numerical upper bound.
The integral coordinate and clipped-log height remain the same functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The displayed width is independent of the requested derivative
order. The original finite coefficients control every order of the
same reference coordinate, height and reciprocal height. -/
theorem exists_positiveReferenceTaylor_allOrder_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {l r U : ℝ}, l < r → 1 ≤ U → (r - l)⁻¹ ≤ U →
      ∀ y h : Bool → PolarPoint → ℝ,
        (∀ (side : Bool) θ, ContDiffAt ℝ ∞ (y side) (if side then r else l, θ)) →
        (∀ (side : Bool) θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ)) →
        (∀ side : Bool, U⁻¹ ≤ radialBoundaryJet (y side) (if side then r else l) 1 0) →
        (∀ side : Bool, U⁻¹ ≤ radialBoundaryJet (h side) (if side then r else l) 0 0) →
        (∀ (side : Bool) j, j ≤ n + 1 →
          |radialBoundaryJet (y side) (if side then r else l) j 0| ≤ U) →
        (∀ (side : Bool) j, j ≤ n + 1 →
          |radialBoundaryJet (h side) (if side then r else l) j 0| ≤ U) →
        let δ := positiveReferenceTaylorWidth n l r U⁻¹ U
        let ys := fun side : Bool =>
          radialEndpointTaylorSlice (n + 1) (if side then r else l) (y side)
        let hs := fun side : Bool =>
          radialEndpointTaylorSlice (n + 1) (if side then r else l) (h side)
        let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
        let H := positiveReferenceHeight l r δ (hs false) (hs true)
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv (k + 1) Y x| ≤ C * U ^ (2 * ((3 * N + 1) * N + 2)) ∧
          |iteratedDeriv k H x| ≤ C * U ^ (2 * ((3 * N + 1) * N + 2)) ∧
          |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤
            C * U ^ (2 * ((3 * N + 1) * N + 2)) := by
  obtain ⟨Ct, hCt, ht⟩ := exists_radialEndpointTaylorSlice_jet_envelope (n + 1) (N + 1)
  obtain ⟨Cy, hCy, hy⟩ := exists_positiveReferenceCoordinate_allOrder_positiveJet_envelope N
  obtain ⟨Ch, hCh, hh⟩ := exists_positiveReferenceHeight_allOrder_jet_envelope N
  let D : ℝ := 24 + 16 * ((n + 2 : ℕ) : ℝ)
  let K : ℝ := D + Ct + 2
  let E : ℕ := (3 * N + 1) * N + 2
  have hcast : 0 ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK : 1 ≤ K := by dsimp only [K, D]; linarith only [hCt, hcast]
  have hDK : D ≤ K := by dsimp only [K]; linarith only [hCt]
  have hCtK : Ct ≤ K := by dsimp only [K, D]; linarith only [hcast]
  have htwoK : (2 : ℝ) ≤ K := by dsimp only [K, D]; linarith only [hCt, hcast]
  have hsum : 1 ≤ Cy + Ch := by linarith only [hCy, hCh]
  refine ⟨(Cy + Ch) * K ^ E,
    one_le_mul_of_one_le_of_one_le hsum (one_le_pow₀ hK), ?_⟩
  intro l r U hlr hU hgapU y h hyc hhc hylower hhlower hyjet hhjet
  let δ := positiveReferenceTaylorWidth n l r U⁻¹ U
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (h side)
  let a : Bool → ℝ → ℝ := fun side => deriv (ys side)
  let L : ℝ := U + ((n + 1 : ℕ) : ℝ) * U
  let V : ℝ := K * U ^ 2
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hκ : 0 < U⁻¹ := inv_pos.mpr hUpos
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hV : 1 ≤ V := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hU)
  have hU2 : U ≤ U ^ 2 := by
    calc
      U = U * 1 := (mul_one U).symm
      _ ≤ U * U := mul_le_mul_of_nonneg_left hU hUpos.le
      _ = U ^ 2 := by ring
  have hlinear {d : ℝ} (hd : 0 ≤ d) (hdK : d ≤ K) : d * U ≤ V :=
    (mul_le_mul_of_nonneg_left hU2 hd).trans
      (mul_le_mul_of_nonneg_right hdK (sq_nonneg U))
  have hCtV : Ct * U ≤ V := hlinear (zero_le_one.trans hCt) hCtK
  have htwoV : 2 * U ≤ V := hlinear (by norm_num) htwoK
  obtain ⟨hδ, hδone, hfour, _hgap, hsmall, hmass, _hinv⟩ :=
    positiveReferenceTaylorWidth_margins n hlr hκ hUpos.le
  have hδV : δ⁻¹ ≤ V :=
    (positiveReferenceTaylorWidth_polynomial_inv_le n hlr hκ hUpos.le hU
      le_rfl (inv_inv U).le hgapU).trans
      (mul_le_mul_of_nonneg_right hDK (sq_nonneg U))
  have hys (side : Bool) : ContDiff ℝ ∞ (ys side) :=
    contDiff_radialEndpointTaylorSlice _ (hyc side) (n + 1)
  have hhs (side : Bool) : ContDiff ℝ ∞ (hs side) :=
    contDiff_radialEndpointTaylorSlice _ (hhc side) (n + 1)
  have ha (side : Bool) (x : ℝ) : ContDiffAt ℝ ∞ (a side) x :=
    (hys side).contDiffAt.derivWithin (by simp)
  have hcollar (side : Bool) (x : ℝ)
      (hx : x ∈ Metric.ball (if side then r else l) δ) :
      U⁻¹ / 2 ≤ a side x ∧ |a side x| ≤ L ∧
        U⁻¹ / 2 ≤ hs side x ∧ |hs side x| ≤ 2 * U := by
    have hx' : |x - (if side then r else l)| ≤ δ :=
      (show |x - (if side then r else l)| < δ from
        (by simpa only [Metric.mem_ball, Real.dist_eq] using hx)).le
    exact radialEndpointTaylorSlice_collar_bounds n hδ.le hδone hUpos.le hx'
      (hylower side) (hhlower side) (fun j _ hj => hyjet side j hj)
      (hhjet side) hsmall
  have hunit (side : Bool) (x : ℝ)
      (hx : x ∈ Metric.ball (if side then r else l) δ) :
      |x - (if side then r else l)| ≤ 1 :=
    (show |x - (if side then r else l)| < δ from
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hx)).le.trans hδone
  have hajet (side : Bool) (k : ℕ) (hk : k ≤ N)
      (x : ℝ) (hx : x ∈ Metric.ball (if side then r else l) δ) :
      |iteratedDeriv k (a side) x| ≤ V := by
    change |iteratedDeriv k (deriv (ys side)) x| ≤ V
    rw [← iteratedDeriv_succ']
    exact (ht hUpos.le (y side) _ (hyjet side) (k + 1)
      (Nat.add_le_add_right hk 1) x (hunit side x hx)).trans hCtV
  have hhjet' (side : Bool) (k : ℕ) (hk : k ≤ N)
      (x : ℝ) (hx : x ∈ Metric.ball (if side then r else l) δ) :
      |iteratedDeriv k (hs side) x| ≤ V :=
    (ht hUpos.le (h side) _ (hhjet side) k
      (hk.trans (Nat.le_succ N)) x (hunit side x hx)).trans hCtV
  have hheightValue (side : Bool) (x : ℝ)
      (hx : x ∈ Metric.ball (if side then r else l) δ) :
      0 < hs side x ∧ hs side x ≤ V ∧ (hs side x)⁻¹ ≤ V := by
    have hc := hcollar side x hx
    have hinv : (hs side x)⁻¹ ≤ 2 * U := by
      simpa only [inv_div, div_inv_eq_mul] using inv_anti₀ (half_pos hκ) hc.2.2.1
    exact ⟨(half_pos hκ).trans_le hc.2.2.1,
      (le_abs_self _).trans (hc.2.2.2.trans htwoV), hinv.trans htwoV⟩
  have hscale := positiveReferenceScale_two_sided hδ hfour (half_pos hκ) hL
    (a := a) (fun side x _ => ha side x) (fun side x hx => (hcollar side x hx).1)
    (fun side x hx => (hcollar side x hx).2.1) hmass
  have hscaleV : |positiveReferenceScale l r δ (a false) (a true)| ≤ V := by
    have hμ : 0 ≤ positiveReferenceScale l r δ (a false) (a true) :=
      (show 0 < 1 / (2 * (r - l)) from
        one_div_pos.mpr (mul_pos (by norm_num) (sub_pos.mpr hlr))).le.trans hscale.1
    rw [abs_of_nonneg hμ]
    exact (hscale.2.trans (by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hgapU (by norm_num : (0 : ℝ) ≤ 2))).trans htwoV
  have hNE : N + 1 ≤ E := by dsimp only [E]; nlinarith
  have hfinish {d : ℝ} (hd : d ≤ Cy + Ch) :
      d * V ^ E ≤ ((Cy + Ch) * K ^ E) * U ^ (2 * E) := by
    calc
      _ ≤ (Cy + Ch) * V ^ E :=
        mul_le_mul_of_nonneg_right hd (pow_nonneg (zero_le_one.trans hV) _)
      _ = _ := by dsimp only [V]; rw [mul_pow, ← pow_mul]; ring
  change ∀ k, k ≤ N → ∀ x : ℝ,
    |iteratedDeriv (k + 1) (positiveReferenceCoordinate l r δ (a false) (a true)) x| ≤
        ((Cy + Ch) * K ^ E) * U ^ (2 * E) ∧
    |iteratedDeriv k (positiveReferenceHeight l r δ (hs false) (hs true)) x| ≤
        ((Cy + Ch) * K ^ E) * U ^ (2 * E) ∧
    |iteratedDeriv k (fun t =>
      (positiveReferenceHeight l r δ (hs false) (hs true) t)⁻¹) x| ≤
        ((Cy + Ch) * K ^ E) * U ^ (2 * E)
  intro k hk x
  have hY := hy hδ hV hδV (zero_le_one.trans hV) a
    (fun side t _ => ha side t) hajet hscaleV k hk x
  have hY' : |iteratedDeriv (k + 1)
      (positiveReferenceCoordinate l r δ (a false) (a true)) x| ≤
      Cy * V ^ E := by
    calc
      _ ≤ Cy * V ^ N * V := hY
      _ = Cy * V ^ (N + 1) := by rw [pow_succ]; ring
      _ ≤ Cy * V ^ E := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hV hNE) (zero_le_one.trans hCy)
  have hH := hh hδ hV hδV hs (fun side t _ => (hhs side).contDiffAt)
    hheightValue hhjet' k hk x
  exact ⟨hY'.trans (hfinish (le_add_of_nonneg_right (zero_le_one.trans hCh))),
    hH.1.trans (hfinish (le_add_of_nonneg_left (zero_le_one.trans hCy))),
    hH.2.trans (hfinish (le_add_of_nonneg_left (zero_le_one.trans hCy)))⟩

end ContinuousFlexibility.Analysis
