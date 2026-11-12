import ContinuousFlexibility.Analysis.PositiveReferenceCollarLinearJetEnvelope
import ContinuousFlexibility.Analysis.EndpointFiberInterpolation

/-!
# Linear high jets of the same two-collar radial fiber

The actual endpoint collars agree with the identity at their true exits.
The radial glue is therefore locally one of the two existing collars or
the identity. This transfers the linear high-data bound without adding
cutoff derivatives or selecting a new width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveReferenceCollarCoordinate_unit_exit_germ
    {n : ℕ} {A : ℕ → ℝ → ℝ} {l r δ : ℝ}
    (hA : ∀ j, j ≤ n + 1 → ContDiff ℝ ∞ (A j))
    (hδ : 0 < δ) (hgap : 2 * δ < r - l) (root : Bool)
    (hvalue : ∀ θ, A 0 θ = if root then r else l) (θ : ℝ) :
    positiveReferenceCollarCoordinate n l r δ l (r - l) root A
        (Prod.fst : PolarPoint → ℝ) =ᶠ[𝓝 (if root then l else r, θ)]
      (Prod.fst : PolarPoint → ℝ) := by
  let P := positiveReferenceCollarField n l r root A (Prod.fst : PolarPoint → ℝ)
  have hP (side : Bool) : ContDiff ℝ ∞ (P side) := by
    by_cases hs : side = root
    · simpa only [P, positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [P, positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  have hPvalue (side : Bool) (η : ℝ) :
      P side (if side then r else l, η) = if side then l + (r - l) else l := by
    by_cases hs : side = root
    · subst side
      have ht : boundaryTaylorPolynomial (n + 1) (if root then r else l) A
          (if root then r else l, η) = A 0 η := by
        simpa only [iteratedDeriv_zero] using
          iteratedDeriv_boundaryTaylorPolynomial (n + 1) (if root then r else l)
            A (k := 0) (Nat.zero_le _) η
      have hv : A 0 η = if root then l + (r - l) else l := by
        rw [hvalue η]
        split_ifs <;> ring
      simpa only [P, positiveReferenceCollarField, if_pos rfl, ite_true] using ht.trans hv
    · simp only [P, positiveReferenceCollarField, if_neg hs]
      cases side <;> simp only [↓reduceIte] <;> ring
  have hm : r - l ≠ 0 := (show 0 < r - l by linarith).ne'
  have he := parameterizedPositiveReferenceCoordinate_endpoint_germ
    hP hδ hgap hm hPvalue (!root) θ
  have hne : (!root) ≠ root := by cases root <;> decide
  have hout : P (!root) = (Prod.fst : PolarPoint → ℝ) := by
    simp only [P, positiveReferenceCollarField, if_neg hne]
  have hpoint : (if !root then r else l) = (if root then l else r) := by
    cases root <;> rfl
  change parameterizedPositiveReferenceCoordinate l r δ l (r - l)
    (fun side => radialPartial (P side)) =ᶠ[𝓝 (if root then l else r, θ)] _
  simpa only [hout, hpoint] using he

/-- The actual radial glue has a genuine collar or reference germ at
every point, including both exits. Thus all finite jets obey the same bound. -/
theorem norm_iteratedFDeriv_twoEndpointFiberCoordinate_sub_fst_le
    {l r c d K : ℝ} {Y : Bool → PolarPoint → ℝ}
    (hcd : c < d) (hK : 0 ≤ K)
    (hmatch : ∀ (side : Bool) (θ : ℝ), Y side =ᶠ[𝓝 (if side then d else c, θ)]
      (Prod.fst : PolarPoint → ℝ))
    (k : ℕ)
    (hbound : ∀ (side : Bool) (p : PolarPoint),
      p.1 ∈ Icc (if side then d else l) (if side then r else c) →
      ‖iteratedFDeriv ℝ k (fun q => Y side q - q.1) p‖ ≤ K)
    {p : PolarPoint} (hp : p.1 ∈ Icc l r) :
    ‖iteratedFDeriv ℝ k
      (fun q => twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ) q - q.1) p‖ ≤ K := by
  rcases p with ⟨x, θ⟩
  by_cases hc : x < c
  · have he : twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ)
        =ᶠ[𝓝 (x, θ)] Y false := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hc] with q hq
      simp only [twoEndpointFiberCoordinate, radialGermGlue, if_pos hq]
    have he' : (fun q => twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ) q - q.1)
        =ᶠ[𝓝 (x, θ)] (fun q => Y false q - q.1) := he.sub Filter.EventuallyEq.rfl
    rw [(he'.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hbound false (x, θ) ⟨hp.1, hc.le⟩
  · by_cases hd : d < x
    · have he : twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ)
          =ᶠ[𝓝 (x, θ)] Y true := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hd] with q hq
        have hqc : ¬q.1 < c := not_lt_of_ge (hcd.trans hq).le
        simp only [twoEndpointFiberCoordinate, radialGermGlue, if_neg hqc,
          if_neg (not_lt_of_ge hq.le)]
      have he' : (fun q => twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ) q - q.1)
          =ᶠ[𝓝 (x, θ)] (fun q => Y true q - q.1) := he.sub Filter.EventuallyEq.rfl
      rw [(he'.iteratedFDeriv ℝ k).eq_of_nhds]
      exact hbound true (x, θ) ⟨hd.le, hp.2⟩
    · have he := twoEndpointFiberCoordinate_reference_germ_on_middle hcd hmatch
        (show x ∈ Icc c d from ⟨le_of_not_gt hc, le_of_not_gt hd⟩) θ
      have he' : (fun q => twoEndpointFiberCoordinate c d Y (Prod.fst : PolarPoint → ℝ) q - q.1)
          =ᶠ[𝓝 (x, θ)] (fun _ => (0 : ℝ)) := by
        filter_upwards [he] with q hq
        exact sub_eq_zero.mpr hq
      rw [(he'.iteratedFDeriv ℝ k).eq_of_nhds]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hK

/-- Use the displayed widths chosen from low data. The high angular
derivatives of the positive radial Taylor data remain a separate linear factor. -/
theorem exists_endpointFiberInterpolation_linear_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U B l r c d κ Mσ : ℝ},
      1 ≤ U → 1 ≤ B → l < c → c < d → d < r → 0 < κ → 0 ≤ Mσ →
      (∀ side, (endpointFiberWidths n l r c d κ Mσ side)⁻¹ ≤ U) →
      ∀ (A : Bool → ℕ → ℝ → ℝ),
      (∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (A side j)) →
      (∀ side θ, A side 0 θ = if side then r else l) →
      (∀ side j, 1 ≤ j → j ≤ n + 1 → ∀ b, b ≤ N → ∀ θ,
        |iteratedDeriv b (A side j) θ| ≤ B) →
      ∀ k, k ≤ N → ∀ p : PolarPoint, p.1 ∈ Icc l r →
        ‖iteratedFDeriv ℝ k
          (fun q => endpointFiberInterpolation n l r c d
            (endpointFiberWidths n l r c d κ Mσ) A q - q.1) p‖ ≤
          C * (1 + (r - l)) * U ^ (2 * N + 1) * B := by
  obtain ⟨C, hC, hcollar⟩ := exists_positiveReferenceCollarCoordinate_linear_jet_envelope n N
  refine ⟨C, hC, ?_⟩
  intro U B l r c d κ Mσ hU hB hlc hcd hdr hκ hMσ hinv A hA hvalue hjets k hk p hp
  let a : Bool → ℝ := fun side => if side then d else l
  let b : Bool → ℝ := fun side => if side then r else c
  let η := endpointFiberWidths n l r c d κ Mσ
  let Y := endpointFiberCollar n l r c d η A
  have hab (side : Bool) : a side < b side := by cases side <;> assumption
  have hmarg (side : Bool) := prescribedEndpointWidth_margins n
    (sub_pos.mpr (hab side)) zero_lt_one hκ hMσ
    (zero_le_one.trans (le_max_right (Mσ + ((n + 1 : ℕ) : ℝ) * Mσ) 1))
    (sub_pos.mpr (hab side))
  have hfour (side : Bool) : 4 * η side ≤ b side - a side := by
    have hspan : η side ≤ (b side - a side) / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hspan]
  have hmatch (side : Bool) (θ : ℝ) :
      Y side =ᶠ[𝓝 (if side then d else c, θ)] (Prod.fst : PolarPoint → ℝ) := by
    have hv (α : ℝ) : A side 0 α = if side then b side else a side := by
      cases side with
      | false => simpa only [a, b, ↓reduceIte] using hvalue false α
      | true => simpa only [a, b, ↓reduceIte] using hvalue true α
    have he := positiveReferenceCollarCoordinate_unit_exit_germ (hA side)
      (l := a side) (r := b side) (δ := η side)
      (hmarg side).1 (hmarg side).2.2.2.1 side hv θ
    cases side <;> simpa only [Y, endpointFiberCollar, a, b, ↓reduceIte] using he
  have hspan (side : Bool) : b side - a side ≤ r - l := by
    cases side <;> dsimp only [a, b, ↓reduceIte] <;> linarith
  have hbnd (side : Bool) (q : PolarPoint) (hq : q.1 ∈ Icc (a side) (b side)) :
      ‖iteratedFDeriv ℝ k (fun x => Y side x - x.1) q‖ ≤
        C * (1 + (r - l)) * U ^ (2 * N + 1) * B := by
    calc
      _ ≤ C * (1 + (b side - a side)) * U ^ (2 * N + 1) * B :=
        hcollar hU hB (hmarg side).1 (hmarg side).2.2.1 (hfour side)
          (hinv side) side (A side) (hA side) (hjets side) k hk q hq
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_left (hspan side) 1) (zero_le_one.trans hC))
          (pow_nonneg (zero_le_one.trans hU) _)) (zero_le_one.trans hB)
  have hbig : 0 ≤ C * (1 + (r - l)) * U ^ (2 * N + 1) * B := by
    have hlr : l < r := hlc.trans (hcd.trans hdr)
    positivity
  exact norm_iteratedFDeriv_twoEndpointFiberCoordinate_sub_fst_le hcd hbig hmatch k hbnd hp

end ContinuousFlexibility.Analysis
