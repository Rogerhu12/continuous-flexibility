import ContinuousFlexibility.Analysis.WholePositiveTransportAssembly
import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransportPolynomial

/-!
# The full positive coordinate and height family with a controlled inverse choice

The actual one-sided fields feed the same coordinate and height formulas.
The inverse-fiber envelope now has a fixed polynomial cost. The height
collar retains its explicit reciprocal formula and the actual height and
reciprocal remain bounded by exp(2) times the square of the endpoint
value envelope. Reference identity and every finite matching jet are
unchanged; no exponential of a higher-jet bound is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

universe u

set_option backward.isDefEq.respectTransparency false

private theorem polynomial_endpoint_projection_jet_bound
    {F : PolarPoint → PolarPoint} {p : PolarPoint} {M : ℝ} {k : ℕ}
    (hF : ContDiffAt ℝ ∞ F p) (hbound : ‖iteratedFDeriv ℝ k F p‖ ≤ M)
    (L : PolarPoint →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ‖iteratedFDeriv ℝ k (L ∘ F) p‖ ≤ M :=
  (L.norm_iteratedFDeriv_comp_left hF (by simp : (k : ℕ∞ω) ≤ ∞)).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hL).trans hbound)

theorem exists_wholePositiveTransport_polynomial_envelope (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
    ∀ {ι : Type u} (i₀ : ι)
    {F : ι → Bool → PolarPoint → PolarPoint} {q : ι → Bool → PolarPoint → ℝ}
    {a b : Bool → ℝ} {l r c d κφ κX M H : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκφ : 0 < κφ) (hκφone : κφ ≤ 1) (hκφinv : κφ⁻¹ ≤ M) (hκX : 0 < κX)
    (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hdata : ∀ i side, OneSidedTransportEndpoint (F i side) (q i side)
      (a side) (b side) (if side then r else l))
    (hangle : ∀ i side θ, κφ ≤ angularPartial (fun p => (F i side p).2)
      (if side then r else l, θ))
    (hradial : ∀ i side θ, κX ≤ radialPartial (fun p => (F i side p).1)
      (if side then r else l, θ))
    (hjets : ∀ i side k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
      ‖iteratedFDeriv ℝ k (F i side) (if side then r else l, θ)‖ ≤ M)
    (hupper : ∀ i side θ, q i side (if side then r else l, θ) ≤ H)
    (hinverse : ∀ i side θ, (q i side (if side then r else l, θ))⁻¹ ≤ H)
    (hqjets : ∀ i side k, 1 ≤ k → k ≤ n → ∀ θ,
      ‖iteratedFDeriv ℝ k (q i side) (if side then r else l, θ)‖ ≤ H)
    (href : ∀ side θ,
      F i₀ side =ᶠ[𝓝 (if side then r else l, θ)] (id : PolarPoint → PolarPoint) ∧
      q i₀ side =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ))),
    let ρ := min ((r - l) / 4) (min (c - l) (r - d))
    ∃ Clog Mσ δ : ℝ, 0 < Clog ∧ 1 ≤ Mσ ∧ Mσ ≤ C * M ^ degree ∧
      0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (Clog * H ^ (2 * n + 1) + 1) ∧
      0 < endpointFiberLower n l r c d κX Mσ ∧
      ∀ i,
      let ψ := fun side p => (F i side p).2
      let X := fun side p => (F i side p).1
      let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
      let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
      let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (q i)
      WholePositiveTransportMatching n (F i) (q i) τ σ Q l r c d
        (endpointFiberLower n l r c d κX Mσ * (κφ / 2)) (Real.exp 2 * H ^ 2) ∧
        (i = i₀ → τ = id ∧ σ = id ∧ Q = (fun _ => (1 : ℝ))) := by
  obtain ⟨C, hC, degree, hcoordinates⟩ :=
    exists_oneSidedWholeComponentTransport_polynomial_envelope n
  refine ⟨C, hC, degree, ?_⟩
  intro ι i₀ F q a b l r c d κφ κX M H hlc hcd hdr
    hκφ hκφone hκφinv hκX hM hH hdata hangle hradial hjets hupper hinverse hqjets href
  let ψ : ι → Bool → PolarPoint → ℝ := fun i side p => (F i side p).2
  let X : ι → Bool → PolarPoint → ℝ := fun i side p => (F i side p).1
  have hab (side : Bool) : a side < b side := (hdata i₀ side).interval
  have hend (side : Bool) : (if side then r else l) ∈ Icc (a side) (b side) :=
    (hdata i₀ side).endpoint
  have hψjets (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k)
      (hkn : k ≤ n + 2) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)‖ ≤ M := by
    simpa only [ψ, ContinuousLinearMap.coe_snd', Function.comp_def] using
      polynomial_endpoint_projection_jet_bound ((hdata i side).root_smooth θ)
        (hjets i side k hk hkn θ) (ContinuousLinearMap.snd ℝ ℝ ℝ)
        (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hXjets (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k)
      (hkn : k ≤ n + 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M := by
    simpa only [X, ContinuousLinearMap.coe_fst', Function.comp_def] using
      polynomial_endpoint_projection_jet_bound ((hdata i side).root_smooth θ)
        (hjets i side k hk (by omega) θ) (ContinuousLinearMap.fst ℝ ℝ ℝ)
        (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hperiod (i : ι) (side : Bool) (x : ℝ) (hx : x ∈ Ioo (a side) (b side))
      (θ : ℝ) : F i side (x, θ + Real.pi) = F i side (x, θ) + (0, Real.pi) := by
    simpa only [Prod.mk_add_mk, add_zero] using
      (hdata i side).period_add (x, θ) ⟨hx, mem_univ _⟩
  have hreflect (i : ι) (side : Bool) (x : ℝ) (hx : x ∈ Ioo (a side) (b side))
      (θ : ℝ) : F i side (x, -θ) = ((F i side (x, θ)).1, -(F i side (x, θ)).2) :=
    (hdata i side).reflect (x, θ) ⟨hx, mem_univ _⟩
  have ht := hcoordinates hlc hcd hdr hab hend
    hκφ hκφone hκφinv hκX hM
    (fun i side => (hdata i side).smooth_on.snd)
    (fun i side θ => ((hdata i side).root_smooth θ).snd) hangle hψjets
    (fun i side x hx θ => by
      simpa only [ψ, Prod.snd_add] using congrArg Prod.snd (hperiod i side x hx θ))
    (fun i side x hx θ => congrArg Prod.snd (hreflect i side x hx θ))
    (fun i side => (hdata i side).smooth_on.fst)
    (fun i side θ => ((hdata i side).root_smooth θ).fst)
    (fun i side => (hdata i side).root_radial) hradial hXjets
    (fun i side x hx θ => by
      simpa only [X, Prod.fst_add, add_zero] using congrArg Prod.fst (hperiod i side x hx θ))
    (fun i side x hx θ => congrArg Prod.fst (hreflect i side x hx θ))
  dsimp only at ht
  rcases ht with ⟨_, _, _, _, _, Mσ, hMσ, hcost, hη, hηgap, hB, ht⟩
  let ρ : ℝ := min ((r - l) / 4) (min (c - l) (r - d))
  have hlr : l < r := hlc.trans (hcd.trans hdr)
  have hρ : 0 < ρ := lt_min (div_pos (sub_pos.mpr hlr) (by norm_num))
    (lt_min (sub_pos.mpr hlc) (sub_pos.mpr hdr))
  have hρwidth : 2 * ρ ≤ r - l := by
    have h := min_le_left ((r - l) / 4) (min (c - l) (r - d))
    dsimp only [ρ]
    linarith
  have hρleft : ρ ≤ c - l :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρright : ρ ≤ r - d :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Clog, hClog, hlogbound⟩ := exists_oneSidedLogBoundaryJet_envelope n
  let Mlog : ℝ := Clog * H ^ (2 * n + 1)
  have hMlog : 0 ≤ Mlog := mul_nonneg hClog.le (pow_nonneg (zero_le_one.trans hH) _)
  have hlog (i : ι) (side : Bool) (j : ℕ) (_hj : 0 < j) (hjn : j ≤ n) (θ : ℝ) :
      |positiveHeightTaylorData l r (fun _ => 1) (q i) side j θ| ≤ Mlog := by
    simpa only [positiveHeightTaylorData, boundaryHeightLogRatio, div_one, Mlog] using
      hlogbound H hH (q i side) (a side) (b side) (if side then r else l)
        (hab side) (hdata i side).height_smooth_on (hend side)
        (fun η => ((hdata i side).height_root η).1) (hdata i side).height_positive
        (fun η => ((hdata i side).height_root η).2) (hupper i side) (hinverse i side)
        (hqjets i side) j hjn θ
  obtain ⟨δ, hδ, hδρ, hδone, hrecip, hQ⟩ := exists_oneSidedEndpointHeight_family n
    hab hend hρ hρwidth hMlog hH
    (fun i side => (hdata i side).height_smooth_on)
    (fun i side θ => ((hdata i side).height_root θ).1)
    (fun i side θ => ((hdata i side).height_root θ).2)
    hupper hinverse hlog
    (fun i side x hx θ => by
      simpa only [Prod.mk_add_mk, add_zero] using
        (hdata i side).height_period (x, θ) ⟨hx, mem_univ _⟩)
    (fun i side x hx θ => (hdata i side).height_even (x, θ) ⟨hx, mem_univ _⟩)
  refine ⟨Clog, Mσ, δ, hClog, hMσ, hcost, hδ, hδρ, hδone, hrecip, hB, ?_⟩
  intro i
  dsimp only
  rcases ht i with ⟨hgeometry, _, _, hboundary⟩
  rcases hQ i with ⟨hQsmooth, hQpos, hQjets, hQperiod, hQeven, hQmiddle, hQbound⟩
  constructor
  · refine {
      geometry := hgeometry
      height_smooth := hQsmooth
      height_positive := hQpos
      coordinate_jets := ?_
      height_jets := hQjets
      height_period := hQperiod
      height_even := hQeven
      height_middle_germ := ?_
      height_bound := hQbound }
    · intro side k hk θ
      simpa only [X, ψ, Prod.eta] using hboundary side k hk θ
    · intro x hx θ
      apply hQmiddle (x, θ)
      · rw [Metric.mem_ball, Real.dist_eq]
        apply not_lt.mpr
        rw [abs_of_nonneg (sub_nonneg.mpr (hlc.le.trans hx.1))]
        exact (hδρ.trans hρleft).trans (sub_le_sub_right hx.1 l)
      · rw [Metric.mem_ball, Real.dist_eq]
        apply not_lt.mpr
        rw [abs_of_nonpos (sub_nonpos.mpr (hx.2.trans hdr.le))]
        have h := hδρ.trans hρright
        linarith [hx.2]
  · intro hi
    subst i
    have hψref (side : Bool) (θ : ℝ) : ψ i₀ side =ᶠ[𝓝 (if side then r else l, θ)]
        (Prod.snd : PolarPoint → ℝ) := by
      filter_upwards [(href side θ).1] with p hp
      exact congrArg Prod.snd hp
    have hXref (side : Bool) (θ : ℝ) : X i₀ side =ᶠ[𝓝 (if side then r else l, θ)]
        (Prod.fst : PolarPoint → ℝ) := by
      filter_upwards [(href side θ).1] with p hp
      exact congrArg Prod.fst hp
    have hid := oneSidedWholeComponentTransport_reference_identity
      (κφ := κφ) (κX := κX) (M := M) (Mσ := Mσ) n hψref hXref hη hηgap
    exact ⟨hid.1, hid.2, positiveHeightTaylorInterpolation_reference_one n l r δ
      (fun side θ => (href side θ).2)⟩


end ContinuousFlexibility.Analysis
