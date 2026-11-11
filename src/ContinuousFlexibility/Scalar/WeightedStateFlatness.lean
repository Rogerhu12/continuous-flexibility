import ContinuousFlexibility.Scalar.WeightedStateRegularity
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Flat scalar profiles and admissible scalar states

One Taylor argument gives arbitrary endpoint decay for every smooth radial
function supported in the physical interval. A single constant-on-a-set jet
lemma handles the left and right endpoints. The resulting boundary jets and
periodicity identify a geometric weighted state with the existing admissible
scalar-calculus domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Ordinary derivatives agree with the derivatives of a constant on any
set with unique derivatives, including a closed half-line at its endpoint. -/
private theorem scalar_iteratedDeriv_zero_of_eqOn
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : UniqueDiffOn ℝ s) (hzero : EqOn f (fun _ => 0) s)
    (n : ℕ) {r : ℝ} (hr : r ∈ s) : iteratedDeriv n f r = 0 := by
  calc
    iteratedDeriv n f r = iteratedDerivWithin n f s r :=
      (iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt.of_le (by simp)) hr).symm
    _ = iteratedDerivWithin n (fun _ : ℝ => (0 : ℝ)) s r :=
      iteratedDerivWithin_congr hzero hr
    _ = 0 := iteratedDerivWithin_fun_const_zero

/-- All ordinary derivatives preserve the smooth radial support condition. -/
theorem EndpointFlat.iteratedDeriv {D : ReferenceData} {f : ℝ → ℝ}
    (hf : EndpointFlat D f) (n : ℕ) : EndpointFlat D (iteratedDeriv n f) := by
  refine ⟨?_, ?_⟩
  · rw [iteratedDeriv_eq_iterate]
    exact hf.1.iterate_deriv n
  · intro r hr
    rcases hr with hr | hr
    · exact scalar_iteratedDeriv_zero_of_eqOn hf.1 (uniqueDiffOn_Iic D.a)
        (fun t ht => hf.2 t (Or.inl ht)) n hr
    · exact scalar_iteratedDeriv_zero_of_eqOn hf.1 (uniqueDiffOn_Ici D.b)
        (fun t ht => hf.2 t (Or.inr ht)) n hr

/-- Vanishing of all jets at one point gives every prescribed polynomial
decay order there; this statement has no left/right choice. -/
private theorem scalar_flat_taylor_bound
    {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ n : ℕ, iteratedDeriv n f c = 0) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, |r - c| < δ → |f r| ≤ ε * |r - c| ^ k := by
  have hpoly (r : ℝ) : taylorWithinEval f k univ c r = 0 := by
    simp only [taylor_within_apply, iteratedDerivWithin_univ, hzero,
      smul_zero, Finset.sum_const_zero]
  have ht := taylor_isLittleO_univ (x₀ := c) (hf.of_le (by simp) : ContDiff ℝ k f)
  have hsmall : f =o[𝓝 c] (fun r => (r - c) ^ k) := by
    simpa only [hpoly, sub_zero] using ht
  have hbound : ∀ᶠ r in 𝓝 c, |f r| ≤ ε * |r - c| ^ k := by
    simpa only [Real.norm_eq_abs, abs_pow] using hsmall.bound hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨δ, hδ, fun r hr => hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq] using hr

/-- A globally smooth radial profile supported in the annulus has all the
uniform flat jets used in the scalar weighted interface. -/
theorem EndpointFlat.uniformFlatJets {D : ReferenceData} {f : ℝ → ℝ}
    (hf : EndpointFlat D f) : UniformFlatJets D (fun p => f p.1) := by
  intro a b k ε hε
  cases b with
  | zero =>
    have hg := hf.iteratedDeriv a
    obtain ⟨δl, hδl, hl⟩ := scalar_flat_taylor_bound hg.1
      (fun n => (hg.iteratedDeriv n).2 D.a (Or.inl le_rfl)) k (half_pos hε)
    obtain ⟨δr, hδr, hr⟩ := scalar_flat_taylor_bound hg.1
      (fun n => (hg.iteratedDeriv n).2 D.b (Or.inr le_rfl)) k (half_pos hε)
    refine ⟨min δl δr, lt_min hδl hδr, ?_⟩
    intro r θ hrange _ hnear
    have hd : 0 < endpointDistance D r :=
      lt_min (sub_pos.mpr hrange.1) (sub_pos.mpr hrange.2)
    have hb : |_root_.iteratedDeriv a f r| ≤ ε / 2 * endpointDistance D r ^ k := by
      rcases le_total (r - D.a) (D.b - r) with hle | hle
      · have he : endpointDistance D r = r - D.a := min_eq_left hle
        have hn : |r - D.a| < δl := by
          rw [abs_of_pos (sub_pos.mpr hrange.1), ← he]
          exact hnear.trans_le (min_le_left _ _)
        simpa only [abs_of_pos (sub_pos.mpr hrange.1), ← he] using hl r hn
      · have he : endpointDistance D r = D.b - r := min_eq_right hle
        have hn : |r - D.b| < δr := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hrange.2), ← he]
          exact hnear.trans_le (min_le_right _ _)
        simpa only [abs_sub_comm r D.b, abs_of_pos (sub_pos.mpr hrange.2), ← he]
          using hr r hn
    simp only [mixedDerivative, iteratedDeriv_zero]
    rw [zpow_neg, zpow_natCast, abs_mul, abs_inv, abs_of_pos (pow_pos hd k)]
    calc
      (endpointDistance D r ^ k)⁻¹ * |_root_.iteratedDeriv a f r|
          ≤ (endpointDistance D r ^ k)⁻¹ * (ε / 2 * endpointDistance D r ^ k) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg hd.le k))
      _ = ε / 2 := by
        rw [mul_comm (ε / 2), inv_mul_cancel_left₀ (pow_ne_zero k hd.ne')]
      _ < ε := half_lt_self hε
  | succ b =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro r θ _ _ _
    simpa only [mixedDerivative, iteratedDeriv_const, Nat.succ_ne_zero, ↓reduceIte,
      ite_self, mul_zero, abs_zero] using hε

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateProfile_uniformFlatJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    UniformFlatJets D (fun p => scalarStateProfile D S x p.1) :=
  (scalarStateProfile_endpointFlat hD hT hS x).uniformFlatJets

theorem scalarCommonHeightDecode_periodic
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    Function.Periodic (scalarCommonHeightDecode S u) (0, Real.pi) := by
  have hp := ((hS.1 scalarBeta).2.2.2.1 u.1).2.2.1
  intro p
  simp only [scalarCommonHeightDecode, Prod.fst_add, add_zero, hp p]

theorem scalarStateIncrement_periodic
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    Function.Periodic (scalarStateIncrement S x) (0, Real.pi) :=
  scalarCommonHeightDecode_periodic hS (x.1.1.2, x.1.2)

theorem scalarStateIncrement_periodic_two_pi
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    Function.Periodic (scalarStateIncrement S x) (0, 2 * Real.pi) := by
  have hp := scalarStateIncrement_periodic hS x
  simpa only [Prod.mk_add_mk, zero_add, two_mul] using hp.add_period hp

theorem scalarStateHeight_periodic
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    Function.Periodic (scalarStateHeight D S x) (0, Real.pi) := by
  intro p
  simp only [scalarStateHeight, heightFamily, Radial.radialHeightField,
    Prod.fst_add, add_zero, scalarStateIncrement_periodic hS x p]

/-- A constant extension on any uniquely differentiable radial set gives
both first height jets there. The same proof covers both closed half-lines. -/
private theorem scalar_firstJets_eq_zero_of_constant_on
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) {r c : ℝ} (hr : r ∈ s)
    (hc : ∀ t ∈ s, ∀ θ, u (t, θ) = c) (θ : ℝ) :
    heightRadial u (r, θ) = 0 ∧ heightAngular u (r, θ) = 0 := by
  have hu' := hu.differentiable (by simp)
  have hrad := Radial.hasDerivAt_radialSlice (hu' (r, θ))
  have hconst : HasDerivWithinAt (fun t => u (t, θ)) 0 s r :=
    (hasDerivWithinAt_const r s c).congr_of_mem (fun t ht => hc t ht θ) hr
  have hk : radialPartial u (r, θ) = 0 :=
    (hs r hr).eq_deriv s hrad.hasDerivWithinAt hconst
  have hang := Radial.hasDerivAt_angularSlice (hu' (r, θ))
  have he : (fun t => u (r, t)) = fun _ => c := funext (hc r hr)
  rw [he] at hang
  have ht : angularPartial u (r, θ) = 0 := hang.unique (hasDerivAt_const θ c)
  exact ⟨hk, by rw [heightAngular, ht, zero_div]⟩

private theorem scalar_endpoint_firstJets
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {a b cL cR : ℝ}
    (hL : ∀ r, r ≤ a → ∀ θ, u (r, θ) = cL)
    (hR : ∀ r, b ≤ r → ∀ θ, u (r, θ) = cR) (θ : ℝ) :
    heightRadial u (a, θ) = 0 ∧ heightAngular u (a, θ) = 0 ∧
      heightRadial u (b, θ) = 0 ∧ heightAngular u (b, θ) = 0 := by
  have hl := scalar_firstJets_eq_zero_of_constant_on hu (uniqueDiffOn_Iic a)
    self_mem_Iic hL θ
  have hr := scalar_firstJets_eq_zero_of_constant_on hu (uniqueDiffOn_Ici b)
    self_mem_Ici hR θ
  exact ⟨hl.1, hl.2, hr.1, hr.2⟩

theorem scalarStateIncrement_endpoint_jets
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (hu : ContDiff ℝ ∞ (scalarStateIncrement S x)) (θ : ℝ) :
    heightRadial (scalarStateIncrement S x) (D.a, θ) = 0 ∧
      heightAngular (scalarStateIncrement S x) (D.a, θ) = 0 ∧
      heightRadial (scalarStateIncrement S x) (D.b, θ) = 0 ∧
      heightAngular (scalarStateIncrement S x) (D.b, θ) = 0 := by
  have hv := scalarCommonHeightDecode_endpoint_values hS (x.1.1.2, x.1.2)
  exact scalar_endpoint_firstJets hu hv.1 hv.2 θ

/-- All conditions of the finite-annulus scalar domain follow from the
actual weighted-state geometry; no additional boundary or periodicity premise
is assumed. -/
theorem ScalarStateGeometry.admissibleScalarData
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {x : ScalarWeightedState S} (hg : ScalarStateGeometry D S x) :
    AdmissibleScalarData D.a D.b (scalarStateProfile D S x)
      (scalarStatePrimitive D S x) (scalarStateIncrement S x) x.2 := by
  obtain ⟨C, hC⟩ := hD
  rcases hg with ⟨hw, hh, hu, hhw, hout, _, _, hleft, hright, hpos⟩
  have hz : ContDiff ℝ ∞ (scalarStateHeight D S x) :=
    (hh.comp contDiff_fst).add (contDiff_const.mul hu)
  have hend (θ : ℝ) := scalar_endpoint_firstJets hz hleft hright θ
  have hdisc (r : ℝ) (hr : r = D.a ∨ r = D.b) (θ : ℝ) :
      polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) (r, θ) = 1 := by
    have hrz : scalarStateProfile D S x r = 0 := by
      rcases hr with rfl | rfl
      · exact hout D.a (Or.inl le_rfl)
      · exact hout D.b (Or.inr le_rfl)
    have hk : heightRadial (scalarStateHeight D S x) (r, θ) = 0 := by
      rcases hr with rfl | rfl
      · exact (hend θ).1
      · exact (hend θ).2.2.1
    have hp : heightAngular (scalarStateHeight D S x) (r, θ) = 0 := by
      rcases hr with rfl | rfl
      · exact (hend θ).2.1
      · exact (hend θ).2.2.2
    simp only [polarDiscriminant, heightDiscriminant, profileEnergy, radialEnergy,
      hrz, hk, hp, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, sub_zero, mul_one]
  refine ⟨hC.1.1, hC.1.2.1, hw, hh, hu, hhw,
    scalarStateIncrement_periodic_two_pi hS x,
    hout D.a (Or.inl le_rfl), hout D.b (Or.inr le_rfl),
    scalarStateIncrement_endpoint_jets hS x hu, ?_⟩
  intro r hr θ
  change 0 < polarDiscriminant (scalarStateProfile D S x)
    (scalarStateHeight D S x) (r, θ)
  rcases eq_or_lt_of_le hr.1 with hleft | hleft
  · rw [← hleft, hdisc D.a (Or.inl rfl) θ]
    exact zero_lt_one
  rcases eq_or_lt_of_le hr.2 with hright | hright
  · rw [hright, hdisc D.b (Or.inr rfl) θ]
    exact zero_lt_one
  exact lt_of_lt_of_le (by norm_num) ((hpos r ⟨hleft, hright⟩).2 θ).1

end ContinuousFlexibility.Statements
