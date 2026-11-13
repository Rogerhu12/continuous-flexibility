import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N04RealizationCubicOneHighBounds
import ContinuousFlexibility.Analysis.N07aParameterGrading

/-!
# Current jet data through the actual cubic quotient

The positive canonical intervals of the reference-gauged atlas are `(0,1)`.
The numerator is the actual principal difference. Its three zero jets at
each endpoint, supplied by an actual smooth representative, transfer the
current value and parameter estimates to the stored quotient with six
additional radial orders. Pieces on which the divided atom is zero are
handled in the same family, so the tower is defined on every piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- An open-strip bound suffices: the smooth representative extends the
bound to the endpoints by continuity. -/
theorem n04PrincipalDivided_value_of_representative
    {N e : PolarPoint → ℝ}
    (hrep : ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧ EqOn F N unitStrip ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ q ∈ unitStrip, N q = (q.1 * (1 - q.1)) ^ 3 * e q)
    (a b : ℕ) {M : ℝ}
    (hbound : ∀ q ∈ unitStrip, |mixedDerivative (a + 6) b N q| ≤ M)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    |mixedDerivative a b e q| ≤ M / 36 := by
  rcases hrep with ⟨F, hF, he, hz⟩
  have hc : Continuous (fun t : ℝ => |mixedDerivative (a + 6) b F (t, q.2)|) :=
    ((contDiff_mixedDerivative hF (a + 6) b).continuous.comp
      (continuous_id.prodMk continuous_const)).abs
  have hclosed : IsClosed {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} :=
    isClosed_le hc continuous_const
  have hinner : Ioo (0 : ℝ) 1 ⊆
      {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} := by
    intro t ht
    have heq := mixedDerivative_eq_of_eqOn_radialCylinder
      (fun r hr θ => @he (r, θ) ⟨hr, mem_univ _⟩) (a + 6) b (p := (t, q.2)) ht
    change |mixedDerivative (a + 6) b F (t, q.2)| ≤ M
    rw [heq]
    exact hbound (t, q.2) ⟨ht, mem_univ _⟩
  have hboundary : Icc (0 : ℝ) 1 ⊆
      {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr hinner
  apply abs_mixedDerivative_of_twoEndpointCubicFactorization hF zero_lt_one
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hz false)
    (by simpa only [↓reduceIte] using hz true)
    (fun p hp => ?_) a b (fun t ht => hboundary ht) hq.1
  have hp' : p ∈ unitStrip := ⟨hp, mem_univ _⟩
  simpa only [sub_zero] using (he hp').trans (hfactor p hp')

/-- Cubic division preserves the complete current-data interface. The
only extra input is the genuine endpoint representative of the numerator;
all parameter towers and their estimates come from the principal data. -/
theorem n04PrincipalDivided_currentData
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ} (P : ℕ → Prop)
    {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (href : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip ∧
      ∀ q ∈ unitStrip, f₀ m (q + (0, Real.pi)) = f₀ m q)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hrep : ∀ m, P m → ∀ z ∈ sectorNeighborhood S base ε ε,
      ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
        EqOn F (fun q => f z m q - f₀ m q) unitStrip ∧
        ∀ c : Bool, ∀ θ i, i ≤ 2 →
          iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ m, P m → ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
      f z m q - f₀ m q = (q.1 * (1 - q.1)) ^ 3 * g z m q)
    (hzero : ∀ m, ¬ P m → ∀ z ∈ sectorNeighborhood S base ε ε,
      EqOn (g z m) (fun _ => 0) unitStrip)
    (hrefzero : ∀ m, g₀ m = fun _ => 0) :
    CurrentJetDataOn S T cell (fun _ => True) base ε g g₀ := by
  classical
  have hzero₀ : g₀ = fun _ _ => (0 : ℝ) := funext hrefzero
  subst g₀
  let U : Set (Parameter S) := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let I : Type := {m : ℕ // P m}
  let N : I → Parameter S → PolarPoint → ℝ := fun m z q => f z m.val q - f₀ m.val q
  let RN : ∀ m : I, MixedJetRegularity U unitStrip (N m) := fun m =>
    { spatial := fun z hz => (h.1 z hz m.val trivial).1.sub (href m.val).1
      parameter := fun a b q hq => h.2.choose m.val a b ⟨q, hq⟩ }
  have hnum : ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m : I, ∀ a b, a + b ≤ s → ∀ q (hq : q ∈ unitStrip),
      ∀ z ∈ U, ∀ v : Fin k → Parameter S,
        |((RN m).parameter a b q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m.val)) ^ B *
            T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
    intro k
    have ht := h.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m a b hab q hq z hz v
    exact (ht.choose_spec s).choose_spec.2 z hz v m.val trivial ⟨q, hq⟩ a b hab
  have hout := n04Realization_unitCubic_oneHigh_bounds hU
    (parameterGrading S) (n07aParameterGrading_withSeminorms S)
    (n07aParameterGrading_monotone S) base
    (fun m : I => T.E0 (T.sample (cell m.val)))
    (fun m : I => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ))
    (fun _ : I => (1 : ℝ)) (fun m => hE m.val)
    (fun m => Real.rpow_nonneg (hH m.val) _) (fun _ => zero_lt_one)
    (bw := 1) zero_lt_one
    (fun m => by simpa only [inv_one, Real.rpow_one, one_mul] using hE m.val)
    N (fun m z => g z m.val) RN
    (fun m => hrep m.val m.property)
    (fun m z hz q hq => by
      simpa only [one_pow, one_mul] using hfactor m.val m.property z hz q hq) hnum
  let RE : ∀ m : I, MixedJetRegularity U unitStrip (fun z => g z m.val) := hout.choose
  have hRE := hout.choose_spec
  have hnegJet (m : ℕ) (hm : ¬ P m) (a b : ℕ) (q : unitStrip)
      (z : Parameter S) (hz : z ∈ U) :
      mixedDerivative a b (fun y => g z m y - 0) q.val = 0 := by
    simp only [sub_zero]
    calc
      mixedDerivative a b (g z m) q.val =
          mixedDerivative a b (fun _ : PolarPoint => (0 : ℝ)) q.val :=
        mixedDerivative_eq_of_eqOn_radialCylinder
          (fun r hr θ => hzero m hm z hz ⟨hr, mem_univ _⟩) a b q.property.1
      _ = 0 := mixedDerivative_fun_zero a b q.val
  let J : ∀ m (a b : ℕ) (q : unitStrip), SmoothDirections U
      (fun z => mixedDerivative a b (fun y => g z m y - 0) q.val) := fun m a b q =>
    if hm : P m then
      ((RE ⟨m, hm⟩).parameter a b q.val q.property).congr
        (fun _ _ => by simp only [sub_zero])
    else (smoothDirections_constant hU (0 : ℝ)).congr
      (fun z hz => (hnegJet m hm a b q z hz).symm)
  have hJDpos (m : ℕ) (hm : P m) (a b : ℕ) (q : unitStrip)
      (k : ℕ) (z : Parameter S) (hz : z ∈ U) (v : Fin k → Parameter S) :
      (J m a b q).D k z v = ((RE ⟨m, hm⟩).parameter a b q.val q.property).D k z v := by
    exact congrArg (fun A : Parameter S [×k]→L[ℝ] ℝ => A v)
      (HasProjectiveJetsOn.unique hU (J m a b q).hasProjectiveJetsOn
        (((RE ⟨m, hm⟩).parameter a b q.val q.property).congr
          (fun _ _ => by simp only [sub_zero])).hasProjectiveJetsOn k z hz)
  have hJDneg (m : ℕ) (hm : ¬ P m) (a b : ℕ) (q : unitStrip)
      (k : ℕ) (z : Parameter S) (hz : z ∈ U) (v : Fin k → Parameter S) :
      (J m a b q).D k z v = 0 := by
    have he := n04Realization_smoothDirections_D_const_mul
      (J m a b q) (J m a b q) 0
      (fun y hy => by rw [hnegJet m hm a b q y hy, zero_mul]) k hz v
    simpa only [zero_mul] using he
  refine ⟨?_, J, ?_, ?_⟩
  · intro z hz m _
    have hshift (q : PolarPoint) (hq : q ∈ unitStrip) :
        q + (0, Real.pi) ∈ unitStrip := by
      exact ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
    by_cases hm : P m
    · refine ⟨(RE ⟨m, hm⟩).spatial z hz, ?_⟩
      intro q hq
      have hn : (q.1 * (1 - q.1)) ^ 3 ≠ 0 :=
        pow_ne_zero 3 (mul_pos hq.1.1 (sub_pos.mpr hq.1.2)).ne'
      apply mul_left_cancel₀ hn
      have hf1 := hfactor m hm z hz (q + (0, Real.pi)) (hshift q hq)
      have hf0 := hfactor m hm z hz q hq
      simpa only [Prod.fst_add, add_zero, (h.1 z hz m trivial).2 q hq,
        (href m).2 q hq, hf0] using hf1.symm
    · refine ⟨contDiffOn_const.congr (fun q hq => (hzero m hm z hz hq).symm), ?_⟩
      intro q hq
      exact (hzero m hm z hz (hshift q hq)).trans (hzero m hm z hz hq).symm
  · have hv := h.2.choose_spec.1
    refine ⟨hv.choose + 6, fun s => ⟨(hv.choose_spec (s + 6)).choose,
      (hv.choose_spec (s + 6)).choose_spec.1, ?_⟩⟩
    intro z hz m _ q a b hab
    let B : ℝ := (hv.choose_spec (s + 6)).choose
    let M : ℝ := B * T.E0 (T.sample (cell m)) ^ B *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + (hv.choose + 6)) z
    have hM : 0 ≤ M := mul_nonneg
      (mul_nonneg (mul_nonneg (hv.choose_spec (s + 6)).choose_spec.1.le
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
        (Real.rpow_nonneg (hH m) _)) (apply_nonneg _ _)
    by_cases hm : P m
    · have hb' : ∀ p ∈ unitStrip,
          |mixedDerivative (a + 6) b (fun y => f z m y - f₀ m y) p| ≤ M := by
        intro p hp
        have he : s + 6 + hv.choose = s + (hv.choose + 6) := by omega
        have hh := (hv.choose_spec (s + 6)).choose_spec.2
          z hz m trivial ⟨p, hp⟩ (a + 6) b (by omega)
        exact he ▸ hh
      have hb := n04PrincipalDivided_value_of_representative
        (hrep m hm z hz) (hfactor m hm z hz) a b hb' q.property
      simp only [sub_zero]
      exact hb.trans (div_le_self hM (by norm_num))
    · rw [hnegJet m hm a b q z hz, abs_zero]
      exact hM
  · intro k
    have ht := hRE k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v m _ q a b hab
    by_cases hm : P m
    · rw [hJDpos m hm a b q k z hz v]
      exact (ht.choose_spec s).choose_spec.2 ⟨m, hm⟩ a b hab q.val q.property z hz v
    · rw [hJDneg m hm a b q k z hz v, abs_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (ht.choose_spec s).choose_spec.1.le
          (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
          (Real.rpow_nonneg (hH m) _)) (oneHighVariationWeight_nonneg _ _ _ _ _)

end ContinuousFlexibility.Analysis
