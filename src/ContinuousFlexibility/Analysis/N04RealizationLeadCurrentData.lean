import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
import ContinuousFlexibility.Analysis.NonlinearNeighborhoodRestriction

/-!
# Jet-difference towers of scalar families

`CurrentJetDataOn` is the per-family form of the `CurrentJets` clause:
current regularity and π-periodicity, a smooth directional tower of the
spatial jets of the difference with a reference family, one value bound and
one tower bound with the cost `B * E0^B * H^(3/4)` at the sample of the piece.
It is restricted to the pieces satisfying a predicate, so that negative and
positive pieces can be supplied separately and combined. The derivative
tower, as well as its estimates, is required only on those pieces.
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

/-- Jet-difference towers of a scalar family on the unit strip, on the pieces
satisfying `P`, with the cost of `CurrentJets`. -/
def CurrentJetDataOn (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (P : ℕ → Prop) (base : ℕ) (ε : ℝ)
    (f : Parameter S → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  (∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
    ContDiffOn ℝ ∞ (f z m) unitStrip ∧
      ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q) ∧
  ∃ J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val),
    (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → ∀ (q : unitStrip) (i j : ℕ),
        i + j ≤ s →
        |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            parameterGrading S (s + loss) z) ∧
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S, ∀ m (hm : P m),
        ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |(J m hm i j q).D k z v| ≤
            B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading S) base (s + loss) z v

section Calculus

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

private theorem parameterGrading_monotone' (S : PhysicalSpacesData) :
    Monotone (parameterGrading S) :=
  tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)

/-- Raising the weight in a bound with a nonnegative cost. -/
private theorem costWeight_le {B e h w w' x : ℝ} (hB : 0 ≤ B) (he : 0 ≤ e) (hh : 0 ≤ h)
    (hw : w ≤ w') (hx : x ≤ B * e ^ B * h ^ (3 / 4 : ℝ) * w) :
    x ≤ B * e ^ B * h ^ (3 / 4 : ℝ) * w' :=
  hx.trans (mul_le_mul_of_nonneg_left hw
    (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg he _)) (Real.rpow_nonneg hh _)))

/-- A smaller neighborhood and fewer pieces keep the data. -/
theorem CurrentJetDataOn.mono {P P' : ℕ → Prop} {base base' : ℕ} {ε ε' : ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀) (hP : ∀ m, P' m → P m)
    (hb : base ≤ base') (hε : ε' ≤ ε)
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (cell m))) (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P' base' ε' f f₀ := by
  have hsub : sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hb hε hε
  have hopen : IsOpen (sectorNeighborhood S base' ε' ε') :=
    isOpen_sectorNeighborhood S base' ε' ε'
  have hJ := h.2
  refine ⟨fun z hz m hm => h.1 z (hsub hz) m (hP m hm),
    fun m hm i j q => (hJ.choose m (hP m hm) i j q).restrict hopen hsub, ?_, ?_⟩
  · have hv := hJ.choose_spec.1
    exact ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose, (hv.choose_spec s).choose_spec.1,
      fun z hz m hm q i j hij =>
        (hv.choose_spec s).choose_spec.2 z (hsub hz) m (hP m hm) q i j hij⟩⟩
  · intro k
    have ht := hJ.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, fun z hz v m hm q i j hij => ?_⟩⟩
    have h1 := (ht.choose_spec s).choose_spec.2 z (hsub hz) v m (hP m hm) q i j hij
    exact costWeight_le (ht.choose_spec s).choose_spec.1.le (hE m) (hH m)
      (oneHighVariationWeight_mono (parameterGrading_monotone' S) hb le_rfl z v) h1

/-- Raising the constant, the exponent and the grading in a bound. -/
private theorem cost_raise {B B' e h g g' x : ℝ} (hB : 0 < B) (hBB : B ≤ B') (he : 1 ≤ e)
    (hh : 0 ≤ h) (hg : 0 ≤ g) (hgg : g ≤ g')
    (hx : x ≤ B * e ^ B * h ^ (3 / 4 : ℝ) * g) :
    x ≤ B' * e ^ B' * h ^ (3 / 4 : ℝ) * g' := by
  have he0 : 0 ≤ e := zero_le_one.trans he
  have h1 : B * e ^ B ≤ B' * e ^ B' :=
    mul_le_mul hBB (Real.rpow_le_rpow_of_exponent_le he hBB) (Real.rpow_nonneg he0 _)
      (hB.le.trans hBB)
  have hH : 0 ≤ h ^ (3 / 4 : ℝ) := Real.rpow_nonneg hh _
  calc x ≤ B * e ^ B * h ^ (3 / 4 : ℝ) * g := hx
    _ ≤ B' * e ^ B' * h ^ (3 / 4 : ℝ) * g' :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1 hH) hgg hg
        (mul_nonneg (mul_nonneg (hB.le.trans hBB) (Real.rpow_nonneg he0 _)) hH)

/-- Data on two families of pieces combine to data on every piece they cover. -/
theorem CurrentJetDataOn.union {P Q R : ℕ → Prop} {base : ℕ} {ε : ℝ}
    (hP : CurrentJetDataOn S T cell P base ε f f₀)
    (hQ : CurrentJetDataOn S T cell Q base ε f f₀) (hcover : ∀ m, R m → P m ∨ Q m)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell R base ε f f₀ := by
  have hmono := parameterGrading_monotone' S
  have htP := hP.2.choose_spec.2
  have htQ := hQ.2.choose_spec.2
  -- uniform tower constants, chosen before the piece
  let lP : ℕ → ℕ := fun k => (htP k).choose
  let lQ : ℕ → ℕ := fun k => (htQ k).choose
  let BP : ℕ → ℕ → ℝ := fun k s => ((htP k).choose_spec s).choose
  let BQ : ℕ → ℕ → ℝ := fun k s => ((htQ k).choose_spec s).choose
  have hBP : ∀ k s, 0 < BP k s := fun k s => ((htP k).choose_spec s).choose_spec.1
  have hBQ : ∀ k s, 0 < BQ k s := fun k s => ((htQ k).choose_spec s).choose_spec.1
  have hpiece : ∀ m, R m → ∃ Jm : ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val),
      ∀ (k s : ℕ), ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |(Jm i j q).D k z v| ≤
            max (BP k s) (BQ k s) * T.E0 (T.sample (cell m)) ^ max (BP k s) (BQ k s) *
              T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
                oneHighVariationWeight (parameterGrading S) base (s + max (lP k) (lQ k)) z v :=
    fun m hm => (hcover m hm).elim
      (fun hPm => ⟨hP.2.choose m hPm, fun k s z hz v q i j hij =>
        cost_raise (hBP k s) (le_max_left _ _) (hE m) (hH m)
          (oneHighVariationWeight_nonneg _ _ _ _ _)
          (oneHighVariationWeight_mono (base := base) (base' := base) hmono le_rfl
            (Nat.add_le_add_left (le_max_left _ _) s) z v)
          (((htP k).choose_spec s).choose_spec.2 z hz v m hPm q i j hij)⟩)
      (fun hQm => ⟨hQ.2.choose m hQm, fun k s z hz v q i j hij =>
        cost_raise (hBQ k s) (le_max_right _ _) (hE m) (hH m)
          (oneHighVariationWeight_nonneg _ _ _ _ _)
          (oneHighVariationWeight_mono (base := base) (base' := base) hmono le_rfl
            (Nat.add_le_add_left (le_max_right _ _) s) z v)
          (((htQ k).choose_spec s).choose_spec.2 z hz v m hQm q i j hij)⟩)
  have hvP := hP.2.choose_spec.1
  have hvQ := hQ.2.choose_spec.1
  refine ⟨fun z hz m hm => (hcover m hm).elim (hP.1 z hz m) (hQ.1 z hz m),
    fun m hm => (hpiece m hm).choose, ⟨max hvP.choose hvQ.choose, fun s => ?_⟩,
    fun k => ⟨max (lP k) (lQ k), fun s => ⟨max (BP k s) (BQ k s),
      lt_max_of_lt_left (hBP k s), fun z hz v m hm q i j hij =>
        (hpiece m hm).choose_spec k s z hz v q i j hij⟩⟩⟩
  have hsP := hvP.choose_spec s
  have hsQ := hvQ.choose_spec s
  exact ⟨max hsP.choose hsQ.choose, lt_max_of_lt_left hsP.choose_spec.1,
    fun z hz m hm q i j hij => (hcover m hm).elim
      (fun hPm => cost_raise hsP.choose_spec.1 (le_max_left _ _) (hE m) (hH m)
        (apply_nonneg _ _) (hmono (Nat.add_le_add_left (le_max_left _ _) s) z)
        (hsP.choose_spec.2 z hz m hPm q i j hij))
      (fun hQm => cost_raise hsQ.choose_spec.1 (le_max_right _ _) (hE m) (hH m)
        (apply_nonneg _ _) (hmono (Nat.add_le_add_left (le_max_right _ _) s) z)
        (hsQ.choose_spec.2 z hz m hQm q i j hij))⟩

end Calculus

end ContinuousFlexibility.Analysis
