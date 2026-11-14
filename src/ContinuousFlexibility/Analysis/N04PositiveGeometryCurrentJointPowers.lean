module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryJointNormalization
public import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentData
public import ContinuousFlexibility.Analysis.N04PrincipalTowerValue

/-!
# Current data from positive joint powers on the actual unit strip

All spatial directions are appended before normalizing the parameter
multilinear map. The state arity remains the requested positive order,
and the spatial order occurs with coefficient one in the final loss.
-/

@[expose] public section

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

theorem CurrentJetDataOn.of_positiveJointUnitPower
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hperiod : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (href : ∀ m, P m → f₀ m = f 0 m)
    (J : ∀ m, P m → SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun z : Parameter S × PolarPoint => f z.1 m z.2))
    (hraw : ∀ k : ℕ, 0 < k → ∃ shift : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ hm : P m,
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (base + s + shift * k + 1) z ≤ R →
      ∀ n : ℕ, n ≤ k + s → ∀ w : StateAngleWord n, w.stateArity = k →
      ∀ v : Fin n → Parameter S × PolarPoint,
      (∀ i, parameterGrading S base (v i).1 ≤ 1) →
      (∀ i, parameterGrading S (base + s + shift * k + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        |(J m hm).D n (z, q) v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            R ^ (((w.angleArity + shift * k : ℕ) : ℝ) / ((s + shift * k : ℕ) + 1))) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  have hU := isOpen_sectorNeighborhood S base ε ε
  have hV : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood S base ε ε ×ˢ unitStrip) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo _ _).prod convex_univ)
  let Q : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q.val) := fun m hm i j q =>
    (n04Realization_jointMixedRegularity (J m hm) hU hV hc).parameter i j q.val q.property
  apply CurrentJetDataOn.of_positiveParameterJets hε hE hH
    (fun _ hz => n04Principal_parameter_low_le_one hεhalf hz)
    (fun z hz m hm => ⟨(J m hm).spatial_value_contDiffOn hV z hz, hperiod z hz m hm⟩)
    href Q
  intro k hk
  let sd := hraw k hk
  let shift : ℕ := sd.choose
  refine ⟨base + shift * k + 1, fun s => ?_⟩
  let bd := sd.choose_spec s
  let B : ℝ := bd.choose
  have hB : 0 < B := bd.choose_spec.1
  refine ⟨B, hB, fun z hz v m hm q a b hab => ?_⟩
  let high : ℕ := base + s + shift * k + 1
  let exponent : ℝ := ((s + shift * k : ℕ) : ℝ) / ((s + shift * k : ℕ) + 1)
  let M : ℝ := B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    (Real.rpow_nonneg (hH m) _)
  have hden : (0 : ℝ) < ((s + shift * k : ℕ) : ℝ) + 1 := by positivity
  have he : exponent ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hnormalized : ∀ R : ℝ, 1 ≤ R → parameterGrading S high (z - 0) ≤ R →
      ∀ n : ℕ, n ≤ k + a + b → ∀ w : StateAngleWord n, w.stateArity = k →
      ∀ u : Fin n → Parameter S × PolarPoint,
      (∀ i, parameterGrading S base (u i).1 ≤ 1) →
      (∀ i, parameterGrading S high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
        |(J m hm).D n (z, q.val) u| ≤ M * R ^ exponent := by
    intro R hR hzR n hn w hw u huL huH huS hu0 hu1
    have hn' : n ≤ k + s := by omega
    have hangle : w.angleArity ≤ s := by have := w.arity_sum; omega
    have hb' := bd.choose_spec.2 m hm z hz q.val q.property R hR
      (by simpa only [sub_zero] using hzR) n hn' w hw u huL huH huS hu0 hu1
    have hexp : (((w.angleArity + shift * k : ℕ) : ℝ) /
        ((s + shift * k : ℕ) + 1)) ≤ exponent := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast Nat.add_le_add_right hangle (shift * k)
    exact hb'.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR hexp) hM)
  have hb := n04PositiveGeometry_mixed_oneHigh_of_jointUnitPower (J m hm) hU hV hc
    (parameterGrading S) base high 0 k a b z hz q.val q.property hM he
    hnormalized (Q m hm a b q) v
  have hhigh : high = s + (base + shift * k + 1) := by dsimp only [high]; omega
  simpa only [M, sub_zero, hhigh] using hb

/-- A fixed reference pullback may first be evaluated at the level of
the true mixed parameter jets. The same final normalization applies. -/
theorem CurrentJetDataOn.of_positiveMixedUnitPower
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hregular : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ContDiffOn ℝ ∞ (f z m) unitStrip ∧
        ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (href : ∀ m, P m → f₀ m = f 0 m)
    (J : ∀ m, P m → ∀ a b (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative a b (f z m) q.val))
    (hraw : ∀ k : ℕ, 0 < k → ∃ shift : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ hm : P m,
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (base + s + shift * k + 1) z ≤ R →
      ∀ v : Fin k → Parameter S,
      (∀ i, parameterGrading S base (v i) ≤ 1) →
      (∀ i, parameterGrading S (base + s + shift * k + 1) (v i) ≤ R) →
        |(J m hm a b q).D k z v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            R ^ (((a + b + shift * k : ℕ) : ℝ) / ((s + shift * k : ℕ) + 1))) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  apply CurrentJetDataOn.of_positiveParameterJets hε hE hH
    (fun _ hz => n04Principal_parameter_low_le_one hεhalf hz) hregular href J
  intro k hk
  let sd := hraw k hk
  let shift : ℕ := sd.choose
  refine ⟨base + shift * k + 1, fun s => ?_⟩
  let bd := sd.choose_spec s
  let B : ℝ := bd.choose
  have hB : 0 < B := bd.choose_spec.1
  refine ⟨B, hB, fun z hz v m hm q a b hab => ?_⟩
  let high : ℕ := base + s + shift * k + 1
  let exponent : ℝ := ((a + b + shift * k : ℕ) : ℝ) / ((s + shift * k : ℕ) + 1)
  let M : ℝ := B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    (Real.rpow_nonneg (hH m) _)
  have hden : (0 : ℝ) < ((s + shift * k : ℕ) : ℝ) + 1 := by positivity
  have hnum : ((a + b + shift * k : ℕ) : ℝ) ≤ ((s + shift * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hab (shift * k)
  have he : exponent ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hb := weightedMultilinear_oneHigh_of_unitPower (parameterGrading S) base high z
    ((J m hm a b q).D k z) (δ := 1) zero_le_one hM he
    (fun u hu R hR hzR huR => by
      simpa only [one_mul] using bd.choose_spec.2 m hm z hz q a b hab R hR hzR u hu huR)
  have hhigh : high = s + (base + shift * k + 1) := by dsimp only [high]; omega
  simpa only [M, one_mul, hhigh] using hb v

end ContinuousFlexibility.Analysis
