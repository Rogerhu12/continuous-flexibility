import ContinuousFlexibility.Analysis.N04NegativeHeightScalarData
import ContinuousFlexibility.Analysis.N04NegativeHeightProductBounds
import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceProduct

/-! Multiplication of current scalar families on selected negative pieces.
The low order and the neighborhood are chosen before the parameter order.
The full product jet retains the sampled height gain, and its first jet
controls the reference difference on the same neighborhood. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ}
  {f₀ g₀ : ℕ → PolarPoint → ℝ}

/-- Products preserve the selected current-data estimate on a smaller
state neighborhood selected before every parameter and spatial order. -/
theorem CurrentJetDataOn.height_mul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hg : CurrentJetDataOn S T cell P base ε g g₀)
    (hf₀ : N04HeightReferenceDataOn T cell P f₀)
    (hg₀ : N04HeightReferenceDataOn T cell P g₀)
    (hfzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    (hgzero : ∀ m, P m → ∀ q ∈ unitStrip, g 0 m q = g₀ m q) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε'
        (fun z m q => f z m q * g z m q) (fun m q => f₀ m q * g₀ m q) := by
  classical
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  let F : Fin 2 → Parameter S → ℕ → PolarPoint → ℝ :=
    Fin.cases f (fun _ : Fin 1 => g)
  let F₀ : Fin 2 → ℕ → PolarPoint → ℝ := Fin.cases f₀ (fun _ : Fin 1 => g₀)
  have hF : ∀ l, CurrentJetDataOn S T cell P base ε (F l) (F₀ l) :=
    Fin.cases (motive := fun l => CurrentJetDataOn S T cell P base ε (F l) (F₀ l))
      hf (fun _ => hg)
  have hF₀ : ∀ l, N04HeightReferenceDataOn T cell P (F₀ l) :=
    Fin.cases (motive := fun l => N04HeightReferenceDataOn T cell P (F₀ l))
      hf₀ (fun _ => hg₀)
  have hFzero : F 0 = f := by simp only [F, Fin.cases_zero]
  have hFone : F 1 = g := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
    simp only [F, Fin.cases_succ]
  let RF : ∀ l m, P m → MixedJetRegularity U unitStrip (fun z => F l z m) :=
    fun l m hm => (hF l).height_regularity (hF₀ l) m hm
  let RG : ∀ m, P m → MixedJetRegularity U unitStrip
      (fun z q => f z m q * g z m q) :=
    fun m hm => (hf.height_regularity hf₀ m hm).mul
      (hg.height_regularity hg₀ m hm) hU hΩ
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  obtain ⟨RH, hRH, hheight⟩ := material_sample_height_coefficient_power_bounded hD hT cell 0
    (by norm_num : (0 : ℝ) < 3 / 4)
  have hHR (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH := by
    simpa only [Real.rpow_zero, mul_one] using hheight m
  have ht := fun l : Fin 2 => (hF l).height_fullTower hD hT (hF₀ l) hE
  let L : ℕ → ℕ := fun k => ∑ l : Fin 2, (ht l k).choose
  have hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t : Fin 2 × {m // P m}, ∀ q (hq : q ∈ unitStrip) a b, a + b ≤ s →
      ∀ z ∈ U, ∀ v : Fin k → Parameter S,
        |((RF t.1 t.2.val t.2.property).parameter a b q hq).D k z v| ≤
          B * T.E0 (T.sample (cell t.2.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell t.2.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    intro k s
    let C : Fin 2 → ℝ := fun l => ((ht l k).choose_spec s).choose
    have hC (l : Fin 2) : 0 < C l := ((ht l k).choose_spec s).choose_spec.1
    let B : ℝ := 1 + ∑ l : Fin 2, C l
    have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun l _ => (hC l).le))
    have hCB (l : Fin 2) : C l ≤ B :=
      (Finset.single_le_sum (fun n _ => (hC n).le) (Finset.mem_univ l)).trans
        (le_add_of_nonneg_left zero_le_one)
    refine ⟨B, hB, ?_⟩
    intro t q hq a b hab z hz v
    have hbase := ((ht t.1 k).choose_spec s).choose_spec.2
      t.2.val t.2.property q hq a b hab ((RF t.1 t.2.val t.2.property).parameter a b q hq)
      z hz v
    have hcoef : C t.1 * T.E0 (T.sample (cell t.2.val)) ^ C t.1 ≤
        B * T.E0 (T.sample (cell t.2.val)) ^ B :=
      mul_le_mul (hCB t.1) (Real.rpow_le_rpow_of_exponent_le (hE t.2.val) (hCB t.1))
        (Real.rpow_nonneg (zero_le_one.trans (hE t.2.val)) _) hB.le
    have horder : (ht t.1 k).choose ≤ L k :=
      Finset.single_le_sum (fun l _ => Nat.zero_le ((ht l k).choose)) (Finset.mem_univ t.1)
    have hweight := oneHighVariationWeight_mono hp (le_rfl : base ≤ base)
      (Nat.add_le_add_left horder s) z v
    exact hbase.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hcoef
        (parameterHeightWeight_nonneg (Real.rpow_nonneg (hH t.2.val) _) k)) hweight
      (oneHighVariationWeight_nonneg _ _ _ _ _)
      (mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE t.2.val)) _))
        (parameterHeightWeight_nonneg (Real.rpow_nonneg (hH t.2.val) _) k)))
  obtain ⟨b', hb', hprefix⟩ := n04SourceColumns_prefix_power
    (parameterGrading S) hp hI base L
    (fun t : Fin 2 × {m // P m} => T.E0 (T.sample (cell t.2.val)))
    (fun k t => parameterHeightWeight (T.H (T.sample (cell t.2.val)) ^ (3 / 4 : ℝ)) k)
    (fun t => hE t.2.val)
    (fun k t => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH t.2.val) _) k)
    (fun t z => F t.1 z t.2.val) (fun t => RF t.1 t.2.val t.2.property) hbound
  let ε' : ℝ := min ε (1 / 2)
  let U' := sectorNeighborhood S b' ε' ε'
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hU' : IsOpen U' := isOpen_sectorNeighborhood S b' ε' ε'
  have hsub : U' ⊆ U := sectorNeighborhood_mono S hb' hεε hεε
  let R' : ∀ m, P m → MixedJetRegularity U' unitStrip
      (fun z q => f z m q * g z m q) :=
    fun m hm => (RG m hm).height_restrict hU' hsub
  have hlow : ∀ z ∈ U', parameterGrading S b' z ≤ 1 :=
    fun z hz => n04NegativeHeight_parameterGrading_le_one (min_le_right ε (1 / 2)) hz
  refine ⟨b', ε', hb', hε', hεε, CurrentJetDataOn.of_positive_towers hε' hE hH R'
    (fun z hz m hm q hq => by
      rw [(hf.1 z (hsub hz) m hm).2 q hq, (hg.1 z (hsub hz) m hm).2 q hq])
    (fun m hm => (hf₀.1 m hm).1.mul (hg₀.1 m hm).1)
    (fun m hm q hq => by rw [hfzero m hm q hq, hgzero m hm q hq]) hlow ?_⟩
  intro k hk
  obtain ⟨shift, hshift⟩ := hprefix k
  refine ⟨b' + shift * k + 1, fun s => ?_⟩
  obtain ⟨A, hA, hraw⟩ := hshift s
  obtain ⟨B, hB, hprod⟩ := n04NegativeHeight_product_positive_oneHigh
    (X := Parameter S) 2 k s shift RH
  let M : ℝ := 1 + A
  have hM : 1 ≤ M := le_add_of_nonneg_right hA.le
  have hAM : A ≤ M := le_add_of_nonneg_left zero_le_one
  obtain ⟨Q, hQ, hpack⟩ := coefficientEnvelope_pack (B * M ^ 2) (M * (2 : ℝ))
  refine ⟨Q, hQ, ?_⟩
  intro m hm q hq a b hab z hz v
  let E : ℝ := T.E0 (T.sample (cell m))
  have hE0 : 1 ≤ E := hE m
  have hME : 1 ≤ M * E ^ M := one_le_mul_of_one_le_of_one_le hM
    (Real.one_le_rpow hE0 (zero_le_one.trans hM))
  have hAE : A * E ^ A ≤ M * E ^ M := mul_le_mul hAM
    (Real.rpow_le_rpow_of_exponent_le hE0 hAM)
    (Real.rpow_nonneg (zero_le_one.trans hE0) _) (zero_le_one.trans hM)
  have hraw' (l : Fin 2) (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ s)
      (d : Fin j → Parameter S) (hd : ∀ i, parameterGrading S b' (d i) ≤ 1)
      (R : ℝ) (hR : 1 ≤ R)
      (hzR : parameterGrading S (s + (b' + shift * k + 1)) (z - 0) ≤ R)
      (hdR : ∀ i, parameterGrading S (s + (b' + shift * k + 1)) (d i) ≤ R) :
      ‖((RF l m hm).parameter u w q hq).D j z d‖ ≤ M * E ^ M *
        parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + shift * k : ℕ) : ℝ) + 1)) := by
    have hr := hraw j hj (l, ⟨m, hm⟩) q hq u w huw z (hsub hz) (hlow z hz) d hd R hR
      (by simpa only [sub_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hzR)
      (fun i => by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdR i)
    rw [Real.norm_eq_abs]
    exact hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAE
        (parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m) _) j))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
  let Jprod : SmoothDirections U
      (fun y => mixedDerivative a b (fun p => ∏ l : Fin 2, F l y m p) q) :=
    ((RG m hm).parameter a b q hq).congr (fun y hy => by
      have he : (fun p => ∏ l : Fin 2, F l y m p) =
          (fun p => f y m p * g y m p) := by
        funext p
        simp only [Fin.prod_univ_two, hFzero, hFone]
      rw [he])
  have hresult := hprod (parameterGrading S) 0 b' (s + (b' + shift * k + 1))
    U hU unitStrip hΩ (fun l y => F l y m) (fun l => RF l m hm) q hq
    (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) (M * E ^ M)
    (Real.rpow_nonneg (hH m) _) (hHR m) hME z (hsub hz)
    (by simpa only [sub_zero] using hlow z hz) hraw'
    k le_rfl hk a b hab Jprod v
  have hcost := mul_le_mul_of_nonneg_right (hpack E hE0)
    (mul_nonneg (Real.rpow_nonneg (hH m) _)
      (oneHighVariationWeight_nonneg (parameterGrading S) b'
        (s + (b' + shift * k + 1)) z v))
  have hpow : B * (M * E ^ M) ^ 2 = (B * M ^ 2) * E ^ (M * (2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE0)]
    ring
  simpa only [R', MixedJetRegularity.height_restrict, SmoothDirections.restrict,
    Jprod, SmoothDirections.congr, Real.norm_eq_abs, sub_zero, hpow, mul_assoc] using
    hresult.trans (by simpa only [sub_zero, hpow, mul_assoc] using hcost)

end ContinuousFlexibility.Analysis
