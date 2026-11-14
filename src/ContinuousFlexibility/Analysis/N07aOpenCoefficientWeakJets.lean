module

public import ContinuousFlexibility.Analysis.N07aCanonicalRepresentationPairing
public import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# The actual L² classes of the bounded open coefficient jets

Interior integration by parts identifies the angular graph with the
original classical derivatives. The representatives are never replaced
by an assumed smooth extension across an endpoint.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficient

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem jet_toLp_zero (χ : N07aCanonicalOpenCoefficient S K m) :
    (χ.jet 0 0).toLp = χ.toLp := by
  apply Lp.ext
  filter_upwards [(χ.jet 0 0).toLp_ae, χ.toLp_ae] with p hp hq
  exact hp.trans (by simpa only [jet, spaces_mixedDerivative_zero] using hq.symm)

theorem jet_toLp_jet (χ : N07aCanonicalOpenCoefficient S K m) (a b c d : ℕ) :
    ((χ.jet a b).jet c d).toLp = (χ.jet (c + a) (d + b)).toLp := by
  apply Lp.ext
  filter_upwards [((χ.jet a b).jet c d).toLp_ae,
    (χ.jet (c + a) (d + b)).toLp_ae,
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp hq hpU
  exact hp.trans ((n07a_mixedDerivative_mixedDerivative_on
    (isOpen_Ioo.prod isOpen_univ) χ.smooth c d a b hpU).trans hq.symm)

theorem toLp_weakFirst (χ : N07aCanonicalOpenCoefficient S K m) (j : Fin 2) :
    N07aWeakCanonicalMixedDerivative S K m χ.toLp
      (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).toLp
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 := by
  intro φ hφ
  have hleft : (∫ p,
      (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).toLp p * φ p
        ∂canonicalMeasure S K m) =
      ∫ p, mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ.value p * φ p
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [(χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).toLp_ae] with p hp
    exact congrArg (· * φ p) hp
  have hright : (∫ p, χ.toLp p *
      mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p
        ∂canonicalMeasure S K m) =
      ∫ p, χ.value p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [χ.toLp_ae] with p hp
    exact congrArg (· * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p) hp
  rw [hleft, hright, n07aFirstOrder_sum, pow_one, neg_one_mul]
  exact n07a_canonicalOpen_first_pairing χ.smooth χ.periodic hφ j

theorem toLp_weakAngular (χ : N07aCanonicalOpenCoefficient S K m) (n : ℕ) :
    WeakCanonicalAngularDerivative S K m χ.toLp (χ.jet 0 n).toLp n := by
  apply (n07a_weakCanonicalMixed_zero_radial_iff _ _ n).mp
  induction n with
  | zero =>
      rw [χ.jet_toLp_zero]
      exact n07a_weakCanonicalMixed_refl _
  | succ n ih =>
      have horder : n07aFirstOrder (1 : Fin 2) = (0, 1) := by
        norm_num [n07aFirstOrder]
      have h := ih.comp ((χ.jet 0 n).toLp_weakFirst (1 : Fin 2))
      simp only [horder, Prod.fst, Prod.snd, zero_add] at h
      rw [χ.jet_toLp_jet 0 n 0 1] at h
      simpa only [zero_add, Nat.add_comm 1 n] using h

end ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficient
