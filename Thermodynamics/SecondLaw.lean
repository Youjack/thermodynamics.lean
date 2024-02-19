import Thermodynamics.Cycle

/-!
# The SECOND Law and Carnot Theorem

This file defines
* the notion of `possible` `Cycle`, that is, `Cycle` that satisfies the second law
  `possible` is abbreviated as `psbl`
* the notion of `reversible` `Cycle`
  `reversible` is abbreviated as `rvsbl`
and states
* axioms stating that connection and scaling preserve the possibility of `Cycle`s,
  i.e. `Cycle.possible_add` and `Cycle.possible_smul_nonneg`
* the axiom of the second law, i.e. `kelvin_stmt` and `clausius_stmt`
and proves
* the equivalence of Kelvin-Plank statement and Clausius statement (under certain assumptions)
* Carnot theorem
-/

namespace Thermodynamics

/-!
## `possible` `Cycle`s
---------------------------------------------------------------------------------------------------/

namespace Cycle

/-- abstract `Cycle` that is possible according to the second law -/
axiom possible : Cycle → Prop
/-- The trivial `Cycle` is possible. -/
axiom trivial_possible : (0:Cycle).possible

/-- The connection of two possible `Cycle`s is possible.
* Note that a connection of possible and impossible can be possible.
-/
axiom possible_add {H₁ H₂ : Cycle} : H₁.possible → H₂.possible → (H₁ + H₂).possible
/-- The scaling of a possible `Cycle` by a nonnegative is possible. -/
axiom possible_smul_nonneg {c : ℝ} {H : Cycle} : 0 ≤ c → H.possible → (c • H).possible

end Cycle

/-!
## `reversible` `Cycle`s
---------------------------------------------------------------------------------------------------/

namespace Cycle

def reversible (H : Cycle) := H.possible ∧ (-H).possible

lemma trvial_reversible : (0:Cycle).reversible := by
  constructor
  . exact trivial_possible
  . rw [neg_zero]
    exact trivial_possible
lemma reversible_add {H₁ H₂ : Cycle} : H₁.reversible → H₂.reversible → (H₁ + H₂).reversible := by
  intro ⟨h₁psbl,h₁rev_psbl⟩ ⟨h₂psbl,h₂rev_psbl⟩
  constructor
  . exact possible_add h₁psbl h₂psbl
  . rw [neg_add]
    exact possible_add h₁rev_psbl h₂rev_psbl
lemma reversible_smul_nonneg {c : ℝ} {H : Cycle} : 0 ≤ c → H.reversible → (c • H).reversible := by
  intro hc ⟨hpsbl,hrev_psbl⟩
  constructor
  . exact possible_smul_nonneg hc hpsbl
  . rw [←smul_neg]
    exact possible_smul_nonneg hc hrev_psbl

end Cycle

/-!
## Kelvin and Clausius statements
---------------------------------------------------------------------------------------------------/

/-!
### Assumption of the existence of `possible` `UsualEngineCycle`s
-/

namespace UsualEngineCycle

/-- There exists a possible `UsualEngineCycle` between any `𝓒 < 𝓗`. -/
@[reducible] def ExistsPossible :=
  ∀ {𝓒 𝓗}, ∀ 𝓒_lt_𝓗 : 𝓒 < 𝓗, ∃ H : UsualEngineCycle 𝓒_lt_𝓗, H.possible

variable (exists_psbl : ExistsPossible)
variable {𝓗 𝓒 : Reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)
variable {Q : ℝ} (hQ : 0 < Q)
/-- There exists possible `UsualEngineCycle 𝓒_lt_𝓗` that absorbs a certain heat `Q > 0`. -/
lemma exists_psbl_abs : ∃ H : UsualEngineCycle 𝓒_lt_𝓗, H.possible ∧ H.Qabs = Q := by
  let ⟨H',hH'⟩ := exists_psbl 𝓒_lt_𝓗
  let c : ℝ>0 := ⟨Q / H'.Qabs, div_pos hQ H'.do_abs⟩
  exists c • H'
  constructor
  . exact Cycle.possible_smul_nonneg (le_of_lt c.property) hH'
  . calc
      _ = Q / H'.Qabs * H'.Qabs := Cycle.Qabs_smul_pos c.property
      _ = Q := div_mul_cancel _ (ne_of_gt H'.do_abs)
/-- There exists possible `UsualEngineCycle 𝓒_lt_𝓗` that releases a certain heat `Q > 0`. -/
lemma exists_psbl_rel : ∃ H : UsualEngineCycle 𝓒_lt_𝓗, H.possible ∧ H.Qrel = Q := by
  let ⟨H',hH'⟩ := exists_psbl 𝓒_lt_𝓗
  let c : ℝ>0 := ⟨Q / H'.Qrel, div_pos hQ H'.do_rel⟩
  exists c • H'
  constructor
  . exact Cycle.possible_smul_nonneg (le_of_lt c.property) hH'
  . calc
      _ = Q / H'.Qrel * H'.Qrel := Cycle.Qrel_smul_pos c.property
      _ = Q := by field_simp [ne_of_gt H'.do_rel]

end UsualEngineCycle

/-!
### Assumption of the existence of `possible` `UsualPumpCycle`s
-/

namespace UsualPumpCycle

/-- There exists a possible `UsualPumpCycle` between any `𝓒 < 𝓗`. -/
@[reducible] def ExistsPossible :=
  ∀ {𝓒 𝓗}, ∀ 𝓒_lt_𝓗 : 𝓒 < 𝓗, ∃ H : UsualPumpCycle 𝓒_lt_𝓗, H.possible

variable (exists_psbl : ExistsPossible)
variable {𝓒 𝓗 : Reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)
variable {W : ℝ} (hW : 0 < W)
/-- There exists possible `UsualPumpCycle 𝓒_lt_𝓗` that consumes a certain work `W > 0`. -/
lemma exists_psbl_consume : ∃ H : UsualPumpCycle 𝓒_lt_𝓗, H.possible ∧ H.𝓦 = -W := by
  let ⟨H',hH'⟩ := exists_psbl 𝓒_lt_𝓗
  let c : ℝ>0 := ⟨W /(-H'.𝓦), div_pos hW (neg_pos_of_neg H'.consume_work)⟩
  exists c • H'
  constructor
  . exact Cycle.possible_smul_nonneg (le_of_lt c.property) hH'
  . calc
      _ = W /(-H'.𝓦) * H'.𝓦 := Cycle.𝓦_smul
      _ = -W := by field_simp [ne_of_lt H'.consume_work]

end UsualPumpCycle

/-!
### Kelvin statements, Clausius statements and their equivalence
-/

namespace SecondLawStmt

/-- Kelvin-Plank statement : `OneRsvCycle` cannot do work. -/
@[reducible] def KelvinStmt :=
  ∀ {𝓣}, ∀ H : OneRsvCycle 𝓣, 0 < H.𝓦 → ¬H.possible
/-- Clausius statement : Heat cannot be fully transfered from colder rsv `𝓒` to hotter rsv `𝓗`. -/
@[reducible] def ClausiusStmt :=
  ∀ {𝓒 𝓗}, 𝓒 < 𝓗 → ∀ H : AbsRelCycle 𝓒 𝓗, H.Qabs = H.Qrel → ¬H.possible

theorem kelvin_implies_clausius (exists_psbl_engine : UsualEngineCycle.ExistsPossible) :
  KelvinStmt → ClausiusStmt := by
  unfold KelvinStmt ClausiusStmt; contrapose!
  intro ⟨𝓒,𝓗,𝓒_lt_𝓗,C,hC_Q,hC_psbl⟩
  refine ⟨𝓒,?_⟩
  let ⟨E,hE_psbl,hE_Q⟩ := UsualEngineCycle.exists_psbl_abs exists_psbl_engine 𝓒_lt_𝓗 C.do_rel
  let K : OneRsvCycle 𝓒 := {
    C.toCycle + E.toCycle with
    one_rsv := by
      show (C.𝓠 + E.𝓠).support = {𝓒}
      apply Finsupp.support_add_exact
      . simp
        calc C.𝓠 𝓒 + E.𝓠 𝓒
          _ = C.Qabs - E.Qrel := by simp [C.Qabs_one_rsv, E.Qrel_one_rsv]
          _ = E.Qabs - E.Qrel := by simp [hC_Q, hE_Q]
          _ = E.𝓦 := by rw [E.𝓦_from_Qabs_Qrel]
          _ ≠ 0 := ne_of_gt E.do_work
      . rw [C.two_rsv.1, E.two_rsv.1]
        simp [ne_of_gt 𝓒_lt_𝓗]
        calc C.𝓠 𝓗 + E.𝓠 𝓗
          _ = -C.Qrel + E.Qabs := by simp [C.Qrel_one_rsv, E.Qabs_one_rsv]
          _ = 0 := by simp [hE_Q]
  }
  refine ⟨K,?_⟩
  constructor
  . calc K.𝓦
      _ = C.𝓦            + E.𝓦 := by simp
      _ = C.Qabs - C.Qrel + E.𝓦 := by rw [C.𝓦_from_Qabs_Qrel]
      _ =                   E.𝓦 := by simp [hC_Q]
      _ > 0 := E.do_work
  . exact Cycle.possible_add hC_psbl hE_psbl
-- #print axioms kelvin_implies_clausius
/-[Thermodynamics.EquilSystem,
   Thermodynamics.mutualEquil,
   Thermodynamics.mutualEquil.iseqv,
   propext,
   Thermodynamics.Reservoir.linearOrder,
   Quot.sound,
   Classical.choice,
   Thermodynamics.Cycle.possible,
   Thermodynamics.Cycle.possible_smul_nonneg,
   Thermodynamics.Cycle.possible_add]-/

theorem clausius_implies_kelvin (exists_psbl_pump : UsualPumpCycle.ExistsPossible) :
  ClausiusStmt → KelvinStmt := by
  unfold ClausiusStmt KelvinStmt; contrapose!
  intro ⟨𝓣,K,hK_W,hK_psbl⟩
  have : (∃ 𝓒, 𝓒 < 𝓣) ∨ (∃ 𝓗, 𝓣 < 𝓗) := by
    by_cases hgtwater : ⟦waterTriplePoint⟧ ≤ 𝓣
    . exact Or.inl ⟨⟦CO2TriplePoint⟧, lt_of_lt_of_le triple_point_CO2_lt_water hgtwater⟩
    . exact Or.inr ⟨⟦waterTriplePoint⟧, lt_of_not_ge hgtwater⟩
  cases' this with h𝓒 h𝓗
  . let ⟨𝓒,𝓒_lt_𝓣⟩ := h𝓒; refine ⟨𝓒,𝓣,𝓒_lt_𝓣,?_⟩
    let ⟨P,hP_psbl,hP_W⟩ := UsualPumpCycle.exists_psbl_consume exists_psbl_pump 𝓒_lt_𝓣 hK_W
    let C' := K.toCycle + P.toCycle
    have K_no_𝓒 : K.𝓠 𝓒 = 0 := by
      have : 𝓒 ∉ K.𝓠.support := by simp [K.one_rsv, ne_of_lt 𝓒_lt_𝓣]
      exact (Finsupp.not_mem_support_iff).mp this
    have C'_do_abs_𝓒 : _ := calc C'.𝓠 𝓒
      _ = K.𝓠 𝓒 + P.𝓠 𝓒 := rfl
      _ = P.Qabs := by simp [K_no_𝓒, P.Qabs_one_rsv]
      _ > 0 := by simp [P.do_abs]
    have C'_do_rel_𝓣 : _ := calc C'.𝓠 𝓣
      _ = K.𝓠 𝓣 + P.𝓠 𝓣 := rfl
      _ = -P.𝓦 - P.Qrel := by simp [K.𝓦_conv_one_rsv, hP_W, P.Qrel_one_rsv]
      _ = -P.Qabs := by simp [P.𝓦_from_Qabs_Qrel]
      _ < 0 := by simp [P.do_abs]
    let C : AbsRelCycle 𝓒 𝓣 := {
      C' with
      two_rsv := by
        constructor
        . show (K.𝓠 + P.𝓠).support = {𝓒, 𝓣}
          apply Finsupp.support_add_exact
          . simp
            constructor
            . exact ne_of_gt C'_do_abs_𝓒
            . exact ne_of_lt C'_do_rel_𝓣
          . simp [K.one_rsv, P.two_rsv.1]
        . exact ne_of_lt 𝓒_lt_𝓣
      do_abs_rsv := C'_do_abs_𝓒
      do_rel_rsv := C'_do_rel_𝓣
    }
    refine ⟨C,?_⟩
    constructor
    . suffices C.𝓦 = 0 from by rw [C.𝓦_from_Qabs_Qrel] at this; linarith
      calc
        _ = K.𝓦 + P.𝓦 := by simp
        _ = 0 := by linarith
    . exact Cycle.possible_add hK_psbl hP_psbl
  . let ⟨𝓗,𝓣_lt_𝓗⟩ := h𝓗; refine ⟨𝓣,𝓗,𝓣_lt_𝓗,?_⟩
    let ⟨P,hP_psbl,hP_W⟩ := UsualPumpCycle.exists_psbl_consume exists_psbl_pump 𝓣_lt_𝓗 hK_W
    let C' := K.toCycle + P.toCycle
    have K_no_𝓗 : K.𝓠 𝓗 = 0 := by
      have : 𝓗 ∉ K.𝓠.support := by simp [K.one_rsv, ne_of_gt 𝓣_lt_𝓗]
      exact (Finsupp.not_mem_support_iff).mp this
    have C'_do_abs_𝓣 : _ := calc C'.𝓠 𝓣
      _ = K.𝓠 𝓣 + P.𝓠 𝓣 := rfl
      _ = -P.𝓦 + P.Qabs := by simp [K.𝓦_conv_one_rsv, hP_W, P.Qabs_one_rsv]
      _ = P.Qrel := by simp [P.𝓦_from_Qabs_Qrel]
      _ > 0 := by simp [P.do_rel]
    have C'_do_rel_𝓗 : _ := calc C'.𝓠 𝓗
      _ = K.𝓠 𝓗 + P.𝓠 𝓗 := rfl
      _ = -P.Qrel := by simp [K_no_𝓗, P.Qrel_one_rsv]
      _ < 0 := by simp [P.do_rel]
    let C : AbsRelCycle 𝓣 𝓗 := {
      C' with
      two_rsv := by
        constructor
        . show (K.𝓠 + P.𝓠).support = {𝓣, 𝓗}
          apply Finsupp.support_add_exact
          . simp
            constructor
            . exact ne_of_gt C'_do_abs_𝓣
            . exact ne_of_lt C'_do_rel_𝓗
          . simp [K.one_rsv, P.two_rsv.1]
        . exact ne_of_lt 𝓣_lt_𝓗
      do_abs_rsv := C'_do_abs_𝓣
      do_rel_rsv := C'_do_rel_𝓗
    }
    refine ⟨C,?_⟩
    constructor
    . suffices C.𝓦 = 0 from by rw [C.𝓦_from_Qabs_Qrel] at this; linarith
      calc
        _ = K.𝓦 + P.𝓦 := by simp
        _ = 0 := by linarith
    . exact Cycle.possible_add hK_psbl hP_psbl
-- #print axioms clausius_implies_kelvin
/-[Thermodynamics.EquilSystem,
   Thermodynamics.mutualEquil,
   Thermodynamics.mutualEquil.iseqv,
   propext,
   Thermodynamics.Reservoir.linearOrder,
   Quot.sound,
   Classical.choice,
   Thermodynamics.Cycle.possible,
   Thermodynamics.waterTriplePoint,
   Thermodynamics.CO2TriplePoint,
   Thermodynamics.triple_point_CO2_lt_water,
   Thermodynamics.Cycle.possible_smul_nonneg,
   Thermodynamics.Cycle.possible_add]-/

end SecondLawStmt

/-!
## The SECOND Law
---------------------------------------------------------------------------------------------------/

@[inherit_doc SecondLawStmt.KelvinStmt]
axiom kelvin_stmt   : SecondLawStmt.KelvinStmt
@[inherit_doc SecondLawStmt.ClausiusStmt]
axiom clausius_stmt : SecondLawStmt.ClausiusStmt

/-!
## Carnot theorem
---------------------------------------------------------------------------------------------------/

section CarnotThm
variable {𝓒 𝓗} {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H R : UsualEngineCycle 𝓒_lt_𝓗}

/-- Carnot theorem : reversible `UsualEngineCycle` has the greatest efficiency. -/
theorem carnot_thm : H.possible → R.reversible → H.eff ≤ R.eff := by
  intro hH_psbl ⟨_,hRrev_psbl⟩
  by_contra heff; refine absurd (@kelvin_stmt 𝓒) ?_; simp
  let c : ℝ>0 := {
    val := H.Qabs / R.Qabs,
    property := div_pos H.do_abs R.do_abs
  }
  let K' := H.toCycle + (c • R.rev).toCycle
  have K'_do_work' := calc H.𝓦 - H.Qabs * R.eff
    _ = (H.eff - R.eff) * H.Qabs := by rw [H.𝓦_from_eff_Qabs]; ring
    _ > 0 := by
      have : H.eff - R.eff > 0 := by linarith
      have := H.do_abs
      positivity
  let K : OneRsvCycle 𝓒 := {
    K' with
    one_rsv := by
      show (H.𝓠 + (c • R.rev).𝓠).support = {𝓒}
      apply Finsupp.support_add_exact
      . simp
        calc K'.𝓠 𝓒
          _ =  H.𝓠 𝓒 + H.Qabs / R.Qabs * -R.𝓠 𝓒 := rfl
          _ = -H.Qrel + H.Qabs / R.Qabs * R.Qrel := by simp [H.Qrel_one_rsv, R.Qrel_one_rsv]
          _ = -H.Qrel + H.Qabs - H.Qabs / R.Qabs * R.𝓦 := by
            rw [R.Qrel_from_Qabs_𝓦]; ring_nf
            have := R.do_abs; field_simp
          _ = H.𝓦 - H.Qabs * R.eff := by rw [H.𝓦_from_Qabs_Qrel, Cycle.eff]; ring
          _ ≠ 0 := ne_of_gt K'_do_work'
      . rw [H.two_rsv.1, (c • R.rev).two_rsv.1]
        simp [ne_of_gt 𝓒_lt_𝓗]
        calc K'.𝓠 𝓗
          _ = H.𝓠 𝓗 + H.Qabs / R.Qabs * -R.𝓠 𝓗 := rfl
          _ = H.Qabs + H.Qabs / R.Qabs * -R.Qabs := by simp [H.Qabs_one_rsv, R.Qabs_one_rsv]
          _ = 0 := by have := R.do_abs; field_simp
  }
  refine ⟨K,?_⟩
  constructor
  . calc K'.𝓦
      _ = H.𝓦 + (c     •   R.rev     ).𝓦 := by simp
      _ = H.𝓦 + (c.val • (-R.toCycle)).𝓦 := rfl
      _ = H.𝓦 - H.Qabs / R.Qabs * R.𝓦    := by simp; ring
      _ = H.𝓦 - H.Qabs * R.eff            := by rw [Cycle.eff]; ring
      _ > 0 := K'_do_work'
  . refine Cycle.possible_add hH_psbl ?_
    refine Cycle.possible_smul_nonneg (le_of_lt c.property) ?_
    exact hRrev_psbl
-- #print axioms carnot_thm
/-[Thermodynamics.EquilSystem,
   Thermodynamics.mutualEquil,
   Thermodynamics.mutualEquil.iseqv,
   propext,
   Thermodynamics.Reservoir.linearOrder,
   Quot.sound,
   Classical.choice,
   Thermodynamics.Cycle.possible,
   Thermodynamics.kelvin_stmt,
   Thermodynamics.waterTriplePoint,
   Thermodynamics.Cycle.possible_add,
   Thermodynamics.Cycle.possible_smul_nonneg]-/

theorem UsualEngineCycle.rev_iff_eff (hR_rvsbl : R.reversible) : H.reversible ↔ H.eff = R.eff := by
  constructor
  . intro hH_rvsbl
    have := carnot_thm hH_rvsbl.1 hR_rvsbl
    have := carnot_thm hR_rvsbl.1 hH_rvsbl
    linarith
  . intro hH_eff
    let ⟨c,hc⟩ := UsualEngineCycle.eq_smul_pos_of_eff_eq hH_eff
    rw [hc]; exact Cycle.reversible_smul_nonneg (le_of_lt c.property) hR_rvsbl

end CarnotThm

end Thermodynamics
