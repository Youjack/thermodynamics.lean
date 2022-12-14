/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import second_law

/-!
# Thermodynamic Temperature

This file states
* the axiom that reversible `cycle`s do exists, i.e. `usual_engine_cycle.exists_reversible`
and defines
* thermodynamic temperature of `reservoir`, i.e. `reservoir.temp`
-/

noncomputable theory

namespace thermodynamics

/-!
## Existence of reversible `usual_engine_cycle`
---------------------------------------------------------------------------------------------------/

namespace usual_engine_cycle
variables {ð ð : reservoir} (ð_lt_ð : ð < ð)

axiom exists_reversible : â H : usual_engine_cycle ð_lt_ð, H.reversible
copy_doc_string exists_reversible' â exists_reversible

variables {Q : â} (hQ : 0 < Q)
/-- There exists reversible `usual_engine_cycle ð_lt_ð` that absorbs a certain heat `Q > 0`. -/
lemma exists_rev_abs : â H : usual_engine_cycle ð_lt_ð, H.reversible â§ âH.Qabs = Q :=
  let â¨H', hH'â© := exists_reversible ð_lt_ð in
  let c : ââ := â¨Q / H'.Qabs, div_pos hQ H'.do_absâ© in
  let H := c â¢ H' in
  â¨ H, 
    cycle.reversible_smul_nonneg (le_of_lt c.property) hH',
    calc âH.Qabs
         = Q / H'.Qabs * H'.Qabs : cycle.Qabs_smul_pos c.property
      ...= Q                     : div_mul_cancel _ (ne_of_gt H'.do_abs), â©
--

def rev_eff := (classical.some (exists_reversible ð_lt_ð)).eff
lemma rev_eff_universal {H : usual_engine_cycle ð_lt_ð} (h : H.reversible) :
  H.eff = rev_eff ð_lt_ð := by {
  apply (usual_engine_cycle.rev_iff_eff _).elim_left h,
  exact classical.some_spec (exists_reversible ð_lt_ð), }
--

end usual_engine_cycle

-- lemma usual_pump_cycle.exists_reversible

/-!
## Thermodynamic temperature
---------------------------------------------------------------------------------------------------/

/-!
### Construction of thermodynamic temperature
-/

namespace reservoir

section
variables {ð ð : reservoir} (ð_lt_ð : ð < ð)
/-- `temp`erature `corr`elation function -/
@[reducible] def temp_corr := 1 - usual_engine_cycle.rev_eff ð_lt_ð
lemma temp_corr_pos    : 0 < temp_corr ð_lt_ð :=
  sub_pos.elim_right (usual_engine_cycle.eff_lt_one _)
lemma temp_corr_lt_one : temp_corr ð_lt_ð < 1 :=
  sub_lt_self _ (cycle.eff_pos _)
lemma temp_corr_eq_Qratio {H : usual_engine_cycle ð_lt_ð} (hH : H.reversible) :
  temp_corr ð_lt_ð = H.Qrel / H.Qabs :=
  calc temp_corr ð_lt_ð
       = 1 - H.eff : by rw [usual_engine_cycle.rev_eff_universal _ hH]
    ...= H.Qrel / H.Qabs : by { rw H.eff_from_Qabs_Qrel, ring }
end

section
variables {ð ð ð : reservoir} (ð_lt_ð : ð < ð) (ð_lt_ð : ð < ð)
theorem temp_corr_trans :
  temp_corr (ð_lt_ð.trans ð_lt_ð) = (temp_corr ð_lt_ð) * (temp_corr ð_lt_ð) :=
  let ð_lt_ð := ð_lt_ð.trans ð_lt_ð in
  let â¨Hðð, hHððâ© := usual_engine_cycle.exists_reversible ð_lt_ð in
  let â¨Hðð, hHðð, hQâ© := usual_engine_cycle.exists_rev_abs ð_lt_ð Hðð.do_rel in by {
  let Hðð' := Hðð.to_cycle + Hðð.to_cycle,
  have Hðð_noð : ð â Hðð.ð .support, {
    rw Hðð.two_rsv.elim_left,
    simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
    exact â¨ne_of_gt ð_lt_ð, ne_of_gt ð_lt_ðâ©, },
  have Hðð_noð : ð â Hðð.ð .support, {
    rw Hðð.two_rsv.elim_left,
    simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
    exact â¨ne_of_lt ð_lt_ð, ne_of_lt ð_lt_ðâ©, },
  have Hðð'Qabs :=
    calc Hðð'.ð  ð
         = Hðð.ð  ð + Hðð.ð  ð : rfl
      ...= Hðð.ð  ð            : by rw [finsupp.not_mem_support_iff.elim_left Hðð_noð, add_zero]
      ...= Hðð.Qabs            : Hðð.Qabs_one_rsv.symm,
  have Hðð'Qrel :=
    calc Hðð'.ð  ð
         = Hðð.ð  ð + Hðð.ð  ð : rfl
      ...=            Hðð.ð  ð : by rw [finsupp.not_mem_support_iff.elim_left Hðð_noð, zero_add]
      ...=           -Hðð.Qrel : by rw [âneg_neg (Hðð.ð  ð), âHðð.Qrel_one_rsv],
  have do_abs_rsv : Hðð'.ð  ð > 0, from Hðð'Qabs.symm â¸ Hðð.do_abs,
  have do_rel_rsv : Hðð'.ð  ð < 0, {
    rw Hðð'Qrel,
    exact neg_lt_zero.elim_right Hðð.do_rel, },
  let Hðð : usual_engine_cycle ð_lt_ð :=
    { two_rsv := by {
        refine â¨_, ne_of_gt ð_lt_ðâ©,
        have : Hðð'.ð  = Hðð.ð  + Hðð.ð , from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
          split,
            exact ne_of_gt do_abs_rsv,
            exact ne_of_lt do_rel_rsv, },
        { have : (Hðð.ð .support âª Hðð.ð .support) \ {ð, ð} = {ð}, {
            rw [Hðð.two_rsv.elim_left, Hðð.two_rsv.elim_left],
            ext, simp, split,
            { tauto, },
            { assume hð,
              split,
              { exact or.inl hð, },
              { rw [not_or_distrib, hð],
                exact â¨ne_of_lt ð_lt_ð, ne_of_gt ð_lt_ðâ©, } } },
          simp only [this, finset.mem_singleton, forall_eq],
          calc Hðð.ð  ð + Hðð.ð  ð
               = -Hðð.Qrel + Hðð.Qabs : by rw [Hðð.Qrel_one_rsv, neg_neg, Hðð.Qabs_one_rsv]
            ...= 0                     : by { rw hQ, ring }, } },
      do_abs_rsv := do_abs_rsv,
      do_rel_rsv := do_rel_rsv,
      do_work :=
        calc Hðð'.ð¦
             = Hðð.ð¦ + Hðð.ð¦ : cycle.ð¦_add
          ...> 0                : add_pos Hðð.do_work Hðð.do_work,
      ..Hðð' },
  have := temp_corr_eq_Qratio ð_lt_ð hHðð, rw this,
  have := temp_corr_eq_Qratio ð_lt_ð hHðð, rw this,
  rw [hQ, div_mul_div_cancel _ (ne_of_gt Hðð.do_rel)],
  have : Hðð.reversible, from cycle.reversible_add hHðð hHðð,
  have := temp_corr_eq_Qratio ð_lt_ð this, rw this,
  rw [Hðð.Qabs_one_rsv, Hðð'Qabs],
  rw [Hðð.Qrel_one_rsv, Hðð'Qrel, neg_neg], }
/-- `temp_corr ð_lt_ð` is `strict_mono` as a function of `ð` -/
lemma temp_corr_strict_mono : temp_corr (ð_lt_ð.trans ð_lt_ð) < temp_corr ð_lt_ð := by {
  rw temp_corr_trans ð_lt_ð ð_lt_ð,
  exact (mul_lt_iff_lt_one_left (temp_corr_pos _)).elim_right (temp_corr_lt_one _), }
end

/-- `ref`erence `sys`tem -/
@[reducible] def ref_sys : equil_system := water_triple_point
/-- reference temperature of `ref_sys` -/
@[reducible] def ref_temp : ââ := â¨273.16, by cancel_denomsâ©
/-- thermodynamic `temp`erature of `reservoir`s -/
def temp : reservoir âªo ââ := order_embedding.of_strict_mono
  ( Î» ð£,
    if        heq : ð£ = â¦ref_sysâ§ then
      ref_temp
    else if   hlt : ð£ < â¦ref_sysâ§ then
      â¨(temp_corr hlt) * ref_temp, mul_pos (temp_corr_pos _) ref_temp.propertyâ©
    else have hgt : ð£ > â¦ref_sysâ§, from ne.lt_of_le' heq (le_of_not_gt hlt),
      â¨ref_temp / (temp_corr hgt), div_pos ref_temp.property (temp_corr_pos _)â© )
  ( assume ð ð ð_lt_ð,
    if        hðlt : ð < â¦ref_sysâ§ then by {
      have hðlt := ð_lt_ð.trans hðlt,
      simp only [ne_of_lt hðlt, hðlt, ne_of_lt hðlt, hðlt,
        dif_pos, dite_eq_ite, if_false],
      refine mul_lt_mul _ (le_rfl) (ref_temp.property) (le_of_lt (temp_corr_pos _)),
      exact temp_corr_strict_mono ð_lt_ð hðlt, }
    else if   hðeq : ð = â¦ref_sysâ§ then by {
      have hðlt : ð < â¦ref_sysâ§, from hðeq â¸ ð_lt_ð,
      simp only [ne_of_lt hðlt, hðlt, hðeq,
        dif_pos, not_false_iff, dif_neg],
      exact (mul_lt_iff_lt_one_left ref_temp.property).elim_right (temp_corr_lt_one _), }
    else have hðgt : ð > â¦ref_sysâ§, from
        ne.lt_of_le (ne.symm hðeq) (le_of_not_gt hðlt), by {
      simp only [ne_of_gt hðgt, not_lt_of_gt hðgt,
        not_false_iff, dif_neg],
      apply subtype.coe_lt_coe.elim_left,
      rw [subtype.coe_mk (âref_temp / temp_corr hðgt) _, div_eq_mul_one_div],
      exact if  hðlt : ð < â¦ref_sysâ§ then by {
        simp only [ne_of_lt hðlt, hðlt,
          dif_pos, dite_eq_ite, if_false],
        rw [subtype.coe_mk, mul_comm (temp_corr hðlt) _],
        refine mul_lt_mul' (le_rfl) _ (le_of_lt (temp_corr_pos _)) (ref_temp.property),
          apply (lt_div_iff (temp_corr_pos _)).elim_right,
          rw âtemp_corr_trans,
          exact temp_corr_lt_one _, }
      else if   hðeq : ð = â¦ref_sysâ§ then by {
        simp only [hðeq, dif_pos],
        apply lt_mul_right ref_temp.property,
          apply (lt_div_iff (temp_corr_pos _)).elim_right,
          rw one_mul,
          exact temp_corr_lt_one _, }
      else have hðgt : ð > â¦ref_sysâ§, from
          ne.lt_of_le (ne.symm hðeq) (le_of_not_gt hðlt), by {
        simp only [ne_of_gt hðgt, not_lt_of_gt hðgt,
          not_false_iff, dif_neg],
        rw [subtype.coe_mk, div_eq_mul_one_div _ (temp_corr hðgt)],
        refine mul_lt_mul' (le_rfl) _ _ (ref_temp.property),
        { apply (one_div_lt_one_div (temp_corr_pos _) (temp_corr_pos _)).elim_right,
          rw temp_corr_trans hðgt ð_lt_ð,
          exact (mul_lt_iff_lt_one_right (temp_corr_pos _)).elim_right (temp_corr_lt_one _), },
        { exact div_nonneg zero_le_one (le_of_lt (temp_corr_pos _)), } } } )
--

end reservoir

/-!
### Applications of thermodynamic temperature
-/

/- namespace usual_engine_cycle
variables {ð ð : reservoir} (ð_lt_ð : ð < ð)

lemma rev_eff_from_temp : rev_eff ð_lt_ð = 1 - ð.temp / ð.temp := sorry

end usual_engine_cycle -/

/-!
## The absolute zero

TODO
* existence of the absolute zero as a limit ?
* require `rsv_no_min` ?
* behavior of `usual_engine_cycle` when ð.temp -> 0
---------------------------------------------------------------------------------------------------/

end thermodynamics
