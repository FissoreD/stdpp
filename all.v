From stdpp Require Import base binders boolset coGset coPset countable decidable finite fin_map_dom fin_maps fin_sets fin functions gmap gmultiset hashset hlist infinite lexico list_basics list_misc list_monad list_numbers list_relations listset_nodup listset list_tactics list mapset namespaces nat_cancel natmap nmap numbers options option orders pmap prelude pretty proof_irrel propset relations sets sorting ssreflect streams stringmap strings tactics telescopes topGset vector well_founded zmap.

Set Printing All.
Print HintDb typeclass_instances.

(* 
Discriminated database
Unfoldable variable definitions: all
Unfoldable constant definitions: all except: Alter AntiSymm
  CRelationClasses.Antisymmetric Antisymmetric Assoc
  CRelationClasses.Asymmetric Asymmetric Bottom CProd Cancel Comm Decision
  Delete Difference DifferenceWith DisjUnion Disjoint Dom ElemOf Elements
  Empty Equiv FMap Filter Fresh Half IdemP Inj Inj2 Insert Intersection
  IntersectionWith CRelationClasses.Irreflexive Irreflexive Join LeftAbsorb
  LeftId LeibnizEquiv Lexico Lookup LookupTotal MBind MJoin MRet MThrow
  nat_cancel.MakeNatAdd nat_cancel.MakeNatS MapFold Maybe Maybe2 Maybe3
  Maybe4 Meet Merge N_lexico NatCancel nat_cancel.NatCancelL
  nat_cancel.NatCancelR CMorphisms.Normalizes Normalizes OMap PartialAlter
  CRelationClasses.PartialOrder RelationClasses.PartialOrder Pretty
  ProofIrrel CMorphisms.Proper Proper CMorphisms.ProperProxy ProperProxy
  Qcanon.Qcle Qcanon.Qclt CRelationClasses.Reflexive Reflexive
  ssrclasses.Reflexive ReflexiveProxy RelDecision RightAbsorb RightId
  ScalarMul Singleton SingletonM SingletonMS Size SolveProperSubrelation
  SqSubsetEq SubsetEq Surj CRelationClasses.Symmetric Symmetric TCFastDone
  TCSimpl Top Total CRelationClasses.Transitive Transitive Trichotomy
  TrichotomyT Unconvertible Union UnionWith UpClose Z_lexico all arrow
  CRelationClasses.arrow arrows bool_lexico boolset_elem_of coGset_difference
  coGset_elem_of coGset_empty coGset_intersection coGset_singleton coGset_top
  coGset_union coPset disj_union_list Qp.div CRelationClasses.flip
  CMorphisms.forall_relation forall_relation gmultiset_difference
  gmultiset_dom gmultiset_elem_of gmultiset_elements gmultiset_empty
  gmultiset_map gmultiset_scalar_mul gmultiset_singleton gmultiset_size
  gmultiset_subseteq gmultiset_union gset hashset_elem_of iff
  CRelationClasses.iffT impl N.le Pos.le Z.le lt N.lt Pos.lt Z.lt map_img
  map_lookup_total map_preimg max_list_with minimal nat_lexico not
  option_equiv pointwise_lifting CMorphisms.pointwise_relation
  pointwise_relation predicate_equivalence predicate_implication prod_equiv
  CRelationClasses.relation_equivalence relation_equivalence
  CMorphisms.respectful respectful set_bind set_disjoint_instance
  set_equiv_instance set_filter set_fold set_fresh set_map set_mfail set_omap
  set_size set_subseteq_instance CRelationClasses.subrelation subrelation
  sum_equiv sum_list_with tc_opaque texist tforall topGset_elem_of
  topGset_empty topGset_singleton topGset_top topGset_union union_list
  vm_compute_eq
Unfoldable projection definitions: all
Cut: emp
For any goal ->   
For Alter (modes - -
!) ->   simple apply @list_alter (cost 0, pattern 
	    Alter nat ?M2105 (list ?M2105), id 0)
        simple apply @fn_alter (cost 1, pattern Alter 
                                                 ?M5297 
                                                 ?M5298
                                                 (forall _ : ?M5297, ?M5298), id 0)
        simple apply @map_alter (cost 1, pattern Alter ?M3700 ?M3701 ?M3702, id 0)
For AntiSymm ->   simple apply @AntiSymm_instance_0 (cost 0, pattern 
                  @AntiSymm (list ?M2156) (@Permutation ?M2156)
                    (@submseteq ?M2156), id 0)
                  simple apply @partial_order_anti_symm (cost 1, pattern 
                  @AntiSymm ?M5957 (@eq ?M5957) ?M5958, id 0)
                  simple apply @AntiSymm_instance_1 (cost 1, pattern 
                  @AntiSymm (list ?M2192) (@eq (list ?M2192))
                    (@Forall2 ?M2192 ?M2192 ?M2193), id 0)
                  simple eapply @set_subseteq_antisymm (cost 4, pattern 
                  @AntiSymm ?M2978
                    (@equiv ?M2978 (@set_equiv_instance ?M2977 ?M2978 ?M2979))
                    (@subseteq ?M2978
                       (@set_subseteq_instance ?M2977 ?M2978 ?M2979)), id 0)
For Antisymmetric ->   simple eapply @partial_order_antisym (cost 2, pattern 
                       @Antisymmetric ?M267 ?M268 
                         ?M269 ?M270, id 0)
                       (*external*) (class_apply @flip_Antisymmetric) (cost 3, pattern 
                       @Antisymmetric _ (@flip _ _ _ _) _, id 0)
For CRelationClasses.Antisymmetric ->   simple eapply @CRelationClasses.partial_order_antisym (cost 2, pattern 
                                        @CRelationClasses.Antisymmetric 
                                          ?M428 ?M429 
                                          ?M430 ?M431, id 0)
                                        (*external*) (
                                        class_apply
                                         @CRelationClasses.flip_Antisymmetric) (cost 3, pattern 
                                        @CRelationClasses.Antisymmetric _
                                          (@CRelationClasses.flip _ _ _ _) _, id 0)
For Assoc ->   simple apply @gmultiset_disj_union_assoc (cost 0, pattern 
               @Assoc (@gmultiset ?M5568 ?M5569 ?M5570)
                 (@eq (@gmultiset ?M5568 ?M5569 ?M5570))
                 (@disj_union (@gmultiset ?M5568 ?M5569 ?M5570)
                    (@gmultiset_disj_union ?M5568 ?M5569 ?M5570)), id 0)
               simple apply @gmultiset_intersection_assoc (cost 0, pattern 
               @Assoc (@gmultiset ?M5553 ?M5554 ?M5555)
                 (@eq (@gmultiset ?M5553 ?M5554 ?M5555))
                 (@intersection (@gmultiset ?M5553 ?M5554 ?M5555)
                    (@gmultiset_intersection ?M5553 ?M5554 ?M5555)), id 0)
               simple apply @gmultiset_union_assoc (cost 0, pattern 
               @Assoc (@gmultiset ?M5538 ?M5539 ?M5540)
                 (@eq (@gmultiset ?M5538 ?M5539 ?M5540))
                 (@union (@gmultiset ?M5538 ?M5539 ?M5540)
                    (@gmultiset_union ?M5538 ?M5539 ?M5540)), id 0)
               simple apply @Assoc_instance_0 (cost 0, pattern 
               @Assoc (list ?M2117) (@eq (list ?M2117)) 
                 (@app ?M2117), id 0)
               exact Qp.min_assoc (cost 0, pattern 
               @Assoc Qp (@eq Qp) Qp.min, id 0)
               exact Qp.max_assoc (cost 0, pattern 
               @Assoc Qp (@eq Qp) Qp.max, id 0)
               exact Qp.mul_assoc (cost 0, pattern 
               @Assoc Qp (@eq Qp) Qp.mul, id 0)
               exact Qp.add_assoc (cost 0, pattern 
               @Assoc Qp (@eq Qp) Qp.add, id 0)
               exact Qcmult_assoc' (cost 0, pattern 
               @Assoc Qcanon.Qc (@eq Qcanon.Qc) Qcanon.Qcmult, id 0)
               exact Qcplus_assoc' (cost 0, pattern 
               @Assoc Qcanon.Qc (@eq Qcanon.Qc) Qcanon.Qcplus, id 0)
               exact Z.mul_assoc' (cost 0, pattern 
               @Assoc Z (@eq Z) Z.mul, id 0)
               exact Z.add_assoc' (cost 0, pattern 
               @Assoc Z (@eq Z) Z.add, id 0)
               exact N.mul_assoc' (cost 0, pattern 
               @Assoc N (@eq N) N.mul, id 0)
               exact N.add_assoc' (cost 0, pattern 
               @Assoc N (@eq N) N.add, id 0)
               exact Pos.app_assoc (cost 0, pattern 
               @Assoc positive (@eq positive) Pos.app, id 0)
               exact Pos.mul_assoc' (cost 0, pattern 
               @Assoc positive (@eq positive) Pos.mul, id 0)
               exact Pos.add_assoc' (cost 0, pattern 
               @Assoc positive (@eq positive) Pos.add, id 0)
               exact Nat.mul_assoc' (cost 0, pattern 
               @Assoc nat (@eq nat) Nat.mul, id 0)
               exact Nat.add_assoc' (cost 0, pattern 
               @Assoc nat (@eq nat) Nat.add, id 0)
               simple apply @id2_assoc (cost 0, pattern 
               @Assoc ?M1205 (@eq ?M1205) (fun _ x : ?M1205 => x), id 0)
               simple apply @id1_assoc (cost 0, pattern 
               @Assoc ?M1204 (@eq ?M1204) (fun x _ : ?M1204 => x), id 0)
               simple apply @const2_assoc (cost 0, pattern 
               @Assoc ?M1202 (@eq ?M1202) (fun _ _ : ?M1202 => ?M1203), id 0)
               exact or_assoc (cost 0, pattern @Assoc Prop iff or, id 0)
               exact and_assoc (cost 0, pattern @Assoc Prop iff and, id 0)
               simple eapply @union_assoc (cost 3, pattern 
               @Assoc ?M3020
                 (@equiv ?M3020 (@set_equiv_instance ?M3019 ?M3020 ?M3021))
                 (@union ?M3020 ?M3024), id 0)
               simple eapply @intersection_assoc (cost 5, pattern 
               @Assoc ?M3116
                 (@equiv ?M3116 (@set_equiv_instance ?M3115 ?M3116 ?M3117))
                 (@intersection ?M3116 ?M3121), id 0)
               simple eapply @union_assoc_L (cost 6, pattern 
               @Assoc ?M3081 (@eq ?M3081) (@union ?M3081 ?M3085), id 0)
               simple eapply @intersection_assoc_L (cost 8, pattern 
               @Assoc ?M3163 (@eq ?M3163) (@intersection ?M3163 ?M3168), id 0)
               simple eapply @map_intersection_assoc (cost 9, pattern 
               @Assoc (?M4115 ?M4125) (@eq (?M4115 ?M4125))
                 (@intersection (?M4115 ?M4125)
                    (@map_intersection ?M4115 ?M4121 ?M4125)), id 0)
               simple eapply @map_union_assoc (cost 9, pattern 
               @Assoc (?M4023 ?M4033) (@eq (?M4023 ?M4033))
                 (@union (?M4023 ?M4033) (@map_union ?M4023 ?M4029 ?M4033)), id 0)
For Asymmetric ->   simple apply @StrictOrder_Asymmetric (cost 1, pattern 
                    @Asymmetric ?M230 ?M231, id 0)
                    (*external*) (class_apply @flip_Asymmetric) (cost 3, pattern 
                    @Asymmetric _ (@flip _ _ _ _), id 0)
For CRelationClasses.Asymmetric ->   simple apply @CRelationClasses.StrictOrder_Asymmetric (cost 1, pattern 
                                     @CRelationClasses.Asymmetric 
                                       ?M394 ?M395, id 0)
                                     (*external*) (
                                     class_apply
                                      @CRelationClasses.flip_Asymmetric) (cost 3, pattern 
                                     @CRelationClasses.Asymmetric _
                                       (@CRelationClasses.flip _ _ _ _), id 0)
For ZifyClasses.BinOp ->   exact ZifyInst.Op_Z_pow_pos (cost 0, pattern 
                           @ZifyClasses.BinOp Z positive Z Z Z Z Z.pow_pos
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_pow (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.pow
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_quot (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.quot
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_rem (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.rem
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_mod (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.modulo
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_div (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.div
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_sub (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.sub
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_mul (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.mul
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_max (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.max
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_min (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.min
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_Z_add (cost 0, pattern 
                           @ZifyClasses.BinOp Z Z Z Z Z Z Z.add
                             ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z
                             ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_N_pow (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.pow
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_mod (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.modulo
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_div (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.div
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_sub (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.sub
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_mul (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.mul
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_max (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.max
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_min (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.min
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_N_add (cost 0, pattern 
                           @ZifyClasses.BinOp N N N Z Z Z N.add
                             ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z
                             ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_pos_pow (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.pow ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_max (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.max ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_min (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.min ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_mul (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.mul ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_sub (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.sub ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_add_carry (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.add_carry ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_pos_add (cost 0, pattern 
                           @ZifyClasses.BinOp positive positive positive Z Z
                             Z Pos.add ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_max (cost 0, pattern 
                           @ZifyClasses.BinOp nat nat nat Z Z Z Nat.max
                             ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z
                             ZifyInst.Inj_nat_Z, id 0)
                           exact ZifyInst.Op_min (cost 0, pattern 
                           @ZifyClasses.BinOp nat nat nat Z Z Z Nat.min
                             ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z
                             ZifyInst.Inj_nat_Z, id 0)
                           exact ZifyInst.Op_mul (cost 0, pattern 
                           @ZifyClasses.BinOp nat nat nat Z Z Z Nat.mul
                             ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z
                             ZifyInst.Inj_nat_Z, id 0)
                           exact ZifyInst.Op_sub (cost 0, pattern 
                           @ZifyClasses.BinOp nat nat nat Z Z Z Nat.sub
                             ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z
                             ZifyInst.Inj_nat_Z, id 0)
                           exact ZifyInst.Op_plus (cost 0, pattern 
                           @ZifyClasses.BinOp nat nat nat Z Z Z Nat.add
                             ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z
                             ZifyInst.Inj_nat_Z, id 0)
For ZifyClasses.BinOpSpec ->   exact ZifyInst.ZminSpec (cost 0, pattern 
                               @ZifyClasses.BinOpSpec Z Z Z Z.min, id 0)
                               exact ZifyInst.ZmaxSpec (cost 0, pattern 
                               @ZifyClasses.BinOpSpec Z Z Z Z.max, id 0)
For ZifyClasses.BinRel ->   exact ZifyInst.Op_eqZ (cost 0, pattern 
                            @ZifyClasses.BinRel Z Z 
                              (@eq Z) ZifyInst.Inj_Z_Z, id 0)
                            exact ZifyInst.Op_Z_le (cost 0, pattern 
                            @ZifyClasses.BinRel Z Z Z.le ZifyInst.Inj_Z_Z, id 0)
                            exact ZifyInst.Op_Z_gt (cost 0, pattern 
                            @ZifyClasses.BinRel Z Z Z.gt ZifyInst.Inj_Z_Z, id 0)
                            exact ZifyInst.Op_Z_lt (cost 0, pattern 
                            @ZifyClasses.BinRel Z Z Z.lt ZifyInst.Inj_Z_Z, id 0)
                            exact ZifyInst.Op_Z_ge (cost 0, pattern 
                            @ZifyClasses.BinRel Z Z Z.ge ZifyInst.Inj_Z_Z, id 0)
                            exact ZifyInst.Op_eq_N (cost 0, pattern 
                            @ZifyClasses.BinRel N Z 
                              (@eq N) ZifyInst.Inj_N_Z, id 0)
                            exact ZifyInst.Op_N_le (cost 0, pattern 
                            @ZifyClasses.BinRel N Z N.le ZifyInst.Inj_N_Z, id 0)
                            exact ZifyInst.Op_N_gt (cost 0, pattern 
                            @ZifyClasses.BinRel N Z N.gt ZifyInst.Inj_N_Z, id 0)
                            exact ZifyInst.Op_N_lt (cost 0, pattern 
                            @ZifyClasses.BinRel N Z N.lt ZifyInst.Inj_N_Z, id 0)
                            exact ZifyInst.Op_N_ge (cost 0, pattern 
                            @ZifyClasses.BinRel N Z N.ge ZifyInst.Inj_N_Z, id 0)
                            exact ZifyInst.Op_eq_pos (cost 0, pattern 
                            @ZifyClasses.BinRel positive Z 
                              (@eq positive) ZifyInst.Inj_pos_Z, id 0)
                            exact ZifyInst.Op_pos_le (cost 0, pattern 
                            @ZifyClasses.BinRel positive Z Pos.le
                              ZifyInst.Inj_pos_Z, id 0)
                            exact ZifyInst.Op_pos_gt (cost 0, pattern 
                            @ZifyClasses.BinRel positive Z Pos.gt
                              ZifyInst.Inj_pos_Z, id 0)
                            exact ZifyInst.Op_pos_lt (cost 0, pattern 
                            @ZifyClasses.BinRel positive Z Pos.lt
                              ZifyInst.Inj_pos_Z, id 0)
                            exact ZifyInst.Op_pos_ge (cost 0, pattern 
                            @ZifyClasses.BinRel positive Z Pos.ge
                              ZifyInst.Inj_pos_Z, id 0)
                            exact ZifyInst.Op_Nat_eq (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z Nat.eq
                              ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_eq_nat (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z 
                              (@eq nat) ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_Nat_le (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z Nat.le
                              ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_le (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z le ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_gt (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z gt ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_Nat_lt (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z Nat.lt
                              ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_lt (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z lt ZifyInst.Inj_nat_Z, id 0)
                            exact ZifyInst.Op_ge (cost 0, pattern 
                            @ZifyClasses.BinRel nat Z ge ZifyInst.Inj_nat_Z, id 0)
For Bottom (modes !) ->   
For CProd (modes ! !
-) ->   simple apply @gset_cprod (cost 0, pattern 
        CProd (@gset ?M5207 ?M5208 ?M5209) (@gset ?M5210 ?M5211 ?M5212)
          (@gset (prod ?M5207 ?M5210)
             (@prod_eq_dec ?M5207 ?M5208 ?M5210 ?M5211)
             (@prod_countable ?M5207 ?M5208 ?M5209 ?M5210 ?M5211 ?M5212)), id 0)
        simple apply @boolset_cprod (cost 0, pattern 
        CProd (boolset ?M4649) (boolset ?M4650)
          (boolset (prod ?M4649 ?M4650)), id 0)
        simple apply @list_cprod (cost 0, pattern 
        CProd (list ?M2302) (list ?M2303) (list (prod ?M2302 ?M2303)), id 0)
        simple apply @monadset_cprod (cost 2, pattern 
        CProd (?M3329 ?M3332) (?M3329 ?M3333) (?M3329 (prod ?M3332 ?M3333)), id 0)
For Cancel (modes + + - - !, + + - ! -) ->   simple apply @prod_swap_cancel (cost 0, pattern 
        @Cancel (prod ?M1231 ?M1232) (prod ?M1232 ?M1231)
          (@eq (prod ?M1232 ?M1231)) (@prod_swap ?M1231 ?M1232)
          (@prod_swap ?M1232 ?M1231), id 0)
For Comm ->   simple apply @gmultiset_disj_union_comm (cost 0, pattern 
              @Comm (@gmultiset ?M5565 ?M5566 ?M5567)
                (@gmultiset ?M5565 ?M5566 ?M5567)
                (@eq (@gmultiset ?M5565 ?M5566 ?M5567))
                (@disj_union (@gmultiset ?M5565 ?M5566 ?M5567)
                   (@gmultiset_disj_union ?M5565 ?M5566 ?M5567)), id 0)
              simple apply @gmultiset_intersection_comm (cost 0, pattern 
              @Comm (@gmultiset ?M5550 ?M5551 ?M5552)
                (@gmultiset ?M5550 ?M5551 ?M5552)
                (@eq (@gmultiset ?M5550 ?M5551 ?M5552))
                (@intersection (@gmultiset ?M5550 ?M5551 ?M5552)
                   (@gmultiset_intersection ?M5550 ?M5551 ?M5552)), id 0)
              simple apply @gmultiset_union_comm (cost 0, pattern 
              @Comm (@gmultiset ?M5535 ?M5536 ?M5537)
                (@gmultiset ?M5535 ?M5536 ?M5537)
                (@eq (@gmultiset ?M5535 ?M5536 ?M5537))
                (@union (@gmultiset ?M5535 ?M5536 ?M5537)
                   (@gmultiset_union ?M5535 ?M5536 ?M5537)), id 0)
              simple apply @app_Permutation_comm (cost 0, pattern 
              @Comm (list ?M2135) (list ?M2135) (@Permutation ?M2135)
                (@app ?M2135), id 0)
              exact Qp.min_comm (cost 0, pattern @Comm Qp Qp (@eq Qp) Qp.min, id 0)
              exact Qp.max_comm (cost 0, pattern @Comm Qp Qp (@eq Qp) Qp.max, id 0)
              exact Qp.mul_comm (cost 0, pattern @Comm Qp Qp (@eq Qp) Qp.mul, id 0)
              exact Qp.add_comm (cost 0, pattern @Comm Qp Qp (@eq Qp) Qp.add, id 0)
              exact Qcmult_comm' (cost 0, pattern 
              @Comm Qcanon.Qc Qcanon.Qc (@eq Qcanon.Qc) Qcanon.Qcmult, id 0)
              exact Qcplus_comm' (cost 0, pattern 
              @Comm Qcanon.Qc Qcanon.Qc (@eq Qcanon.Qc) Qcanon.Qcplus, id 0)
              exact Z.mul_comm' (cost 0, pattern @Comm Z Z (@eq Z) Z.mul, id 0)
              exact Z.add_comm' (cost 0, pattern @Comm Z Z (@eq Z) Z.add, id 0)
              exact N.mul_comm' (cost 0, pattern @Comm N N (@eq N) N.mul, id 0)
              exact N.add_comm' (cost 0, pattern @Comm N N (@eq N) N.add, id 0)
              exact Pos.mul_comm' (cost 0, pattern 
              @Comm positive positive (@eq positive) Pos.mul, id 0)
              exact Pos.add_comm' (cost 0, pattern 
              @Comm positive positive (@eq positive) Pos.add, id 0)
              exact Nat.mul_comm' (cost 0, pattern 
              @Comm nat nat (@eq nat) Nat.mul, id 0)
              exact Nat.add_comm' (cost 0, pattern 
              @Comm nat nat (@eq nat) Nat.add, id 0)
              simple apply @const2_comm (cost 0, pattern 
              @Comm ?M1200 ?M1199 (@eq ?M1200) (fun _ _ : ?M1199 => ?M1201), id 0)
              exact or_comm (cost 0, pattern @Comm Prop Prop iff or, id 0)
              exact and_comm (cost 0, pattern @Comm Prop Prop iff and, id 0)
              exact iff_comm (cost 0, pattern @Comm Prop Prop iff iff, id 0)
              simple apply @flip_eq_comm (cost 0, pattern 
              @Comm Prop ?M1169 iff (fun x y : ?M1169 => @eq ?M1169 y x), id 0)
              simple apply @eq_comm (cost 0, pattern 
              @Comm Prop ?M1168 iff (@eq ?M1168), id 0)
              simple apply @difference_with_comm (cost 1, pattern 
              @Comm (option ?M2030) (option ?M2030) 
                (@eq (option ?M2030))
                (@intersection_with ?M2030 (option ?M2030)
                   (@option_intersection_with ?M2030) 
                   ?M2031), id 0)
              simple apply @option.intersection_with_comm (cost 1, pattern 
              @Comm (option ?M2027) (option ?M2027) 
                (@eq (option ?M2027))
                (@intersection_with ?M2027 (option ?M2027)
                   (@option_intersection_with ?M2027) 
                   ?M2028), id 0)
              simple apply @option.union_with_comm (cost 1, pattern 
              @Comm (option ?M2020) (option ?M2020) 
                (@eq (option ?M2020))
                (@union_with ?M2020 (option ?M2020)
                   (@option_union_with ?M2020) ?M2021), id 0)
              simple eapply @union_comm (cost 3, pattern 
              @Comm ?M3013 ?M3013
                (@equiv ?M3013 (@set_equiv_instance ?M3012 ?M3013 ?M3014))
                (@union ?M3013 ?M3017), id 0)
              simple eapply @intersection_comm (cost 5, pattern 
              @Comm ?M3107 ?M3107
                (@equiv ?M3107 (@set_equiv_instance ?M3106 ?M3107 ?M3108))
                (@intersection ?M3107 ?M3112), id 0)
              simple eapply @union_comm_L (cost 6, pattern 
              @Comm ?M3073 ?M3073 (@eq ?M3073) (@union ?M3073 ?M3077), id 0)
              simple eapply @intersection_comm_L (cost 8, pattern 
              @Comm ?M3153 ?M3153 (@eq ?M3153) (@intersection ?M3153 ?M3158), id 0)
              simple eapply @Comm_instance_1 (cost 10, pattern 
              @Comm (?M4077 ?M4087) (?M4077 ?M4087) 
                (@eq (?M4077 ?M4087))
                (@intersection_with ?M4087 (?M4077 ?M4087)
                   (@map_intersection_with ?M4077 ?M4083 ?M4087) 
                   ?M4088), id 0)
              simple eapply @Comm_instance_0 (cost 10, pattern 
              @Comm (?M3985 ?M3995) (?M3985 ?M3995) 
                (@eq (?M3985 ?M3995))
                (@union_with ?M3995 (?M3985 ?M3995)
                   (@map_union_with ?M3985 ?M3991 ?M3995) 
                   ?M3996), id 0)
              simple eapply @merge_comm' (cost 10, pattern 
              @Comm (?M3900 ?M3910) (?M3900 ?M3910) 
                (@eq (?M3900 ?M3910))
                (@merge ?M3900 ?M3906 ?M3910 ?M3910 ?M3910 ?M3911), id 0)
For Countable (modes !
-) ->   simple apply @topGset_countable (cost 0, pattern 
        @Countable (@topGset ?M5900 ?M5901 ?M5902)
          (@topGset_eq_dec ?M5900 ?M5901 ?M5902), id 0)
        exact namespace_countable (cost 0, pattern 
        @Countable namespace namespace_eq_dec, id 0)
        simple apply @gmultiset_countable (cost 0, pattern 
        @Countable (@gmultiset ?M5303 ?M5304 ?M5305)
          (@gmultiset_eq_dec ?M5303 ?M5304 ?M5305), id 0)
        simple apply @coGset_countable (cost 0, pattern 
        @Countable (@coGset ?M5240 ?M5241 ?M5242)
          (@coGset_eq_dec ?M5240 ?M5241 ?M5242), id 0)
        exact coPset_countable (cost 0, pattern @Countable coPset
                                                 coPset_eq_dec, id 0)
        simple apply @gset_countable (cost 0, pattern 
        @Countable (@gset ?M5173 ?M5174 ?M5175)
          (@gset_eq_dec ?M5173 ?M5174 ?M5175), id 0)
        exact binder_countable (cost 0, pattern @Countable binder
                                                 binder_dec_eq, id 0)
        exact String.countable (cost 0, pattern @Countable string
                                                 String.eq_dec, id 0)
        exact Ascii.countable (cost 0, pattern @Countable Ascii.ascii
                                                 Ascii.eq_dec, id 0)
        simple apply fin_countable (cost 0, pattern 
        @Countable (Fin.t ?M2478) (@fin_dec ?M2478), id 0)
        exact Qp_countable (cost 0, pattern @Countable Qp Qp.eq_dec, id 0)
        exact Qc_countable (cost 0, pattern @Countable Qcanon.Qc Qc_eq_dec, id 0)
        exact nat_countable (cost 0, pattern @Countable nat Nat.eq_dec, id 0)
        exact Z_countable (cost 0, pattern @Countable Z Z.eq_dec, id 0)
        exact N_countable (cost 0, pattern @Countable N N.eq_dec, id 0)
        exact pos_countable (cost 0, pattern @Countable positive Pos.eq_dec, id 0)
        exact bool_countable (cost 0, pattern @Countable bool bool_eq_dec, id 0)
        exact unit_countable (cost 0, pattern @Countable unit unit_eq_dec, id 0)
        exact Empty_set_countable (cost 0, pattern 
        @Countable Empty_set Empty_set_eq_dec, id 0)
        simple apply @gmap_countable (cost 1, pattern 
        @Countable (@gmap ?M5143 ?M5144 ?M5145 ?M5146)
          (@gmap_eq_dec ?M5143 ?M5144 ?M5145 ?M5146 ?M5147), id 0)
        simple apply @Pmap_countable (cost 1, pattern 
        @Countable (Pmap ?M5094) (@Pmap_eq_dec ?M5094 ?M5095), id 0)
        simple apply @finite_countable ; trivial (cost 1, pattern 
        @Countable ?M2519 ?M2520, id 0)
        simple apply @vec_countable (cost 1, pattern 
        @Countable (Vector.t ?M2515 ?M2518) (@vec_dec ?M2515 ?M2516 ?M2518), id 0)
        simple apply @gen_tree_countable (cost 1, pattern 
        @Countable (gen_tree ?M2481) (@gen_tree_dec ?M2481 ?M2482), id 0)
        simple apply @list_countable (cost 1, pattern 
        @Countable (list ?M2475) (@list_eq_dec ?M2475 ?M2476), id 0)
        simple apply @option_countable (cost 1, pattern 
        @Countable (option ?M2448) (@option_eq_dec ?M2448 ?M2449), id 0)
        simple eapply @mapset_countable (cost 2, pattern 
        @Countable (mapset' (?M5042 unit)) (@mapset_eq_dec ?M5042 ?M5043), id 0)
        simple apply @sigT_countable (cost 2, pattern 
        @Countable (@sigT ?M2469 ?M2472)
          (@sigT_eq_dec ?M2469 ?M2472 ?M2470 ?M2473), id 0)
        simple apply @sig_countable (cost 2, pattern 
        @Countable (@sig ?M2463 (fun x : ?M2463 => ?M2466 x))
          (@sig_eq_dec ?M2463 ?M2466 ?M2468 ?M2464), id 0)
        simple apply @prod_countable (cost 2, pattern 
        @Countable (prod ?M2457 ?M2460)
          (@prod_eq_dec ?M2457 ?M2458 ?M2460 ?M2461), id 0)
        simple apply @sum_countable (cost 2, pattern 
        @Countable (sum ?M2451 ?M2454)
          (@sum_eq_dec ?M2451 ?M2452 ?M2454 ?M2455), id 0)
For ZifyClasses.CstOp ->   exact ZifyInst.Op_Z_Z0 (cost 0, pattern 
                           @ZifyClasses.CstOp Z Z Z0 ZifyInst.Inj_Z_Z, id 0)
                           exact ZifyInst.Op_N_N0 (cost 0, pattern 
                           @ZifyClasses.CstOp N Z N0 ZifyInst.Inj_N_Z, id 0)
                           exact ZifyInst.Op_xH (cost 0, pattern 
                           @ZifyClasses.CstOp positive Z xH
                             ZifyInst.Inj_pos_Z, id 0)
                           exact ZifyInst.Op_O (cost 0, pattern 
                           @ZifyClasses.CstOp nat Z O ZifyInst.Inj_nat_Z, id 0)
For DecidableClass.Decidable ->   simple apply Z.Decidable_ge_Z (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Z.ge ?M1515 ?M1516), id 0)
                                  simple apply Z.Decidable_gt_Z (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Z.gt ?M1513 ?M1514), id 0)
                                  simple apply Z.Decidable_le_Z (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Z.le ?M1511 ?M1512), id 0)
                                  simple apply Z.Decidable_lt_Z (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Z.lt ?M1509 ?M1510), id 0)
                                  simple apply Z.Decidable_eq_Z (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Z.eq ?M1507 ?M1508), id 0)
                                  simple apply Nat.Decidable_le_nat (cost 0, pattern 
                                  DecidableClass.Decidable 
                                    (le ?M585 ?M586), id 0)
                                  simple apply Nat.Decidable_eq_nat (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (Nat.eq ?M583 ?M584), id 0)
                                  simple apply Decidable_eq_bool (cost 0, pattern 
                                  DecidableClass.Decidable
                                    (@eq bool ?M336 ?M337), id 0)
                                  simple apply @DecidableClass.Decidable_not (cost 1, pattern 
                                  DecidableClass.Decidable 
                                    (not ?M332), id 0)
For Decision (modes !) ->   simple apply coPset_infinite_dec (cost 0, pattern 
                            Decision
                              (@set_infinite positive coPset coPset_elem_of
                                 ?M5236), id 0)
                            simple apply coPset_finite_dec (cost 0, pattern 
                            Decision
                              (@set_finite positive coPset coPset_elem_of
                                 ?M5227), id 0)
                            simple apply @listset_empty_dec (cost 0, pattern 
                            Decision
                              (@equiv (listset ?M4591)
                                 (@set_equiv_instance 
                                    ?M4591 (listset ?M4591)
                                    (@listset_elem_of ?M4591))
                                 ?M4592
                                 (@empty (listset ?M4591)
                                    (@listset_empty ?M4591))), id 0)
                            simple apply @list_eq_nil_dec (cost 0, pattern 
                            Decision (@eq (list ?M2122) ?M2123 (@nil ?M2122)), id 0)
                            simple apply @option_None_eq_dec (cost 0, pattern 
                            Decision
                              (@eq (option ?M1971) (@None ?M1971) ?M1972), id 0)
                            simple apply @option_eq_None_dec (cost 0, pattern 
                            Decision
                              (@eq (option ?M1969) ?M1970 (@None ?M1969)), id 0)
                            simple apply @is_Some_dec (cost 0, pattern 
                            Decision (@is_Some ?M1937 ?M1938), id 0)
                            simple apply Is_true_dec (cost 0, pattern 
                            Decision (Is_true ?M1881), id 0)
                            simple apply @decide_rel (cost 1, pattern 
                            Decision (?M5950 ?M5952 ?M5953), id 0)
                            simple apply @topGset_finite_dec (cost 1, pattern 
                            Decision
                              (@set_finite ?M5943
                                 (@topGset ?M5943 ?M5944 ?M5945)
                                 (@topGset_elem_of ?M5943 ?M5944 ?M5945)
                                 ?M5947), id 0)
                            simple apply @StronglySorted_dec (cost 1, pattern 
                            Decision (@StronglySorted ?M5884 ?M5885 ?M5887), id 0)
                            simple apply @Sorted_dec (cost 1, pattern 
                            Decision (@Sorted ?M5880 ?M5881 ?M5883), id 0)
                            simple apply @HdRel_dec (cost 1, pattern 
                            Decision (@HdRel ?M5875 ?M5876 ?M5877 ?M5879), id 0)
                            simple apply @gmultiset_Exists_dec (cost 1, pattern 
                            Decision
                              (@set_Exists ?M5363
                                 (@gmultiset ?M5363 ?M5364 ?M5365)
                                 (@gmultiset_elem_of ?M5363 ?M5364 ?M5365)
                                 ?M5366 ?M5367), id 0)
                            simple apply @gmultiset_Forall_dec (cost 1, pattern 
                            Decision
                              (@set_Forall ?M5357
                                 (@gmultiset ?M5357 ?M5358 ?M5359)
                                 (@gmultiset_elem_of ?M5357 ?M5358 ?M5359)
                                 ?M5360 ?M5361), id 0)
                            simple apply @coGset_finite_dec (cost 1, pattern 
                            Decision
                              (@set_finite ?M5289
                                 (@coGset ?M5289 ?M5290 ?M5291)
                                 (@coGset_elem_of ?M5289 ?M5290 ?M5291)
                                 ?M5293), id 0)
                            simple apply @Exists_dec (cost 1, pattern 
                            Decision (@Exists ?M2167 ?M2168 ?M2170), id 0)
                            simple apply @Forall_dec (cost 1, pattern 
                            Decision (@Forall ?M2163 ?M2164 ?M2166), id 0)
                            simple apply @NoDup_dec (cost 1, pattern 
                            Decision (@NoDup ?M2128 ?M2130), id 0)
                            simple apply @uncurry_dec (cost 1, pattern 
                            Decision
                              (@uncurry ?M1908 ?M1909 Prop ?M1910 ?M1912), id 0)
                            simple apply @not_dec (cost 1, pattern 
                            Decision (not ?M1882), id 0)
                            simple apply @iff_dec (cost 2, pattern 
                            Decision (iff ?M1896 ?M1898), id 0)
                            simple apply @impl_dec (cost 2, pattern 
                            Decision (forall _ : ?M1892, ?M1894), id 0)
                            simple apply @or_dec (cost 2, pattern 
                            Decision (or ?M1888 ?M1890), id 0)
                            simple apply @and_dec (cost 2, pattern 
                            Decision (and ?M1884 ?M1886), id 0)
                            simple eapply @exists_dec (cost 3, pattern 
                            Decision
                              (@ex ?M2527 (fun x : ?M2527 => ?M2530 x)), id 0)
                            simple eapply @forall_dec (cost 3, pattern 
                            Decision (forall x : ?M2522, ?M2525 x), id 0)
                            simple eapply @map_Exists_dec (cost 9, pattern 
                            Decision
                              (@map_Exists ?M3828 
                                 ?M3839 (?M3829 ?M3839) 
                                 (?M3831 ?M3839) ?M3840 
                                 ?M3842), id 0)
                            simple eapply @map_Forall_dec (cost 9, pattern 
                            Decision
                              (@map_Forall ?M3813 
                                 ?M3824 (?M3814 ?M3824) 
                                 (?M3816 ?M3824) ?M3825 
                                 ?M3827), id 0)
                            simple eapply @map_eq_dec_empty (cost 20, pattern 
                            Decision
                              (@eq (?M3801 ?M3811) 
                                 ?M3812
                                 (@empty (?M3801 ?M3811) (?M3804 ?M3811))), id 0)
                            simple eapply @set_Exists_dec (cost 100, pattern 
                            Decision
                              (@set_Exists ?M3657 ?M3658 ?M3659 ?M3668 ?M3670), id 0)
                            simple eapply @set_Forall_dec (cost 100, pattern 
                            Decision
                              (@set_Forall ?M3643 ?M3644 ?M3645 ?M3654 ?M3656), id 0)
                            exact False_dec (cost 1000, pattern 
                            Decision False, id 0)
                            exact True_dec (cost 1000, pattern 
                            Decision True, id 0)
For DeclConstantZ.DeclaredConstant ->   exact DeclConstantZ.DZpow (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall (_ : Z) (_ : Z), Z)
                                          BinIntDef.Z.pow, id 0)
                                        exact DeclConstantZ.DZpow_pos (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall (_ : Z) (_ : positive), Z)
                                          BinIntDef.Z.pow_pos, id 0)
                                        exact DeclConstantZ.DZneg (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall _ : positive, Z) Zneg, id 0)
                                        exact DeclConstantZ.DZpos (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall _ : positive, Z) Zpos, id 0)
                                        exact DeclConstantZ.DZO (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant Z Z0, id 0)
                                        exact DeclConstantZ.DxO (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall _ : positive, positive) xO, id 0)
                                        exact DeclConstantZ.DxI (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall _ : positive, positive) xI, id 0)
                                        exact DeclConstantZ.DxH (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          positive xH, id 0)
                                        exact DeclConstantZ.DS (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant
                                          (forall _ : nat, nat) S, id 0)
                                        exact DeclConstantZ.DO (cost 0, pattern 
                                        @DeclConstantZ.DeclaredConstant nat O, id 0)
For DefaultRelation ->   simple apply @equiv_default_relation (cost 3, pattern 
                         @DefaultRelation ?M1148 (@equiv ?M1148 ?M1149), id 0)
                         simple apply @equivalence_default (cost 4, pattern 
                         @DefaultRelation ?M530 ?M531, id 0)
For Delete (modes -
!) ->   simple apply @list_delete (cost 0, pattern 
        Delete nat (list ?M2107), id 0)
        simple eapply @map_delete (cost 2, pattern 
        Delete ?M3704 ?M3706, id 0)
For Difference (modes !) ->   simple apply @propset_difference (cost 0, pattern 
                              Difference (propset ?M5832), id 0)
                              simple apply @gmultiset_difference (cost 0, pattern 
                              Difference (@gmultiset ?M5336 ?M5337 ?M5338), id 0)
                              simple apply @coGset_difference (cost 0, pattern 
                              Difference (@coGset ?M5261 ?M5262 ?M5263), id 0)
                              exact coPset_difference (cost 0, pattern 
                              Difference coPset, id 0)
                              simple apply @gset_difference (cost 0, pattern 
                              Difference (@gset ?M5164 ?M5165 ?M5166), id 0)
                              simple apply @boolset_difference (cost 0, pattern 
                              Difference (boolset ?M4648), id 0)
                              simple apply @listset_nodup_difference (cost 1, pattern 
                              Difference (listset_nodup ?M5669), id 0)
                              simple apply @hashset_difference (cost 1, pattern 
                              Difference (@hashset ?M5654 ?M5656), id 0)
                              simple apply @mapset_difference (cost 1, pattern 
                              Difference (mapset' (?M5013 unit)), id 0)
                              simple apply @listset_difference (cost 1, pattern 
                              Difference (listset ?M4597), id 0)
                              simple apply @map_difference (cost 1, pattern 
                              Difference (?M3741 ?M3743), id 0)
For DifferenceWith (modes -
!) ->   simple apply @option_difference_with (cost 0, pattern 
        DifferenceWith ?M2009 (option ?M2009), id 0)
        simple apply @map_difference_with (cost 1, pattern 
        DifferenceWith ?M3725 (?M3723 ?M3725), id 0)
For DisjUnion (modes !) ->   simple apply @gmultiset_disj_union (cost 0, pattern 
                             DisjUnion (@gmultiset ?M5333 ?M5334 ?M5335), id 0)
For Disjoint (modes !) ->   exact ndisjoint (cost 0, pattern 
                            Disjoint namespace, id 0)
                            simple eapply @set_disjoint_instance (cost 20, pattern 
                            Disjoint ?M2569, id 0)
For Dom (modes !
-) ->   simple apply @Nmap_dom (cost 0, pattern Dom 
                                                 (Nmap ?M5825)
                                                 (mapset' (Nmap unit)), id 0)
        simple apply @natmap_dom (cost 0, pattern 
        Dom (natmap ?M5818) (mapset' (natmap unit)), id 0)
        simple apply @Zmap_dom (cost 0, pattern Dom 
                                                 (Zmap ?M5641)
                                                 (mapset' (Zmap unit)), id 0)
        simple apply @gmultiset_dom (cost 0, pattern 
        Dom (@gmultiset ?M5342 ?M5343 ?M5344) (@gset ?M5342 ?M5343 ?M5344), id 0)
        simple apply @gset_dom (cost 0, pattern Dom
                                                 (@gmap 
                                                 ?M5188 
                                                 ?M5189 
                                                 ?M5190 
                                                 ?M5191)
                                                 (@gset ?M5188 ?M5189 ?M5190), id 0)
        simple apply @Pmap_dom (cost 0, pattern Dom 
                                                 (Pmap ?M5097)
                                                 (mapset' (Pmap unit)), id 0)
For ElemOf (modes -
!) ->   simple apply @topGset_elem_of (cost 0, pattern 
        ElemOf ?M5903 (@topGset ?M5903 ?M5904 ?M5905), id 0)
        simple apply @propset_elem_of (cost 0, pattern 
        ElemOf ?M5826 (propset ?M5826), id 0)
        simple apply @listset_nodup_elem_of (cost 0, pattern 
        ElemOf ?M5662 (listset_nodup ?M5662), id 0)
        simple apply @hashset_elem_of (cost 0, pattern 
        ElemOf ?M5642 (@hashset ?M5642 ?M5643), id 0)
        simple apply @gmultiset_elem_of (cost 0, pattern 
        ElemOf ?M5306 (@gmultiset ?M5306 ?M5307 ?M5308), id 0)
        simple apply @coGset_elem_of (cost 0, pattern 
        ElemOf ?M5243 (@coGset ?M5243 ?M5244 ?M5245), id 0)
        exact coPset_elem_of (cost 0, pattern ElemOf positive coPset, id 0)
        simple apply @gset_elem_of (cost 0, pattern 
        ElemOf ?M5149 (@gset ?M5149 ?M5150 ?M5151), id 0)
        simple apply @boolset_elem_of (cost 0, pattern 
        ElemOf ?M4645 (boolset ?M4645), id 0)
        simple apply @listset_elem_of (cost 0, pattern 
        ElemOf ?M4586 (listset ?M4586), id 0)
        simple apply @list_elem_of (cost 0, pattern 
        ElemOf ?M1504 (list ?M1504), id 0)
        simple apply @mapset_elem_of (cost 1, pattern 
        ElemOf ?M5000 (mapset' (?M5001 unit)), id 0)
For Elements (modes -
!) ->   simple apply @listset_nodup_elems (cost 0, pattern 
        Elements ?M5671 (listset_nodup ?M5671), id 0)
        simple apply @hashset_elements (cost 0, pattern 
        Elements ?M5657 (@hashset ?M5657 ?M5658), id 0)
        simple apply @gmultiset_elements (cost 0, pattern 
        Elements ?M5315 (@gmultiset ?M5315 ?M5316 ?M5317), id 0)
        simple apply @gset_elements (cost 0, pattern 
        Elements ?M5167 (@gset ?M5167 ?M5168 ?M5169), id 0)
        simple apply @mapset_elements (cost 1, pattern 
        Elements ?M5015 (mapset' (?M5016 unit)), id 0)
        simple apply @listset_elements (cost 1, pattern 
        Elements ?M4599 (listset ?M4599), id 0)
For Empty (modes !) ->   simple apply @topGset_empty (cost 0, pattern 
                         Empty (@topGset ?M5906 ?M5907 ?M5908), id 0)
                         simple apply @propset_empty (cost 0, pattern 
                         Empty (propset ?M5828), id 0)
                         simple apply @Nmap_empty (cost 0, pattern 
                         Empty (Nmap ?M5821), id 0)
                         simple apply @natmap_empty (cost 0, pattern 
                         Empty (natmap ?M5814), id 0)
                         simple apply @listset_nodup_empty (cost 0, pattern 
                         Empty (listset_nodup ?M5663), id 0)
                         simple apply @hashset_empty (cost 0, pattern 
                         Empty (@hashset ?M5644 ?M5645), id 0)
                         simple apply @Zmap_empty (cost 0, pattern 
                         Empty (Zmap ?M5637), id 0)
                         simple apply @gmultiset_empty (cost 0, pattern 
                         Empty (@gmultiset ?M5321 ?M5322 ?M5323), id 0)
                         simple apply @coGset_empty (cost 0, pattern 
                         Empty (@coGset ?M5246 ?M5247 ?M5248), id 0)
                         exact coPset_empty (cost 0, pattern 
                         Empty coPset, id 0)
                         simple apply @gset_empty (cost 0, pattern 
                         Empty (@gset ?M5152 ?M5153 ?M5154), id 0)
                         simple apply @gmap_empty (cost 0, pattern 
                         Empty (@gmap ?M5119 ?M5120 ?M5121 ?M5122), id 0)
                         simple apply @Pmap_empty (cost 0, pattern 
                         Empty (Pmap ?M5091), id 0)
                         simple apply @boolset_empty (cost 0, pattern 
                         Empty (boolset ?M4642), id 0)
                         simple apply @listset_empty (cost 0, pattern 
                         Empty (listset ?M4587), id 0)
                         simple apply @mapset_empty (cost 1, pattern 
                         Empty (mapset' (?M5003 unit)), id 0)
For Equiv (modes !) ->   simple apply @stream_equiv (cost 0, pattern 
                         Equiv (stream ?M5888), id 0)
                         simple apply @gmultiset_equiv (cost 0, pattern 
                         Equiv (@gmultiset ?M5312 ?M5313 ?M5314), id 0)
                         exact Empty_set_equiv (cost 0, pattern 
                         Equiv Empty_set, id 0)
                         exact unit_equiv (cost 0, pattern 
                         Equiv unit, id 0)
                         simple apply @list_equiv (cost 1, pattern 
                         Equiv (list ?M2125), id 0)
                         simple apply @option_equiv (cost 1, pattern 
                         Equiv (option ?M1951), id 0)
                         simple apply @sum_equiv (cost 2, pattern 
                         Equiv (sum ?M1471 ?M1473), id 0)
                         simple apply @prod_equiv (cost 2, pattern 
                         Equiv (prod ?M1329 ?M1331), id 0)
                         simple eapply @map_equiv (cost 20, pattern 
                         Equiv (?M3727 ?M3729), id 0)
                         simple eapply @set_equiv_instance (cost 20, pattern 
                         Equiv ?M2563, id 0)
For CRelationClasses.Equivalence ->   simple apply @CRelationClasses.relation_equivalence_equivalence (cost 0, pattern 
                                      @CRelationClasses.Equivalence
                                        (CRelationClasses.crelation ?M426)
                                        (@CRelationClasses.relation_equivalence
                                           ?M426), id 0)
                                      exact CRelationClasses.iff_equivalence (cost 0, pattern 
                                      @CRelationClasses.Equivalence Prop iff, id 0)
                                      simple apply @CRelationClasses.eq_equivalence (cost 10, pattern 
                                      @CRelationClasses.Equivalence 
                                        ?M421 (@eq ?M421), id 0)
For Equivalence (modes -
!) ->   simple apply @equal_equivalence (cost 0, pattern 
        @Equivalence (stream ?M5889)
          (@equiv (stream ?M5889) (@stream_equiv ?M5889)), id 0)
        simple apply @gmultiset_equiv_equivalence (cost 0, pattern 
        @Equivalence (@gmultiset ?M5351 ?M5352 ?M5353)
          (@equiv (@gmultiset ?M5351 ?M5352 ?M5353)
             (@gmultiset_equiv ?M5351 ?M5352 ?M5353)), id 0)
        simple apply @rtsc_equivalence (cost 0, pattern 
        @Equivalence ?M3395 (@rtsc ?M3395 ?M3396), id 0)
        simple apply @set_equiv_equivalence (cost 0, pattern 
        @Equivalence ?M2572
          (@equiv ?M2572 (@set_equiv_instance ?M2571 ?M2572 ?M2573)), id 0)
        exact QArith_base.Q_Setoid (cost 0, pattern 
        @Equivalence QArith_base.Q QArith_base.Qeq, id 0)
        exact PositiveOrder.TO.eq_equiv (cost 0, pattern 
        @Equivalence positive (@eq positive), id 0)
        exact Z.eqf_equiv (cost 0, pattern @Equivalence 
                                             (forall _ : Z, bool) Z.eqf, id 0)
        exact N.eqf_equiv (cost 0, pattern @Equivalence 
                                             (forall _ : N, bool) N.eqf, id 0)
        exact Empty_set_equivalence (cost 0, pattern 
        @Equivalence Empty_set (@equiv Empty_set Empty_set_equiv), id 0)
        exact unit_equivalence (cost 0, pattern @Equivalence unit
                                                 (@equiv unit unit_equiv), id 0)
        simple apply Permutation_Equivalence (cost 0, pattern 
        @Equivalence (list ?M1071) (@Permutation ?M1071), id 0)
        exact Nat.eqf_equiv (cost 0, pattern @Equivalence
                                               (forall _ : nat, bool) Nat.eqf, id 0)
        simple apply @relation_equivalence_equivalence (cost 0, pattern 
        @Equivalence (relation ?M265) (@relation_equivalence ?M265), id 0)
        simple apply @predicate_equivalence_equivalence (cost 0, pattern 
        @Equivalence (arrows ?M262 Prop) (@predicate_equivalence ?M262), id 0)
        exact iff_equivalence (cost 0, pattern @Equivalence Prop iff, id 0)
        simple apply @map_equivalence (cost 1, pattern 
        @Equivalence (?M4151 ?M4153)
          (@equiv (?M4151 ?M4153)
             (@map_equiv ?M4150 ?M4151 ?M4152 ?M4153 ?M4154)), id 0)
        simple apply @rtc_equivalence (cost 1, pattern 
        @Equivalence ?M3385 (@rtc ?M3385 ?M3386), id 0)
        simple apply @list_equivalence (cost 1, pattern 
        @Equivalence (list ?M2241)
          (@equiv (list ?M2241) (@list_equiv ?M2241 ?M2242)), id 0)
        simple apply @Equivalence_instance_0 (cost 1, pattern 
        @Equivalence (list ?M2186) (@Forall2 ?M2186 ?M2186 ?M2187), id 0)
        simple apply @option_equivalence (cost 1, pattern 
        @Equivalence (option ?M1953)
          (@equiv (option ?M1953) (@option_equiv ?M1953 ?M1954)), id 0)
        simple apply @option_Forall2_equiv (cost 1, pattern 
        @Equivalence (option ?M1948) (@option_Forall2 ?M1948 ?M1948 ?M1949), id 0)
        simple apply @sum_relation_equiv (cost 2, pattern 
        @Equivalence (sum ?M1449 ?M1451)
          (@sum_relation ?M1449 ?M1451 ?M1450 ?M1452), id 0)
        simple apply @prod_equivalence (cost 2, pattern 
        @Equivalence (prod ?M1333 ?M1335)
          (@equiv (prod ?M1333 ?M1335)
             (@prod_equiv ?M1333 ?M1334 ?M1335 ?M1336)), id 0)
        simple apply @prod_relation_equiv (cost 2, pattern 
        @Equivalence (prod ?M1255 ?M1257)
          (@prod_relation ?M1255 ?M1257 ?M1256 ?M1258), id 0)
        simple apply @Equivalence.pointwise_equivalence (cost 9, pattern 
        @Equivalence (forall _ : ?M526, ?M527)
          (@pointwise_relation ?M526 ?M527 ?M528), id 0)
        simple apply @eq_equivalence (cost 10, pattern 
        @Equivalence ?M257 (@eq ?M257), id 0)
        simple apply Permutation_transp_equiv (cost 100, pattern 
        @Equivalence (list ?M1086) (@Permutation_transp ?M1086), id 0)
For FMap (modes !) ->   simple apply @tele_fmap (cost 0, pattern 
                        FMap (tele_fun ?M5896), id 0)
                        exact stream_fmap (cost 0, pattern 
                        FMap stream, id 0)
                        exact propset_fmap (cost 0, pattern 
                        FMap propset, id 0)
                        exact Nmap_fmap (cost 0, pattern 
                        FMap Nmap, id 0)
                        exact natmap_fmap (cost 0, pattern 
                        FMap natmap, id 0)
                        exact Zmap_fmap (cost 0, pattern 
                        FMap Zmap, id 0)
                        simple apply @gmap_fmap (cost 0, pattern 
                        FMap (@gmap ?M5127 ?M5128 ?M5129), id 0)
                        exact Pmap_fmap (cost 0, pattern 
                        FMap Pmap, id 0)
                        exact listset_fmap (cost 0, pattern 
                        FMap listset, id 0)
                        exact list_fmap (cost 0, pattern 
                        FMap list, id 0)
                        exact option_fmap (cost 0, pattern 
                        FMap option, id 0)
For Filter (modes -
!) ->   simple apply @gmultiset_filter (cost 0, pattern 
        Filter ?M5345 (@gmultiset ?M5345 ?M5346 ?M5347), id 0)
        simple apply @list_filter (cost 0, pattern 
        Filter ?M2109 (list ?M2109), id 0)
        simple apply @map_filter (cost 3, pattern 
        Filter (prod ?M3744 ?M3745) ?M3746, id 0)
        simple apply @set_filter (cost 4, pattern 
        Filter ?M3400 ?M3401, id 0)
For FinMap ->   exact Nmap_map (cost 0, pattern @FinMap N Nmap Nmap_fmap
                                                 (@Nmap_lookup) 
                                                 (@Nmap_empty)
                                                 (@Nmap_partial_alter)
                                                 Nmap_omap Nmap_merge
                                                 (@Nmap_fold) N.eq_dec, id 0)
                exact natmap_map (cost 0, pattern 
                @FinMap nat natmap natmap_fmap (@natmap_lookup)
                  (@natmap_empty) (@natmap_partial_alter) natmap_omap
                  natmap_merge (@natmap_fold) Nat.eq_dec, id 0)
                exact Zmap_map (cost 0, pattern @FinMap Z Zmap Zmap_fmap
                                                 (@Zmap_lookup) 
                                                 (@Zmap_empty)
                                                 (@Zmap_partial_alter)
                                                 Zmap_omap Zmap_merge
                                                 (@Zmap_fold) Z.eq_dec, id 0)
                simple apply @gmap_finmap (cost 0, pattern 
                @FinMap ?M5140 (@gmap ?M5140 ?M5141 ?M5142)
                  (@gmap_fmap ?M5140 ?M5141 ?M5142)
                  (@gmap_lookup ?M5140 ?M5141 ?M5142)
                  (@gmap_empty ?M5140 ?M5141 ?M5142)
                  (@gmap_partial_alter ?M5140 ?M5141 ?M5142)
                  (@gmap_omap ?M5140 ?M5141 ?M5142)
                  (@gmap_merge ?M5140 ?M5141 ?M5142)
                  (@gmap_fold ?M5140 ?M5141 ?M5142) 
                  ?M5141, id 0)
                exact Pmap_finmap (cost 0, pattern 
                @FinMap positive Pmap Pmap_fmap (@Pmap_lookup) 
                  (@Pmap_empty) (@Pmap_partial_alter) Pmap_omap Pmap_merge
                  (@Pmap_fold) Pos.eq_dec, id 0)
                simple eapply @finmap_dom_map (cost 9, pattern 
                @FinMap ?M6003 ?M6004 ?M6007 ?M6008 
                  ?M6009 ?M6010 ?M6011 ?M6012 ?M6013 
                  ?M6014, id 0)
For FinMapDom ->   exact nmap.FinMapDom_instance_0 (cost 0, pattern 
                   @FinMapDom N Nmap (mapset' (Nmap unit)) 
                     (@Nmap_dom) Nmap_fmap (@Nmap_lookup) 
                     (@Nmap_empty) (@Nmap_partial_alter) Nmap_omap Nmap_merge
                     (@Nmap_fold) N.eq_dec
                     (@mapset_elem_of N Nmap (@Nmap_lookup))
                     (@mapset_empty Nmap (@Nmap_empty))
                     (@mapset_singleton N Nmap (@Nmap_empty)
                        (@Nmap_partial_alter))
                     (@mapset_union Nmap Nmap_merge)
                     (@mapset_intersection Nmap Nmap_merge)
                     (@mapset_difference Nmap Nmap_merge), id 0)
                   exact natmap.FinMapDom_instance_0 (cost 0, pattern 
                   @FinMapDom nat natmap (mapset' (natmap unit))
                     (@natmap_dom) natmap_fmap (@natmap_lookup)
                     (@natmap_empty) (@natmap_partial_alter) natmap_omap
                     natmap_merge (@natmap_fold) Nat.eq_dec
                     (@mapset_elem_of nat natmap (@natmap_lookup))
                     (@mapset_empty natmap (@natmap_empty))
                     (@mapset_singleton nat natmap 
                        (@natmap_empty) (@natmap_partial_alter))
                     (@mapset_union natmap natmap_merge)
                     (@mapset_intersection natmap natmap_merge)
                     (@mapset_difference natmap natmap_merge), id 0)
                   exact FinMapDom_instance_0 (cost 0, pattern 
                   @FinMapDom Z Zmap (mapset' (Zmap unit)) 
                     (@Zmap_dom) Zmap_fmap (@Zmap_lookup) 
                     (@Zmap_empty) (@Zmap_partial_alter) Zmap_omap Zmap_merge
                     (@Zmap_fold) Z.eq_dec
                     (@mapset_elem_of Z Zmap (@Zmap_lookup))
                     (@mapset_empty Zmap (@Zmap_empty))
                     (@mapset_singleton Z Zmap (@Zmap_empty)
                        (@Zmap_partial_alter))
                     (@mapset_union Zmap Zmap_merge)
                     (@mapset_intersection Zmap Zmap_merge)
                     (@mapset_difference Zmap Zmap_merge), id 0)
                   simple apply @gset_dom_spec (cost 0, pattern 
                   @FinMapDom ?M5204 (@gmap ?M5204 ?M5205 ?M5206)
                     (@gset ?M5204 ?M5205 ?M5206)
                     (@gset_dom ?M5204 ?M5205 ?M5206)
                     (@gmap_fmap ?M5204 ?M5205 ?M5206)
                     (@gmap_lookup ?M5204 ?M5205 ?M5206)
                     (@gmap_empty ?M5204 ?M5205 ?M5206)
                     (@gmap_partial_alter ?M5204 ?M5205 ?M5206)
                     (@gmap_omap ?M5204 ?M5205 ?M5206)
                     (@gmap_merge ?M5204 ?M5205 ?M5206)
                     (@gmap_fold ?M5204 ?M5205 ?M5206) 
                     ?M5205 (@gset_elem_of ?M5204 ?M5205 ?M5206)
                     (@gset_empty ?M5204 ?M5205 ?M5206)
                     (@gset_singleton ?M5204 ?M5205 ?M5206)
                     (@gset_union ?M5204 ?M5205 ?M5206)
                     (@gset_intersection ?M5204 ?M5205 ?M5206)
                     (@gset_difference ?M5204 ?M5205 ?M5206), id 0)
                   exact Pmap_dom_spec (cost 0, pattern 
                   @FinMapDom positive Pmap (mapset' (Pmap unit)) 
                     (@Pmap_dom) Pmap_fmap (@Pmap_lookup) 
                     (@Pmap_empty) (@Pmap_partial_alter) Pmap_omap Pmap_merge
                     (@Pmap_fold) Pos.eq_dec
                     (@mapset_elem_of positive Pmap (@Pmap_lookup))
                     (@mapset_empty Pmap (@Pmap_empty))
                     (@mapset_singleton positive Pmap 
                        (@Pmap_empty) (@Pmap_partial_alter))
                     (@mapset_union Pmap Pmap_merge)
                     (@mapset_intersection Pmap Pmap_merge)
                     (@mapset_difference Pmap Pmap_merge), id 0)
For FinSet (modes - ! - - - - - - -
-) ->   simple apply @listset_nodup_fin_set (cost 0, pattern 
        @FinSet ?M5672 (listset_nodup ?M5672) (@listset_nodup_elem_of ?M5672)
          (@listset_nodup_empty ?M5672) (@listset_nodup_singleton ?M5672)
          (@listset_nodup_union ?M5672 ?M5673)
          (@listset_nodup_intersection ?M5672 ?M5673)
          (@listset_nodup_difference ?M5672 ?M5673)
          (@listset_nodup_elems ?M5672) ?M5673, id 0)
        simple apply @hashset_fin_set (cost 0, pattern 
        @FinSet ?M5659 (@hashset ?M5659 ?M5661)
          (@hashset_elem_of ?M5659 ?M5661) (@hashset_empty ?M5659 ?M5661)
          (@hashset_singleton ?M5659 ?M5661)
          (@hashset_union ?M5659 ?M5660 ?M5661)
          (@hashset_intersection ?M5659 ?M5660 ?M5661)
          (@hashset_difference ?M5659 ?M5660 ?M5661)
          (@hashset_elements ?M5659 ?M5661) ?M5660, id 0)
        simple apply @gset_fin_set (cost 0, pattern 
        @FinSet ?M5201 (@gset ?M5201 ?M5202 ?M5203)
          (@gset_elem_of ?M5201 ?M5202 ?M5203)
          (@gset_empty ?M5201 ?M5202 ?M5203)
          (@gset_singleton ?M5201 ?M5202 ?M5203)
          (@gset_union ?M5201 ?M5202 ?M5203)
          (@gset_intersection ?M5201 ?M5202 ?M5203)
          (@gset_difference ?M5201 ?M5202 ?M5203)
          (@gset_elements ?M5201 ?M5202 ?M5203) ?M5202, id 0)
        simple apply @listset_fin_set (cost 0, pattern 
        @FinSet ?M4601 (listset ?M4601) (@listset_elem_of ?M4601)
          (@listset_empty ?M4601) (@listset_singleton ?M4601)
          (@listset_union ?M4601) (@listset_intersection ?M4601 ?M4602)
          (@listset_difference ?M4601 ?M4602)
          (@listset_elements ?M4601 ?M4602) ?M4602, id 0)
        simple eapply @mapset_fin_set (cost 3, pattern 
        @FinSet ?M5029 (mapset' (?M5030 unit))
          (@mapset_elem_of ?M5029 ?M5030 ?M5032)
          (@mapset_empty ?M5030 ?M5033)
          (@mapset_singleton ?M5029 ?M5030 ?M5033 ?M5034)
          (@mapset_union ?M5030 ?M5036) (@mapset_intersection ?M5030 ?M5036)
          (@mapset_difference ?M5030 ?M5036)
          (@mapset_elements ?M5029 ?M5030 ?M5037) 
          ?M5038, id 0)
For Finite (modes !
-) ->   simple apply fin_finite (cost 0, pattern @Finite 
                                                 (Fin.t ?M2555)
                                                 (@fin_dec ?M2555), id 0)
        exact bool_finite (cost 0, pattern @Finite bool bool_eq_dec, id 0)
        exact unit_finite (cost 0, pattern @Finite unit unit_eq_dec, id 0)
        exact Empty_set_finite (cost 0, pattern @Finite Empty_set
                                                 Empty_set_eq_dec, id 0)
        simple apply @list_finite (cost 1, pattern 
        @Finite
          (@sig (list ?M2551)
             (fun l : list ?M2551 => @eq nat (@length ?M2551 l) ?M2554))
          (@sig_eq_dec (list ?M2551)
             (fun l : list ?M2551 => @eq nat (@length ?M2551 l) ?M2554)
             (fun H : list ?M2551 =>
              @eq_pi nat (@length ?M2551 H)
                (@decide_rel nat nat (@eq nat) Nat.eq_dec (@length ?M2551 H))
                ?M2554)
             (@list_eq_dec ?M2551 ?M2552)), id 0)
        simple apply @vec_finite (cost 1, pattern 
        @Finite (Vector.t ?M2547 ?M2550) (@vec_dec ?M2547 ?M2548 ?M2550), id 0)
        simple apply @option_finite (cost 1, pattern 
        @Finite (option ?M2532) (@option_eq_dec ?M2532 ?M2533), id 0)
        simple apply @sig_finite (cost 2, pattern 
        @Finite (@sig ?M2556 ?M2557)
          (@sig_eq_dec ?M2556 ?M2557 ?M2561 ?M2559), id 0)
        simple apply @prod_finite (cost 2, pattern 
        @Finite (prod ?M2541 ?M2544)
          (@prod_eq_dec ?M2541 ?M2542 ?M2544 ?M2545), id 0)
        simple apply @sum_finite (cost 2, pattern 
        @Finite (sum ?M2535 ?M2538) (@sum_eq_dec ?M2535 ?M2536 ?M2538 ?M2539), id 0)
For Fresh (modes -
!) ->   simple apply @infinite_fresh (cost 1, pattern 
        Fresh ?M5997 (list ?M5997), id 0)
        simple apply @set_fresh (cost 2, pattern Fresh ?M3406 ?M3407, id 0)
For DeclConstantZ.GT ->   simple apply @DeclConstantZ.GT_O (cost 1, pattern 
                          @DeclConstantZ.GT ?M1738 
                            ?M1739, id 0)
                          simple apply @DeclConstantZ.GT_APP1 (cost 2, pattern 
                          @DeclConstantZ.GT ?M1742 
                            (?M1743 ?M1744), id 0)
                          simple apply @DeclConstantZ.GT_APP2 (cost 3, pattern 
                          @DeclConstantZ.GT ?M1749 
                            (?M1750 ?M1751 ?M1752), id 0)
For Half (modes !) ->   
For IdemP ->   simple apply @gmultiset_intersection_idemp (cost 0, pattern 
               @IdemP (@gmultiset ?M5562 ?M5563 ?M5564)
                 (@eq (@gmultiset ?M5562 ?M5563 ?M5564))
                 (@intersection (@gmultiset ?M5562 ?M5563 ?M5564)
                    (@gmultiset_intersection ?M5562 ?M5563 ?M5564)), id 0)
               simple apply @gmultiset_union_idemp (cost 0, pattern 
               @IdemP (@gmultiset ?M5547 ?M5548 ?M5549)
                 (@eq (@gmultiset ?M5547 ?M5548 ?M5549))
                 (@union (@gmultiset ?M5547 ?M5548 ?M5549)
                    (@gmultiset_union ?M5547 ?M5548 ?M5549)), id 0)
               simple apply @id2_idemp (cost 0, pattern 
               @IdemP ?M1207 (@eq ?M1207) (fun _ x : ?M1207 => x), id 0)
               simple apply @id1_idemp (cost 0, pattern 
               @IdemP ?M1206 (@eq ?M1206) (fun x _ : ?M1206 => x), id 0)
               exact or_idemp (cost 0, pattern @IdemP Prop iff or, id 0)
               exact and_idemp (cost 0, pattern @IdemP Prop iff and, id 0)
               simple eapply @union_idemp (cost 3, pattern 
               @IdemP ?M2992
                 (@equiv ?M2992 (@set_equiv_instance ?M2991 ?M2992 ?M2993))
                 (@union ?M2992 ?M2996), id 0)
               simple eapply @intersection_idemp (cost 5, pattern 
               @IdemP ?M3098
                 (@equiv ?M3098 (@set_equiv_instance ?M3097 ?M3098 ?M3099))
                 (@intersection ?M3098 ?M3103), id 0)
               simple eapply @union_idemp_L (cost 6, pattern 
               @IdemP ?M3049 (@eq ?M3049) (@union ?M3049 ?M3053), id 0)
               simple eapply @intersection_idemp_L (cost 8, pattern 
               @IdemP ?M3143 (@eq ?M3143) (@intersection ?M3143 ?M3148), id 0)
               simple eapply @map_intersection_idemp (cost 9, pattern 
               @IdemP (?M4127 ?M4137) (@eq (?M4127 ?M4137))
                 (@intersection (?M4127 ?M4137)
                    (@map_intersection ?M4127 ?M4133 ?M4137)), id 0)
               simple eapply @map_union_idemp (cost 9, pattern 
               @IdemP (?M4035 ?M4045) (@eq (?M4035 ?M4045))
                 (@union (?M4035 ?M4045) (@map_union ?M4035 ?M4041 ?M4045)), id 0)
               simple eapply @merge_idemp' (cost 10, pattern 
               @IdemP (?M3914 ?M3924) (@eq (?M3914 ?M3924))
                 (@merge ?M3914 ?M3920 ?M3924 ?M3924 ?M3924 ?M3925), id 0)
For Infinite (modes !) ->   exact string_infinite (cost 0, pattern 
                            Infinite string, id 0)
                            exact Z_infinite (cost 0, pattern 
                            Infinite Z, id 0)
                            exact positive_infinite (cost 0, pattern 
                            Infinite positive, id 0)
                            exact N_infinite (cost 0, pattern 
                            Infinite N, id 0)
                            exact nat_infinite (cost 0, pattern 
                            Infinite nat, id 0)
                            simple apply @list_infinite (cost 1, pattern 
                            Infinite (list ?M4681), id 0)
                            simple apply @sum_infinite_r (cost 1, pattern 
                            Infinite (sum ?M4670 ?M4671), id 0)
                            simple apply @sum_infinite_l (cost 1, pattern 
                            Infinite (sum ?M4667 ?M4669), id 0)
                            simple apply @option_infinite (cost 1, pattern 
                            Infinite (option ?M4665), id 0)
                            simple apply @prod_infinite_r (cost 2, pattern 
                            Infinite (prod ?M4677 ?M4679), id 0)
                            simple apply @prod_infinite_l (cost 2, pattern 
                            Infinite (prod ?M4673 ?M4675), id 0)
For Inhabited (modes !) ->   exact binder_inhabited (cost 0, pattern 
                             Inhabited binder, id 0)
                             simple apply vec_0_inhabited (cost 0, pattern 
                             Inhabited (Vector.t ?M2511 O), id 0)
                             exact String.inhabited (cost 0, pattern 
                             Inhabited string, id 0)
                             exact Qp.inhabited (cost 0, pattern 
                             Inhabited Qp, id 0)
                             exact Z.inhabited (cost 0, pattern 
                             Inhabited Z, id 0)
                             exact N.inhabited (cost 0, pattern 
                             Inhabited N, id 0)
                             exact Pos.inhabited (cost 0, pattern 
                             Inhabited positive, id 0)
                             exact Nat.inhabited (cost 0, pattern 
                             Inhabited nat, id 0)
                             simple apply @option_inhabited (cost 0, pattern 
                             Inhabited (option ?M1491), id 0)
                             exact unit_inhabited (cost 0, pattern 
                             Inhabited unit, id 0)
                             exact bool_inhabated (cost 0, pattern 
                             Inhabited bool, id 0)
                             simple apply @list_inhabited (cost 0, pattern 
                             Inhabited (list ?M1208), id 0)
                             exact prop_inhabited (cost 0, pattern 
                             Inhabited Prop, id 0)
                             simple apply @vec_inhabited (cost 1, pattern 
                             Inhabited (Vector.t ?M2512 ?M2514), id 0)
                             simple apply @empty_inhabited (cost 1, pattern 
                             Inhabited ?M1500, id 0)
                             simple apply @sum_inhabited_r (cost 1, pattern 
                             Inhabited (sum ?M1416 ?M1417), id 0)
                             simple apply @sum_inhabited_l (cost 1, pattern 
                             Inhabited (sum ?M1413 ?M1414), id 0)
                             simple apply @forall_inhabited (cost 1, pattern 
                             Inhabited (forall x : ?M1170, ?M1171 x), id 0)
                             simple apply @prod_inhabited (cost 2, pattern 
                             Inhabited (prod ?M1217 ?M1218), id 0)
For Inj ->   simple apply @gmultiset_scalar_mul_inj_S (cost 0, pattern 
             @Inj (@gmultiset ?M5588 ?M5589 ?M5590)
               (@gmultiset ?M5588 ?M5589 ?M5590)
               (@eq (@gmultiset ?M5588 ?M5589 ?M5590))
               (@eq (@gmultiset ?M5588 ?M5589 ?M5590))
               (@scalar_mul nat (@gmultiset ?M5588 ?M5589 ?M5590)
                  (@gmultiset_scalar_mul ?M5588 ?M5589 ?M5590) 
                  (S ?M5591)), id 0)
             simple apply @gmultiset_singleton_inj (cost 0, pattern 
             @Inj ?M5585 (@gmultiset ?M5585 ?M5586 ?M5587) 
               (@eq ?M5585) (@eq (@gmultiset ?M5585 ?M5586 ?M5587))
               (@singletonMS ?M5585 (@gmultiset ?M5585 ?M5586 ?M5587)
                  (@gmultiset_singleton ?M5585 ?M5586 ?M5587)), id 0)
             simple apply @gmultiset_disj_union_inj_2 (cost 0, pattern 
             @Inj (@gmultiset ?M5581 ?M5582 ?M5583)
               (@gmultiset ?M5581 ?M5582 ?M5583)
               (@eq (@gmultiset ?M5581 ?M5582 ?M5583))
               (@eq (@gmultiset ?M5581 ?M5582 ?M5583))
               (fun y : @gmultiset ?M5581 ?M5582 ?M5583 =>
                @disj_union (@gmultiset ?M5581 ?M5582 ?M5583)
                  (@gmultiset_disj_union ?M5581 ?M5582 ?M5583) y 
                  ?M5584), id 0)
             simple apply @gmultiset_disj_union_inj_1 (cost 0, pattern 
             @Inj (@gmultiset ?M5577 ?M5578 ?M5579)
               (@gmultiset ?M5577 ?M5578 ?M5579)
               (@eq (@gmultiset ?M5577 ?M5578 ?M5579))
               (@eq (@gmultiset ?M5577 ?M5578 ?M5579))
               (@disj_union (@gmultiset ?M5577 ?M5578 ?M5579)
                  (@gmultiset_disj_union ?M5577 ?M5578 ?M5579) 
                  ?M5580), id 0)
             exact pretty_Z_inj (cost 0, pattern @Inj Z string 
                                                 (@eq Z) 
                                                 (@eq string)
                                                 (@pretty Z pretty_Z), id 0)
             exact pretty_positive_inj (cost 0, pattern 
             @Inj positive string (@eq positive) (@eq string)
               (@pretty positive pretty_positive), id 0)
             exact pretty_nat_inj (cost 0, pattern 
             @Inj nat string (@eq nat) (@eq string) 
               (@pretty nat pretty_nat), id 0)
             exact pretty_N_inj (cost 0, pattern @Inj N string 
                                                 (@eq N) 
                                                 (@eq string)
                                                 (@pretty N pretty_N), id 0)
             simple apply String.app_inj (cost 0, pattern 
             @Inj string string (@eq string) (@eq string)
               (String.append ?M2486), id 0)
             simple apply @encode_Z_inj (cost 0, pattern 
             @Inj ?M2445 Z (@eq ?M2445) (@eq Z)
               (@encode_Z ?M2445 ?M2446 ?M2447), id 0)
             simple apply @encode_nat_inj (cost 0, pattern 
             @Inj ?M2442 nat (@eq ?M2442) (@eq nat)
               (@encode_nat ?M2442 ?M2443 ?M2444), id 0)
             simple apply @encode_inj (cost 0, pattern 
             @Inj ?M2439 positive (@eq ?M2439) (@eq positive)
               (@encode ?M2439 ?M2440 ?M2441), id 0)
             simple apply @fin_to_nat_inj (cost 0, pattern 
             @Inj (Fin.t ?M2438) nat (@eq (Fin.t ?M2438)) 
               (@eq nat) (@fin_to_nat ?M2438), id 0)
             simple apply @FS_inj (cost 0, pattern 
             @Inj (Fin.t ?M2437) (Fin.t (S ?M2437)) 
               (@eq (Fin.t ?M2437)) (@eq (Fin.t (S ?M2437))) 
               (@Fin.FS ?M2437), id 0)
             simple apply @app_Permutation_inj_l (cost 0, pattern 
             @Inj (list ?M2142) (list ?M2142) (@Permutation ?M2142)
               (@Permutation ?M2142)
               (fun l : list ?M2142 => @app ?M2142 l ?M2143), id 0)
             simple apply @cons_Permutation_inj_l (cost 0, pattern 
             @Inj ?M2140 (list ?M2140) (@eq ?M2140) 
               (@Permutation ?M2140)
               (fun x : ?M2140 => @cons ?M2140 x ?M2141), id 0)
             simple apply @app_Permutation_inj_r (cost 0, pattern 
             @Inj (list ?M2138) (list ?M2138) (@Permutation ?M2138)
               (@Permutation ?M2138) (@app ?M2138 ?M2139), id 0)
             simple apply @cons_Permutation_inj_r (cost 0, pattern 
             @Inj (list ?M2136) (list ?M2136) (@Permutation ?M2136)
               (@Permutation ?M2136) (@cons ?M2136 ?M2137), id 0)
             simple apply @Inj_instance_2 (cost 0, pattern 
             @Inj (list ?M2124) (list ?M2124) (@eq (list ?M2124))
               (@eq (list ?M2124)) (@reverse ?M2124), id 0)
             simple apply @Inj_instance_1 (cost 0, pattern 
             @Inj (list ?M2115) (list ?M2115) (@eq (list ?M2115))
               (@eq (list ?M2115))
               (fun l : list ?M2115 => @app ?M2115 l ?M2116), id 0)
             simple apply @Inj_instance_0 (cost 0, pattern 
             @Inj (list ?M2113) (list ?M2113) (@eq (list ?M2113))
               (@eq (list ?M2113)) (@app ?M2113 ?M2114), id 0)
             simple apply Qp.div_inj_l (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (fun q : Qp => Qp.div q ?M2100), id 0)
             simple apply Qp.div_inj_r (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (Qp.div ?M2099), id 0)
             exact Qp.inv_inj (cost 0, pattern @Inj Qp Qp 
                                                 (@eq Qp) 
                                                 (@eq Qp) Qp.inv, id 0)
             simple apply Qp.mul_inj_l (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (fun q : Qp => Qp.mul q ?M2098), id 0)
             simple apply Qp.mul_inj_r (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (Qp.mul ?M2097), id 0)
             simple apply Qp.add_inj_l (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (fun q : Qp => Qp.add q ?M2096), id 0)
             simple apply Qp.add_inj_r (cost 0, pattern 
             @Inj Qp Qp (@eq Qp) (@eq Qp) (Qp.add ?M2095), id 0)
             simple apply Qcplus_inj_l (cost 0, pattern 
             @Inj Qcanon.Qc Qcanon.Qc (@eq Qcanon.Qc) 
               (@eq Qcanon.Qc) (fun x : Qcanon.Qc => Qcanon.Qcplus x ?M2092), id 0)
             simple apply Qcplus_inj_r (cost 0, pattern 
             @Inj Qcanon.Qc Qcanon.Qc (@eq Qcanon.Qc) 
               (@eq Qcanon.Qc) (Qcanon.Qcplus ?M2091), id 0)
             exact Qcopp_inj (cost 0, pattern @Inj Qcanon.Qc Qcanon.Qc
                                                (@eq Qcanon.Qc)
                                                (@eq Qcanon.Qc) Qcanon.Qcopp, id 0)
             exact N2Z.inj' (cost 0, pattern @Inj N Z (@eq N) (@eq Z) Z.of_N, id 0)
             exact SuccNat2Pos.inj' (cost 0, pattern 
             @Inj nat positive (@eq nat) (@eq positive) Pos.of_succ_nat, id 0)
             exact Pos2Nat.inj' (cost 0, pattern @Inj positive nat
                                                 (@eq positive) 
                                                 (@eq nat) Pos.to_nat, id 0)
             exact N2Nat.inj' (cost 0, pattern @Inj N nat 
                                                 (@eq N) 
                                                 (@eq nat) N.to_nat, id 0)
             exact Nat2N.inj' (cost 0, pattern @Inj nat N 
                                                 (@eq nat) 
                                                 (@eq N) N.of_nat, id 0)
             exact Nat2Z.inj' (cost 0, pattern @Inj nat Z 
                                                 (@eq nat) 
                                                 (@eq Z) Z.of_nat, id 0)
             exact Z.neg_inj (cost 0, pattern @Inj positive Z 
                                                (@eq positive) 
                                                (@eq Z) Zneg, id 0)
             exact Z.pos_inj (cost 0, pattern @Inj positive Z 
                                                (@eq positive) 
                                                (@eq Z) Zpos, id 0)
             exact N.pos_inj (cost 0, pattern @Inj positive N 
                                                (@eq positive) 
                                                (@eq N) Npos, id 0)
             exact Pos.dup_inj (cost 0, pattern @Inj positive positive
                                                 (@eq positive)
                                                 (@eq positive) Pos.dup, id 0)
             exact Pos.reverse_inj (cost 0, pattern 
             @Inj positive positive (@eq positive) 
               (@eq positive) Pos.reverse, id 0)
             simple apply Pos.app_inj (cost 0, pattern 
             @Inj positive positive (@eq positive) 
               (@eq positive) (fun p0 : positive => Pos.app p0 ?M2047), id 0)
             exact Pos.xI_inj (cost 0, pattern @Inj positive positive
                                                 (@eq positive)
                                                 (@eq positive) xI, id 0)
             exact Pos.xO_inj (cost 0, pattern @Inj positive positive
                                                 (@eq positive)
                                                 (@eq positive) xO, id 0)
             exact Nat.succ_inj (cost 0, pattern @Inj nat nat 
                                                 (@eq nat) 
                                                 (@eq nat) Nat.succ, id 0)
             simple apply @Some_equiv_inj (cost 0, pattern 
             @Inj ?M1961 (option ?M1961) (@equiv ?M1961 ?M1962)
               (@equiv (option ?M1961) (@option_equiv ?M1961 ?M1962))
               (@Some ?M1961), id 0)
             simple apply @Some_inj (cost 0, pattern 
             @Inj ?M1928 (option ?M1928) (@eq ?M1928) 
               (@eq (option ?M1928)) (@Some ?M1928), id 0)
             exact decidable.Inj_instance_0 (cost 0, pattern 
             @Inj bool Prop (@eq bool) iff Is_true, id 0)
             simple apply @inr_equiv_inj (cost 0, pattern 
             @Inj ?M1489 (sum ?M1487 ?M1489) (@equiv ?M1489 ?M1490)
               (@equiv (sum ?M1487 ?M1489)
                  (@sum_equiv ?M1487 ?M1488 ?M1489 ?M1490))
               (@inr ?M1487 ?M1489), id 0)
             simple apply @inl_equiv_inj (cost 0, pattern 
             @Inj ?M1483 (sum ?M1483 ?M1485) (@equiv ?M1483 ?M1484)
               (@equiv (sum ?M1483 ?M1485)
                  (@sum_equiv ?M1483 ?M1484 ?M1485 ?M1486))
               (@inl ?M1483 ?M1485), id 0)
             simple apply @inr_inj' (cost 0, pattern 
             @Inj ?M1469 (sum ?M1467 ?M1469) ?M1470
               (@sum_relation ?M1467 ?M1469 ?M1468 ?M1470)
               (@inr ?M1467 ?M1469), id 0)
             simple apply @inl_inj' (cost 0, pattern 
             @Inj ?M1463 (sum ?M1463 ?M1465) ?M1464
               (@sum_relation ?M1463 ?M1465 ?M1464 ?M1466)
               (@inl ?M1463 ?M1465), id 0)
             simple apply @inr_inj (cost 0, pattern 
             @Inj ?M1422 (sum ?M1421 ?M1422) (@eq ?M1422)
               (@eq (sum ?M1421 ?M1422)) (@inr ?M1421 ?M1422), id 0)
             simple apply @inl_inj (cost 0, pattern 
             @Inj ?M1419 (sum ?M1419 ?M1420) (@eq ?M1419)
               (@eq (sum ?M1419 ?M1420)) (@inl ?M1419 ?M1420), id 0)
             simple apply @prod_swap_inj (cost 0, pattern 
             @Inj (prod ?M1233 ?M1234) (prod ?M1234 ?M1233)
               (@eq (prod ?M1233 ?M1234)) (@eq (prod ?M1234 ?M1233))
               (@prod_swap ?M1233 ?M1234), id 0)
             simple apply @id_inj (cost 0, pattern 
             @Inj ?M1179 ?M1179 (@eq ?M1179) (@eq ?M1179) 
               (@id ?M1179), id 0)
             simple apply @gmultiset_map_inj (cost 1, pattern 
             @Inj (@gmultiset ?M5601 ?M5602 ?M5603)
               (@gmultiset ?M5604 ?M5605 ?M5606)
               (@eq (@gmultiset ?M5601 ?M5602 ?M5603))
               (@eq (@gmultiset ?M5604 ?M5605 ?M5606))
               (@gmultiset_map ?M5601 ?M5602 ?M5603 
                  ?M5604 ?M5605 ?M5606 ?M5607), id 0)
             simple apply @list_fmap_equiv_inj (cost 1, pattern 
             @Inj (list ?M2312) (list ?M2313)
               (@equiv (list ?M2312) (@list_equiv ?M2312 ?M2315))
               (@equiv (list ?M2313) (@list_equiv ?M2313 ?M2316))
               (@fmap list list_fmap ?M2312 ?M2313 ?M2314), id 0)
             simple apply @list_fmap_eq_inj (cost 1, pattern 
             @Inj (list ?M2308) (list ?M2309) (@eq (list ?M2308))
               (@eq (list ?M2309))
               (@fmap list list_fmap ?M2308 ?M2309 ?M2310), id 0)
             simple apply @option_fmap_equiv_inj (cost 1, pattern 
             @Inj (option ?M1979) (option ?M1981)
               (@equiv (option ?M1979) (@option_equiv ?M1979 ?M1980))
               (@equiv (option ?M1981) (@option_equiv ?M1981 ?M1982))
               (@fmap option option_fmap ?M1979 ?M1981 ?M1983), id 0)
             simple apply @option_fmap_eq_inj (cost 1, pattern 
             @Inj (option ?M1975) (option ?M1976) 
               (@eq (option ?M1975)) (@eq (option ?M1976))
               (@fmap option option_fmap ?M1975 ?M1976 ?M1977), id 0)
             simple apply @existT_inj_2 (cost 1, pattern 
             @Inj (?M1878 ?M1879) (@sigT ?M1877 ?M1878) 
               (@eq (?M1878 ?M1879)) (@eq (@sigT ?M1877 ?M1878))
               (@existT ?M1877 ?M1878 ?M1879), id 0)
             simple apply @proj1_sig_inj (cost 1, pattern 
             @Inj (@sig ?M1874 ?M1875) ?M1874 (@eq (@sig ?M1874 ?M1875))
               (@eq ?M1874) (@proj1_sig ?M1874 ?M1875), id 0)
             simple apply @sig_map_inj (cost 2, pattern 
             @Inj (@sig ?M1492 ?M1493) (@sig ?M1494 ?M1495)
               (@eq (@sig ?M1492 ?M1493)) (@eq (@sig ?M1494 ?M1495))
               (@sig_map ?M1492 ?M1493 ?M1494 ?M1495 ?M1496 ?M1497), id 0)
             simple apply @sum_map_inj (cost 2, pattern 
             @Inj (sum ?M1423 ?M1425) (sum ?M1424 ?M1426)
               (@eq (sum ?M1423 ?M1425)) (@eq (sum ?M1424 ?M1426))
               (@sum_map ?M1423 ?M1424 ?M1425 ?M1426 ?M1427 ?M1428), id 0)
             simple apply @prod_map_inj (cost 2, pattern 
             @Inj (prod ?M1223 ?M1225) (prod ?M1224 ?M1226)
               (@eq (prod ?M1223 ?M1225)) (@eq (prod ?M1224 ?M1226))
               (@prod_map ?M1223 ?M1224 ?M1225 ?M1226 ?M1227 ?M1228), id 0)
             simple eapply @inj2_inj_2 (cost 2, pattern 
             @Inj ?M1160 ?M1161 ?M1163 ?M1164 (?M1165 ?M1167), id 0)
             simple eapply @inj2_inj_1 (cost 2, pattern 
             @Inj ?M1150 ?M1152 ?M1153 ?M1155
               (fun x : ?M1150 => ?M1156 x ?M1158), id 0)
             simple eapply @singleton_equiv_inj (cost 3, pattern 
             @Inj ?M2962 ?M2963 (@eq ?M2962)
               (@equiv ?M2963 (@set_equiv_instance ?M2962 ?M2963 ?M2964))
               (@singleton ?M2962 ?M2963 ?M2966), id 0)
             simple eapply @compose_inj (cost 3, pattern 
             @Inj ?M1180 ?M1182 ?M1183 ?M1185
               (@compose ?M1180 ?M1181 ?M1182 ?M1187 ?M1186), id 0)
             simple eapply @singleton_inj (cost 5, pattern 
             @Inj ?M2969 ?M2970 (@eq ?M2969) (@eq ?M2970)
               (@singleton ?M2969 ?M2970 ?M2973), id 0)
             simple eapply @map_seqZ_inj (cost 7, pattern 
             @Inj (list ?M4493) (?M4483 ?M4493) (@eq (list ?M4493))
               (@eq (?M4483 ?M4493))
               (@map_seqZ ?M4493 (?M4483 ?M4493)
                  (@map_insert Z ?M4493 (?M4483 ?M4493) (?M4487 ?M4493))
                  (?M4486 ?M4493) ?M4494), id 0)
             simple eapply @map_seq_inj (cost 7, pattern 
             @Inj (list ?M4468) (?M4458 ?M4468) (@eq (list ?M4468))
               (@eq (?M4458 ?M4468))
               (@map_seq ?M4468 (?M4458 ?M4468)
                  (@map_insert nat ?M4468 (?M4458 ?M4468) (?M4462 ?M4468))
                  (?M4461 ?M4468) ?M4469), id 0)
             simple eapply @map_fmap_equiv_inj (cost 8, pattern 
             @Inj (?M4429 ?M4439) (?M4429 ?M4441)
               (@equiv (?M4429 ?M4439)
                  (@map_equiv ?M4428 ?M4429 ?M4431 ?M4439 ?M4440))
               (@equiv (?M4429 ?M4441)
                  (@map_equiv ?M4428 ?M4429 ?M4431 ?M4441 ?M4442))
               (@fmap ?M4429 ?M4430 ?M4439 ?M4441 ?M4443), id 0)
             simple eapply @map_fmap_inj (cost 10, pattern 
             @Inj (?M3786 ?M3796) (?M3786 ?M3797) 
               (@eq (?M3786 ?M3796)) (@eq (?M3786 ?M3797))
               (@fmap ?M3786 ?M3787 ?M3796 ?M3797 ?M3798), id 0)
             simple eapply @kmap_inj (cost 16, pattern 
             @Inj (?M4496 ?M4519) (?M4507 ?M4519) 
               (@eq (?M4496 ?M4519)) (@eq (?M4507 ?M4519))
               (@kmap ?M4506 ?M4507
                  (fun elpi_ctx_entry_1_ : Type =>
                   @map_insert ?M4506 elpi_ctx_entry_1_
                     (?M4507 elpi_ctx_entry_1_) (?M4511 elpi_ctx_entry_1_))
                  ?M4510 ?M4495 ?M4496 ?M4503 ?M4519 
                  ?M4517), id 0)
For Inj2 ->   simple apply @ndot_inj (cost 0, pattern 
              @Inj2 namespace ?M5674 namespace (@eq namespace) 
                (@eq ?M5674) (@eq namespace) (@ndot ?M5674 ?M5675 ?M5676), id 0)
              simple apply @cons_equiv_inj (cost 0, pattern 
              @Inj2 ?M2294 (list ?M2294) (list ?M2294) 
                (@equiv ?M2294 ?M2295)
                (@equiv (list ?M2294) (@list_equiv ?M2294 ?M2295))
                (@equiv (list ?M2294) (@list_equiv ?M2294 ?M2295))
                (@cons ?M2294), id 0)
              simple apply @cons_eq_inj (cost 0, pattern 
              @Inj2 ?M2112 (list ?M2112) (list ?M2112) 
                (@eq ?M2112) (@eq (list ?M2112)) (@eq (list ?M2112))
                (@cons ?M2112), id 0)
              simple apply @pair_equiv_inj (cost 0, pattern 
              @Inj2 ?M1343 ?M1345 (prod ?M1343 ?M1345) 
                (@equiv ?M1343 ?M1344) (@equiv ?M1345 ?M1346)
                (@equiv (prod ?M1343 ?M1345)
                   (@prod_equiv ?M1343 ?M1344 ?M1345 ?M1346))
                (@pair ?M1343 ?M1345), id 0)
              simple apply @pair_inj' (cost 0, pattern 
              @Inj2 ?M1265 ?M1267 (prod ?M1265 ?M1267) 
                ?M1266 ?M1268 (@prod_relation ?M1265 ?M1267 ?M1266 ?M1268)
                (@pair ?M1265 ?M1267), id 0)
              simple apply @pair_inj (cost 0, pattern 
              @Inj2 ?M1221 ?M1222 (prod ?M1221 ?M1222) 
                (@eq ?M1221) (@eq ?M1222) (@eq (prod ?M1221 ?M1222))
                (@pair ?M1221 ?M1222), id 0)
              simple eapply @map_singleton_equiv_inj (cost 6, pattern 
              @Inj2 ?M4415 ?M4426 (?M4416 ?M4426) 
                (@eq ?M4415) (@equiv ?M4426 ?M4427)
                (@equiv (?M4416 ?M4426)
                   (@map_equiv ?M4415 ?M4416 ?M4418 ?M4426 ?M4427))
                (@singletonM ?M4415 ?M4426 (?M4416 ?M4426)
                   (@map_singleton ?M4415 ?M4426 (?M4416 ?M4426)
                      (?M4420 ?M4426) (?M4419 ?M4426))), id 0)
              simple eapply @map_singleton_inj (cost 7, pattern 
              @Inj2 ?M3773 ?M3784 (?M3774 ?M3784) 
                (@eq ?M3773) (@eq ?M3784) (@eq (?M3774 ?M3784))
                (@singletonM ?M3773 ?M3784 (?M3774 ?M3784)
                   (@map_singleton ?M3773 ?M3784 (?M3774 ?M3784)
                      (?M3778 ?M3784) (?M3777 ?M3784))), id 0)
For ZifyClasses.InjTyp ->   exact ZifyInst.Inj_N_Z (cost 0, pattern 
                            ZifyClasses.InjTyp N Z, id 0)
                            exact ZifyInst.Inj_pos_Z (cost 0, pattern 
                            ZifyClasses.InjTyp positive Z, id 0)
                            exact ZifyInst.Inj_nat_Z (cost 0, pattern 
                            ZifyClasses.InjTyp nat Z, id 0)
                            exact ZifyInst.Inj_Z_Z (cost 0, pattern 
                            ZifyClasses.InjTyp Z Z, id 0)
For Insert (modes - -
!) ->   simple apply @list_insert (cost 0, pattern 
        Insert nat ?M2106 (list ?M2106), id 0)
        simple apply @fn_insert (cost 1, pattern Insert 
                                                 ?M5294 
                                                 ?M5295
                                                 (forall _ : ?M5294, ?M5295), id 0)
        simple apply @map_insert (cost 1, pattern 
        Insert ?M3696 ?M3697 ?M3698, id 0)
For Intersection (modes !) ->   simple apply @propset_intersection (cost 0, pattern 
                                Intersection (propset ?M5831), id 0)
                                simple apply @gmultiset_intersection (cost 0, pattern 
                                Intersection
                                  (@gmultiset ?M5330 ?M5331 ?M5332), id 0)
                                simple apply @coGset_intersection (cost 0, pattern 
                                Intersection (@coGset ?M5258 ?M5259 ?M5260), id 0)
                                exact coPset_intersection (cost 0, pattern 
                                Intersection coPset, id 0)
                                simple apply @gset_intersection (cost 0, pattern 
                                Intersection (@gset ?M5161 ?M5162 ?M5163), id 0)
                                simple apply @boolset_intersection (cost 0, pattern 
                                Intersection (boolset ?M4647), id 0)
                                simple apply @option_intersection (cost 0, pattern 
                                Intersection (option ?M2013), id 0)
                                simple apply @listset_nodup_intersection (cost 1, pattern 
                                Intersection (listset_nodup ?M5667), id 0)
                                simple apply @hashset_intersection (cost 1, pattern 
                                Intersection (@hashset ?M5651 ?M5653), id 0)
                                simple apply @mapset_intersection (cost 1, pattern 
                                Intersection (mapset' (?M5011 unit)), id 0)
                                simple apply @listset_intersection (cost 1, pattern 
                                Intersection (listset ?M4595), id 0)
                                simple apply @map_intersection (cost 1, pattern 
                                Intersection (?M3738 ?M3740), id 0)
For IntersectionWith (modes -
!) ->   simple apply @option_intersection_with (cost 0, pattern 
        IntersectionWith ?M2008 (option ?M2008), id 0)
        simple apply @map_intersection_with (cost 1, pattern 
        IntersectionWith ?M3722 (?M3720 ?M3722), id 0)
For CRelationClasses.Irreflexive ->   simple apply @CRelationClasses.StrictOrder_Irreflexive (cost 1, pattern 
                                      @CRelationClasses.Irreflexive 
                                        ?M388 ?M389, id 0)
                                      (*external*) (
                                      class_apply
                                       @CRelationClasses.flip_Irreflexive) (cost 3, pattern 
                                      @CRelationClasses.Irreflexive _
                                        (@CRelationClasses.flip _ _ _ _), id 0)
                                      (*external*) (
                                      class_apply
                                       @CRelationClasses.complement_Irreflexive) (cost 3, pattern 
                                      @CRelationClasses.Irreflexive _
                                        (@CRelationClasses.complement _ _), id 0)
For Irreflexive ->   simple apply @Irreflexive_instance_0 (cost 0, pattern 
                     @Irreflexive ?M2487 (@strict ?M2487 ?M2488), id 0)
                     simple apply @StrictOrder_Irreflexive (cost 1, pattern 
                     @Irreflexive ?M224 ?M225, id 0)
                     (*external*) (class_apply @flip_Irreflexive) (cost 3, pattern 
                     @Irreflexive _ (@flip _ _ _ _), id 0)
                     (*external*) (class_apply @complement_Irreflexive) (cost 3, pattern 
                     @Irreflexive _ (@complement _ _), id 0)
For Join (modes !) ->   
For LeftAbsorb ->   simple apply @gmultiset_intersection_left_absorb (cost 0, pattern 
                    @LeftAbsorb (@gmultiset ?M5556 ?M5557 ?M5558)
                      (@eq (@gmultiset ?M5556 ?M5557 ?M5558))
                      (@empty (@gmultiset ?M5556 ?M5557 ?M5558)
                         (@gmultiset_empty ?M5556 ?M5557 ?M5558))
                      (@intersection (@gmultiset ?M5556 ?M5557 ?M5558)
                         (@gmultiset_intersection ?M5556 ?M5557 ?M5558)), id 0)
                    exact Qcmult_left_absorb (cost 0, pattern 
                    @LeftAbsorb Qcanon.Qc (@eq Qcanon.Qc)
                      (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)) Qcanon.Qcmult, id 0)
                    exact Z.mul_left_absorb (cost 0, pattern 
                    @LeftAbsorb Z (@eq Z) Z0 Z.mul, id 0)
                    exact N.mul_left_absorb (cost 0, pattern 
                    @LeftAbsorb N (@eq N) N0 N.mul, id 0)
                    exact Nat.mul_left_absorb (cost 0, pattern 
                    @LeftAbsorb nat (@eq nat) O Nat.mul, id 0)
                    simple apply @intersection_with_left_ab (cost 0, pattern 
                    @LeftAbsorb (option ?M2023) (@eq (option ?M2023))
                      (@None ?M2023)
                      (@intersection_with ?M2023 (option ?M2023)
                         (@option_intersection_with ?M2023) 
                         ?M2024), id 0)
                    simple apply @option_intersection_left_absorb (cost 0, pattern 
                    @LeftAbsorb (option ?M2015) (@eq (option ?M2015))
                      (@None ?M2015)
                      (@intersection (option ?M2015)
                         (@option_intersection ?M2015)), id 0)
                    exact True_or (cost 0, pattern 
                    @LeftAbsorb Prop iff True or, id 0)
                    exact False_and (cost 0, pattern 
                    @LeftAbsorb Prop iff False and, id 0)
                    simple eapply @intersection_empty_l (cost 4, pattern 
                    @LeftAbsorb ?M3125
                      (@equiv ?M3125
                         (@set_equiv_instance ?M3124 ?M3125 ?M3126))
                      (@empty ?M3125 ?M3127) (@intersection ?M3125 ?M3130), id 0)
                    simple eapply @intersection_empty_l_L (cost 7, pattern 
                    @LeftAbsorb ?M3173 (@eq ?M3173) 
                      (@empty ?M3173 ?M3175) (@intersection ?M3173 ?M3178), id 0)
                    simple eapply @map_empty_intersection (cost 8, pattern 
                    @LeftAbsorb (?M4091 ?M4101) (@eq (?M4091 ?M4101))
                      (@empty (?M4091 ?M4101) (?M4094 ?M4101))
                      (@intersection (?M4091 ?M4101)
                         (@map_intersection ?M4091 ?M4097 ?M4101)), id 0)
                    simple eapply @LeftAbsorb_instance_1 (cost 8, pattern 
                    @LeftAbsorb (?M4051 ?M4061) (@eq (?M4051 ?M4061))
                      (@empty (?M4051 ?M4061) (?M4054 ?M4061))
                      (@intersection_with ?M4061 (?M4051 ?M4061)
                         (@map_intersection_with ?M4051 ?M4057 ?M4061) 
                         ?M4062), id 0)
                    simple eapply @LeftAbsorb_instance_0 (cost 9, pattern 
                    @LeftAbsorb (?M3872 ?M3882) (@eq (?M3872 ?M3882))
                      (@empty (?M3872 ?M3882) (?M3875 ?M3882))
                      (@merge ?M3872 ?M3878 ?M3882 ?M3882 ?M3882 ?M3883), id 0)
For LeftId ->   simple apply @gmultiset_disj_union_left_id (cost 0, pattern 
                @LeftId (@gmultiset ?M5571 ?M5572 ?M5573)
                  (@eq (@gmultiset ?M5571 ?M5572 ?M5573))
                  (@empty (@gmultiset ?M5571 ?M5572 ?M5573)
                     (@gmultiset_empty ?M5571 ?M5572 ?M5573))
                  (@disj_union (@gmultiset ?M5571 ?M5572 ?M5573)
                     (@gmultiset_disj_union ?M5571 ?M5572 ?M5573)), id 0)
                simple apply @gmultiset_union_left_id (cost 0, pattern 
                @LeftId (@gmultiset ?M5541 ?M5542 ?M5543)
                  (@eq (@gmultiset ?M5541 ?M5542 ?M5543))
                  (@empty (@gmultiset ?M5541 ?M5542 ?M5543)
                     (@gmultiset_empty ?M5541 ?M5542 ?M5543))
                  (@union (@gmultiset ?M5541 ?M5542 ?M5543)
                     (@gmultiset_union ?M5541 ?M5542 ?M5543)), id 0)
                simple apply @list.LeftId_instance_0 (cost 0, pattern 
                @LeftId (list ?M2118) (@eq (list ?M2118)) 
                  (@nil ?M2118) (@app ?M2118), id 0)
                exact Qp.mul_left_id (cost 0, pattern 
                @LeftId Qp (@eq Qp) (pos_to_Qp xH) Qp.mul, id 0)
                exact Qcmult_left_id (cost 0, pattern 
                @LeftId Qcanon.Qc (@eq Qcanon.Qc)
                  (Qcanon.Q2Qc (QArith_base.Qmake (Zpos xH) xH))
                  Qcanon.Qcmult, id 0)
                exact Qcplus_left_id (cost 0, pattern 
                @LeftId Qcanon.Qc (@eq Qcanon.Qc)
                  (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)) Qcanon.Qcplus, id 0)
                exact Z.mul_left_id (cost 0, pattern 
                @LeftId Z (@eq Z) (Zpos xH) Z.mul, id 0)
                exact Z.add_left_id (cost 0, pattern 
                @LeftId Z (@eq Z) Z0 Z.add, id 0)
                exact N.mul_left_id (cost 0, pattern 
                @LeftId N (@eq N) (Npos xH) N.mul, id 0)
                exact N.add_left_id (cost 0, pattern 
                @LeftId N (@eq N) N0 N.add, id 0)
                exact Pos.app_1_l (cost 0, pattern 
                @LeftId positive (@eq positive) xH Pos.app, id 0)
                exact Pos.mul_left_id (cost 0, pattern 
                @LeftId positive (@eq positive) xH Pos.mul, id 0)
                exact Nat.mul_left_id (cost 0, pattern 
                @LeftId nat (@eq nat) (S O) Nat.mul, id 0)
                exact Nat.add_left_id (cost 0, pattern 
                @LeftId nat (@eq nat) O Nat.add, id 0)
                simple apply @union_with_left_id (cost 0, pattern 
                @LeftId (option ?M2016) (@eq (option ?M2016)) 
                  (@None ?M2016)
                  (@union_with ?M2016 (option ?M2016)
                     (@option_union_with ?M2016) ?M2017), id 0)
                simple apply @option_union_left_id (cost 0, pattern 
                @LeftId (option ?M2011) (@eq (option ?M2011)) 
                  (@None ?M2011)
                  (@union (option ?M2011) (@option_union ?M2011)), id 0)
                exact True_impl (cost 0, pattern @LeftId Prop iff True impl, id 0)
                exact False_or (cost 0, pattern @LeftId Prop iff False or, id 0)
                exact True_and (cost 0, pattern @LeftId Prop iff True and, id 0)
                simple eapply @union_empty_l (cost 2, pattern 
                @LeftId ?M2999
                  (@equiv ?M2999 (@set_equiv_instance ?M2998 ?M2999 ?M3000))
                  (@empty ?M2999 ?M3001) (@union ?M2999 ?M3003), id 0)
                simple eapply @union_empty_l_L (cost 5, pattern 
                @LeftId ?M3057 (@eq ?M3057) (@empty ?M3057 ?M3059)
                  (@union ?M3057 ?M3061), id 0)
                simple eapply @map_empty_union (cost 8, pattern 
                @LeftId (?M3999 ?M4009) (@eq (?M3999 ?M4009))
                  (@empty (?M3999 ?M4009) (?M4002 ?M4009))
                  (@union (?M3999 ?M4009) (@map_union ?M3999 ?M4005 ?M4009)), id 0)
                simple eapply @LeftId_instance_1 (cost 8, pattern 
                @LeftId (?M3959 ?M3969) (@eq (?M3959 ?M3969))
                  (@empty (?M3959 ?M3969) (?M3962 ?M3969))
                  (@union_with ?M3969 (?M3959 ?M3969)
                     (@map_union_with ?M3959 ?M3965 ?M3969) 
                     ?M3970), id 0)
                simple eapply @LeftId_instance_0 (cost 9, pattern 
                @LeftId (?M3844 ?M3854) (@eq (?M3844 ?M3854))
                  (@empty (?M3844 ?M3854) (?M3847 ?M3854))
                  (@merge ?M3844 ?M3850 ?M3854 ?M3854 ?M3854 ?M3855), id 0)
For LeibnizEquiv (modes !
!) ->   simple apply @gmultiset_leibniz (cost 0, pattern 
        @LeibnizEquiv (@gmultiset ?M5348 ?M5349 ?M5350)
          (@gmultiset_equiv ?M5348 ?M5349 ?M5350), id 0)
        exact coPset_leibniz (cost 0, pattern @LeibnizEquiv coPset
                                                (@set_equiv_instance positive
                                                 coPset coPset_elem_of), id 0)
        simple apply @gset_leibniz (cost 0, pattern 
        @LeibnizEquiv (@gset ?M5192 ?M5193 ?M5194)
          (@set_equiv_instance ?M5192 (@gset ?M5192 ?M5193 ?M5194)
             (@gset_elem_of ?M5192 ?M5193 ?M5194)), id 0)
        exact Empty_set_leibniz (cost 0, pattern @LeibnizEquiv Empty_set
                                                 Empty_set_equiv, id 0)
        exact unit_leibniz (cost 0, pattern @LeibnizEquiv unit unit_equiv, id 0)
        simple apply @topGset_leibniz (cost 1, pattern 
        @LeibnizEquiv (@topGset ?M5927 ?M5928 ?M5929)
          (@set_equiv_instance ?M5927 (@topGset ?M5927 ?M5928 ?M5929)
             (@topGset_elem_of ?M5927 ?M5928 ?M5929)), id 0)
        simple apply @coGset_leibniz (cost 1, pattern 
        @LeibnizEquiv (@coGset ?M5273 ?M5274 ?M5275)
          (@set_equiv_instance ?M5273 (@coGset ?M5273 ?M5274 ?M5275)
             (@coGset_elem_of ?M5273 ?M5274 ?M5275)), id 0)
        simple apply @list_leibniz (cost 1, pattern 
        @LeibnizEquiv (list ?M2244) (@list_equiv ?M2244 ?M2245), id 0)
        simple apply @option_leibniz (cost 1, pattern 
        @LeibnizEquiv (option ?M1956) (@option_equiv ?M1956 ?M1957), id 0)
        simple apply @prod_leibniz (cost 2, pattern 
        @LeibnizEquiv (prod ?M1407 ?M1410)
          (@prod_equiv ?M1407 ?M1408 ?M1410 ?M1411), id 0)
        simple eapply @mapset_leibniz (cost 8, pattern 
        @LeibnizEquiv (mapset' (?M5019 unit))
          (@set_equiv_instance ?M5018 (mapset' (?M5019 unit))
             (@mapset_elem_of ?M5018 ?M5019 ?M5021)), id 0)
        simple eapply @map_leibniz (cost 9, pattern 
        @LeibnizEquiv (?M4157 ?M4167)
          (@map_equiv ?M4156 ?M4157 ?M4159 ?M4167 ?M4168), id 0)
For Lexico (modes !) ->   exact Z_lexico (cost 0, pattern 
                          Lexico Z, id 0)
                          exact N_lexico (cost 0, pattern 
                          Lexico N, id 0)
                          exact nat_lexico (cost 0, pattern 
                          Lexico nat, id 0)
                          exact bool_lexico (cost 0, pattern 
                          Lexico bool, id 0)
                          simple apply @list_lexico (cost 1, pattern 
                          Lexico (list ?M4607), id 0)
                          simple apply @sig_lexico (cost 2, pattern 
                          Lexico (@sig ?M4609 ?M4611), id 0)
                          simple apply @prod_lexico (cost 2, pattern 
                          Lexico (prod ?M4603 ?M4605), id 0)
For Lookup (modes - -
!) ->   simple apply @Nmap_lookup (cost 0, pattern 
        Lookup N ?M5822 (Nmap ?M5822), id 0)
        simple apply @natmap_lookup (cost 0, pattern 
        Lookup nat ?M5815 (natmap ?M5815), id 0)
        simple apply @Zmap_lookup (cost 0, pattern 
        Lookup Z ?M5638 (Zmap ?M5638), id 0)
        simple apply @gmap_lookup (cost 0, pattern 
        Lookup ?M5115 ?M5118 (@gmap ?M5115 ?M5116 ?M5117 ?M5118), id 0)
        simple apply @Pmap_lookup (cost 0, pattern 
        Lookup positive ?M5090 (Pmap ?M5090), id 0)
        simple apply @Pmap_ne_lookup (cost 0, pattern 
        Lookup positive ?M5089 (Pmap_ne ?M5089), id 0)
        simple apply @list_lookup (cost 0, pattern 
        Lookup nat ?M2102 (list ?M2102), id 0)
For LookupTotal (modes - -
!) ->   simple apply vector_lookup_total (cost 0, pattern 
        LookupTotal (Fin.t ?M2507) ?M2506 (Vector.t ?M2506 ?M2507), id 0)
        simple apply @list_lookup_total (cost 1, pattern 
        LookupTotal nat ?M2103 (list ?M2103), id 0)
        simple apply @map_lookup_total (cost 20, pattern 
        LookupTotal ?M3750 ?M3751 (?M3752 ?M3751), id 0)
For MBind (modes !) ->   exact propset_bind (cost 0, pattern 
                         MBind propset, id 0)
                         exact listset_bind (cost 0, pattern 
                         MBind listset, id 0)
                         exact list_bind (cost 0, pattern 
                         MBind list, id 0)
                         exact option_bind (cost 0, pattern 
                         MBind option, id 0)
For MJoin (modes !) ->   exact propset_join (cost 0, pattern 
                         MJoin propset, id 0)
                         exact listset_join (cost 0, pattern 
                         MJoin listset, id 0)
                         exact list_join (cost 0, pattern 
                         MJoin list, id 0)
                         exact option_join (cost 0, pattern 
                         MJoin option, id 0)
For MRet (modes !) ->   exact propset_ret (cost 0, pattern 
                        MRet propset, id 0)
                        exact listset_ret (cost 0, pattern 
                        MRet listset, id 0)
                        exact list_ret (cost 0, pattern 
                        MRet list, id 0)
                        exact option_ret (cost 0, pattern 
                        MRet option, id 0)
For MThrow (modes !
!) ->   exact option_mfail (cost 0, pattern MThrow unit option, id 0)
        simple eapply @set_mfail (cost 9, pattern 
        MThrow unit ?M3237, id 0)
For nat_cancel.MakeNatAdd ->   simple apply nat_cancel.make_nat_add_0_r (cost 0, pattern 
                               nat_cancel.MakeNatAdd 
                                 ?M5757 O ?M5757, id 0)
                               simple apply nat_cancel.make_nat_add_0_l (cost 0, pattern 
                               nat_cancel.MakeNatAdd O 
                                 ?M5756 ?M5756, id 0)
                               simple apply nat_cancel.make_nat_add_default (cost 100, pattern 
                               nat_cancel.MakeNatAdd 
                                 ?M5758 ?M5759 (Init.Nat.add ?M5758 ?M5759), id 0)
For nat_cancel.MakeNatS ->   simple apply nat_cancel.make_nat_S_1 (cost 0, pattern 
                             nat_cancel.MakeNatS (S O) 
                               ?M5755 (S ?M5755), id 0)
                             simple apply nat_cancel.make_nat_S_0_l (cost 0, pattern 
                             nat_cancel.MakeNatS O 
                               ?M5754 ?M5754, id 0)
For MapFold (modes ! - -, - -
!) ->   simple apply @Nmap_fold (cost 0, pattern MapFold N 
                                                 ?M5824 
                                                 (Nmap ?M5824), id 0)
        simple apply @natmap_fold (cost 0, pattern 
        MapFold nat ?M5817 (natmap ?M5817), id 0)
        simple apply @Zmap_fold (cost 0, pattern MapFold Z 
                                                 ?M5640 
                                                 (Zmap ?M5640), id 0)
        simple apply @gmap_fold (cost 0, pattern MapFold 
                                                 ?M5136 
                                                 ?M5139
                                                 (@gmap 
                                                 ?M5136 
                                                 ?M5137 
                                                 ?M5138 
                                                 ?M5139), id 0)
        simple apply @Pmap_fold (cost 0, pattern MapFold positive 
                                                 ?M5093 
                                                 (Pmap ?M5093), id 0)
For Maybe ->   simple apply @maybe_list_singleton (cost 0, pattern 
               @Maybe ?M2108 (list ?M2108)
                 (fun x : ?M2108 => @cons ?M2108 x (@nil ?M2108)), id 0)
               exact Pos.maybe_xI (cost 0, pattern 
               @Maybe positive positive xI, id 0)
               exact Pos.maybe_xO (cost 0, pattern 
               @Maybe positive positive xO, id 0)
               simple apply @maybe_Some (cost 0, pattern 
               @Maybe ?M2006 (option ?M2006) (@Some ?M2006), id 0)
               simple apply @maybe_inr (cost 0, pattern 
               @Maybe ?M2005 (sum ?M2004 ?M2005) (@inr ?M2004 ?M2005), id 0)
               simple apply @maybe_inl (cost 0, pattern 
               @Maybe ?M2002 (sum ?M2002 ?M2003) (@inl ?M2002 ?M2003), id 0)
               simple apply @maybe_comp (cost 2, pattern 
               @Maybe ?M1999 ?M1996
                 (@compose ?M1999 ?M1995 ?M1996 ?M1997 ?M2000), id 0)
For Maybe2 ->   simple apply @maybe_cons (cost 0, pattern 
                @Maybe2 ?M2101 (list ?M2101) (list ?M2101) 
                  (@cons ?M2101), id 0)
For Meet (modes !) ->   
For Merge (modes !) ->   exact Nmap_merge (cost 0, pattern 
                         Merge Nmap, id 0)
                         exact natmap_merge (cost 0, pattern 
                         Merge natmap, id 0)
                         exact Zmap_merge (cost 0, pattern 
                         Merge Zmap, id 0)
                         simple apply @gmap_merge (cost 0, pattern 
                         Merge (@gmap ?M5133 ?M5134 ?M5135), id 0)
                         exact Pmap_merge (cost 0, pattern 
                         Merge Pmap, id 0)
For MonadSet ->   exact propset_monad_set (cost 0, pattern 
                  @MonadSet propset (@propset_elem_of) 
                    (@propset_empty) (@propset_singleton) 
                    (@propset_union) propset_bind propset_ret propset_fmap
                    propset_join, id 0)
                  exact listset_set_monad (cost 0, pattern 
                  @MonadSet listset (@listset_elem_of) 
                    (@listset_empty) (@listset_singleton) 
                    (@listset_union) listset_bind listset_ret listset_fmap
                    listset_join, id 0) *)

Set Printing All. 
Elpi Print TC.Solver "stdpp/aa".
multiset_unfold_singleton
(*
For MultisetUnfold (modes + + + - + -) ->   simple apply @multiset_unfold_singleton (cost 0, pattern 
        @MultisetUnfold ?M5378 ?M5379 ?M5380 ?M5381
          (@singletonMS ?M5378 (@gmultiset ?M5378 ?M5379 ?M5380)
             (@gmultiset_singleton ?M5378 ?M5379 ?M5380) 
             ?M5381)
          (S O), id 0)
        simple apply @multiset_unfold_empty (cost 0, pattern 
        @MultisetUnfold ?M5374 ?M5375 ?M5376 ?M5377
          (@empty (@gmultiset ?M5374 ?M5375 ?M5376)
             (@gmultiset_empty ?M5374 ?M5375 ?M5376))
          O, id 0)
        simple apply @multiset_unfold_filter (cost 1, pattern 
        @MultisetUnfold ?M5430 ?M5431 ?M5432 ?M5435
          (@filter ?M5430 (@gmultiset ?M5430 ?M5431 ?M5432)
             (@gmultiset_filter ?M5430 ?M5431 ?M5432) 
             ?M5433 ?M5434 ?M5436)
          match @decide (?M5433 ?M5435) (?M5434 ?M5435) return nat with
          | @left _ _ _ => ?M5437
          | @right _ _ _ => O
          end, id 0)
        simple apply @multiset_unfold_scalar_mul (cost 1, pattern 
        @MultisetUnfold ?M5422 ?M5423 ?M5424 ?M5425
          (@scalar_mul nat (@gmultiset ?M5422 ?M5423 ?M5424)
             (@gmultiset_scalar_mul ?M5422 ?M5423 ?M5424) 
             ?M5426 ?M5427)
          (Init.Nat.mul ?M5426 ?M5428), id 0)
        simple apply @multiset_unfold_map (cost 2, pattern 
        @MultisetUnfold ?M5623 ?M5624 ?M5625 (?M5626 ?M5627)
          (@gmultiset_map ?M5620 ?M5621 ?M5622 ?M5623 
             ?M5624 ?M5625 ?M5626 ?M5628)
          ?M5629, id 0)
        simple apply @multiset_unfold_difference (cost 2, pattern 
        @MultisetUnfold ?M5412 ?M5413 ?M5414 ?M5415
          (@difference (@gmultiset ?M5412 ?M5413 ?M5414)
             (@gmultiset_difference ?M5412 ?M5413 ?M5414) 
             ?M5416 ?M5417)
          (Init.Nat.sub ?M5418 ?M5419), id 0)
        simple apply @multiset_unfold_disj_union (cost 2, pattern 
        @MultisetUnfold ?M5402 ?M5403 ?M5404 ?M5405
          (@disj_union (@gmultiset ?M5402 ?M5403 ?M5404)
             (@gmultiset_disj_union ?M5402 ?M5403 ?M5404) 
             ?M5406 ?M5407)
          (Init.Nat.add ?M5408 ?M5409), id 0)
        simple apply @multiset_unfold_intersection (cost 2, pattern 
        @MultisetUnfold ?M5392 ?M5393 ?M5394 ?M5395
          (@intersection (@gmultiset ?M5392 ?M5393 ?M5394)
             (@gmultiset_intersection ?M5392 ?M5393 ?M5394) 
             ?M5396 ?M5397)
          (Nat.min ?M5398 ?M5399), id 0)
        simple apply @multiset_unfold_union (cost 2, pattern 
        @MultisetUnfold ?M5382 ?M5383 ?M5384 ?M5385
          (@union (@gmultiset ?M5382 ?M5383 ?M5384)
             (@gmultiset_union ?M5382 ?M5383 ?M5384) 
             ?M5386 ?M5387)
          (Nat.max ?M5388 ?M5389), id 0)
        simple apply @multiset_unfold_default (cost 1000, pattern 
        @MultisetUnfold ?M5369 ?M5370 ?M5371 ?M5372 
          ?M5373 (@multiplicity ?M5369 ?M5370 ?M5371 ?M5372 ?M5373), id 0)
For NatCancel (modes ! ! -
-) ->   simple apply nat_cancel.nat_cancel_start (cost 1, pattern 
        NatCancel ?M5749 ?M5750 ?M5751 ?M5752, id 0)
For nat_cancel.NatCancelL (modes ! ! -
-) ->   simple apply nat_cancel.nat_cancel_S_both (cost 1, pattern 
        nat_cancel.NatCancelL (S ?M5784) (S ?M5785) 
          ?M5786 ?M5787, id 0)
        simple eapply nat_cancel.nat_cancel_add (cost 2, pattern 
        nat_cancel.NatCancelL (Init.Nat.add ?M5789 ?M5790) 
          ?M5794 ?M5793 ?M5796, id 0)
        simple eapply nat_cancel.nat_cancel_S (cost 3, pattern 
        nat_cancel.NatCancelL (S ?M5800) ?M5804 ?M5803 
          ?M5806, id 0)
        simple apply @nat_cancel.nat_cancel_r (cost 100, pattern 
        nat_cancel.NatCancelL ?M5744 ?M5745 ?M5746 
          ?M5747, id 0)
For nat_cancel.NatCancelR (modes ! ! -
-) ->   simple apply nat_cancel.nat_cancel_leaf_here (cost 0, pattern 
        nat_cancel.NatCancelR ?M5760 ?M5760 O O, id 0)
        simple eapply nat_cancel.nat_cancel_leaf_add (cost 2, pattern 
        nat_cancel.NatCancelR ?M5763 (Init.Nat.add ?M5766 ?M5767) 
          ?M5765 ?M5770, id 0)
        simple apply nat_cancel.nat_cancel_leaf_S_here (cost 3, pattern 
        nat_cancel.NatCancelR (S ?M5774) (S ?M5775) 
          ?M5776 ?M5777, id 0)
        simple apply nat_cancel.nat_cancel_leaf_S_else (cost 4, pattern 
        nat_cancel.NatCancelR ?M5779 (S ?M5780) ?M5781 
          (S ?M5782), id 0)
        simple apply nat_cancel.nat_cancel_leaf_else (cost 100, pattern 
        nat_cancel.NatCancelR ?M5761 ?M5762 ?M5761 
          ?M5762, id 0)
For CMorphisms.Normalizes ->   (*external*) CMorphisms.normalizes (cost 1, pattern 
                               CMorphisms.Normalizes _ _ _, id 0)
For Normalizes ->   (*external*) normalizes (cost 1, pattern 
                    Normalizes _ _ _, id 0)
For OMap (modes !) ->   exact Nmap_omap (cost 0, pattern 
                        OMap Nmap, id 0)
                        exact natmap_omap (cost 0, pattern 
                        OMap natmap, id 0)
                        exact Zmap_omap (cost 0, pattern 
                        OMap Zmap, id 0)
                        simple apply @gmap_omap (cost 0, pattern 
                        OMap (@gmap ?M5130 ?M5131 ?M5132), id 0)
                        exact Pmap_omap (cost 0, pattern 
                        OMap Pmap, id 0)
                        exact list_omap (cost 0, pattern 
                        OMap list, id 0)
For CRelationClasses.PER ->   simple apply @CRelationClasses.Equivalence_PER (cost 10, pattern 
                              @CRelationClasses.PER 
                                ?M412 ?M413, id 0)
For RelationClasses.PER ->   simple apply @Equivalence_PER (cost 10, pattern 
                             @RelationClasses.PER 
                               ?M248 ?M249, id 0)
For Params ->   exact binders.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A M : Type) (_ : Insert string A M) 
                     (_ : binder) (_ : A) (_ : M),
                   M)
                  (@binder_insert) (S (S (S (S O)))), id 0)
                exact Params_instance_3 (cost 0, pattern 
                @Params
                  (forall (A C : Type) (_ : Fresh A C) 
                     (_ : Union C) (_ : Singleton A C) 
                     (_ : nat) (_ : C),
                   list A)
                  (@fresh_list) (S (S (S (S (S (S O)))))), id 0)
                exact Params_instance_2 (cost 0, pattern 
                @Params
                  (forall (A C : Type) (_ : Elements A C) 
                     (B D : Type) (_ : Singleton B D) 
                     (_ : Empty D) (_ : Union D) (_ : forall _ : A, option B)
                     (_ : C),
                   D)
                  (@set_omap) (S (S (S (S (S (S (S (S O)))))))), id 0)
                exact Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A SA : Type) (_ : Elements A SA) 
                     (SB : Type) (_ : Empty SB) (_ : Union SB)
                     (_ : forall _ : A, SB) (_ : SA),
                   SB)
                  (@set_bind) (S (S (S (S (S (S O)))))), id 0)
                exact Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A C : Type) (_ : Elements A C) 
                     (B D : Type) (_ : Singleton B D) 
                     (_ : Empty D) (_ : Union D) (_ : forall _ : A, B)
                     (_ : C),
                   D)
                  (@set_map) (S (S (S (S (S (S (S (S O)))))))), id 0)
                exact sets.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A C : Type) (_ : ElemOf A C) 
                     (_ : relation A) (_ : A) (_ : C),
                   Prop)
                  (@minimal) (S (S (S (S (S O))))), id 0)
                exact list.Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : forall _ : A, nat) (_ : list A),
                   nat)
                  (@max_list_with) (S O), id 0)
                exact list.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : forall _ : A, nat) (_ : list A),
                   nat)
                  (@sum_list_with) (S O), id 0)
                exact list_misc.list.Params_instance_4 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : list nat) (_ : list A),
                   list (list A))
                  (@reshape) (S (S O)), id 0)
                exact list_misc.list.Params_instance_3 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : nat) (_ : nat) (_ : list A), list A)
                  (@rotate_take) (S (S (S O))), id 0)
                exact list_misc.list.Params_instance_2 (cost 0, pattern 
                @Params (forall (A : Type) (_ : nat) (_ : list A), list A)
                  (@rotate) (S (S O)), id 0)
                exact list_misc.list.Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : nat) (_ : A) (_ : list A), list A)
                  (@resize) (S (S O)), id 0)
                exact list_misc.list.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A : Type) (P : forall _ : A, Prop)
                     (_ : forall x : A, Decision (P x)) 
                     (_ : list A),
                   option (prod nat A))
                  (@list_find) (S (S (S O))), id 0)
                exact list.Params_instance_3 (cost 0, pattern 
                @Params
                  (forall (A B C : Type)
                     (_ : forall (_ : nat) (_ : A) (_ : B), C) 
                     (_ : list A) (_ : list B),
                   list C)
                  (@imap2) (S (S (S O))), id 0)
                exact list.Params_instance_2 (cost 0, pattern 
                @Params
                  (forall (A B : Type)
                     (_ : forall (_ : list A) (_ : list A) (_ : A), B)
                     (_ : list A) (_ : list A),
                   list B)
                  (@zipped_map) (S (S O)), id 0)
                exact list_monad.list.Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A B : Type) (_ : forall (_ : nat) (_ : A), B)
                     (_ : list A),
                   list B)
                  (@imap) (S (S O)), id 0)
                exact list_monad.list.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : MBind M) (_ : MRet M) (A B : Type)
                     (_ : forall _ : A, M B) (_ : list A),
                   M (list B))
                  (@mapM) (S (S (S (S (S O))))), id 0)
                exact list_relations.list.Params_instance_2 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), Prop) 
                  (@NoDup) (S O), id 0)
                exact list_relations.list.Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : forall _ : A, Prop) (_ : list A),
                   Prop)
                  Exists (S O), id 0)
                exact list_relations.list.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : forall _ : A, Prop) (_ : list A),
                   Prop)
                  Forall (S O), id 0)
                exact Params_instance_11 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), option A) 
                  (@last) (S O), id 0)
                exact Params_instance_10 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), list A) 
                  (@reverse) (S O), id 0)
                exact Params_instance_9 (cost 0, pattern 
                @Params (forall (A : Type) (_ : nat) (_ : A), list A)
                  (@replicate) (S (S O)), id 0)
                exact Params_instance_8 (cost 0, pattern 
                @Params (forall (A : Type) (_ : option A), list A)
                  (@option_list) (S O), id 0)
                exact Params_instance_7 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : nat) (_ : list A) (_ : list A),
                   list A)
                  (@list_inserts) (S O), id 0)
                exact Params_instance_6 (cost 0, pattern 
                @Params (forall (A : Type) (_ : nat) (_ : list A), list A)
                  (@skipn) (S O), id 0)
                exact Params_instance_5 (cost 0, pattern 
                @Params (forall (A : Type) (_ : nat) (_ : list A), list A)
                  (@firstn) (S O), id 0)
                exact Params_instance_4 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), list A) 
                  (@tl) (S O), id 0)
                exact list_basics.list.Params_instance_3 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), option A)
                  (@hd_error) (S O), id 0)
                exact list_basics.list.Params_instance_2 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A) (_ : list A), list A)
                  (@app) (S O), id 0)
                exact list_basics.list.Params_instance_1 (cost 0, pattern 
                @Params (forall (A : Type) (_ : A) (_ : list A), list A)
                  (@cons) (S O), id 0)
                exact list_basics.list.Params_instance_0 (cost 0, pattern 
                @Params (forall (A : Type) (_ : list A), nat) 
                  (@length) (S O), id 0)
                exact option.Params_instance_1 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : forall _ : A, Prop) (_ : option A),
                   Prop)
                  (@option_Forall) (S O), id 0)
                exact option.Params_instance_0 (cost 0, pattern 
                @Params
                  (forall (A B : Type) (_ : forall _ : A, B) 
                     (_ : B) (_ : option A),
                   B)
                  (@from_option) (S (S O)), id 0)
                exact Params_instance_51 (cost 0, pattern 
                @Params (forall (A C : Type) (_ : Fresh A C) (_ : C), A)
                  (@fresh) (S (S (S O))), id 0)
                exact Params_instance_50 (cost 0, pattern 
                @Params (forall (C : Type) (_ : Size C) (_ : C), nat) 
                  (@size) (S (S O)), id 0)
                exact Params_instance_49 (cost 0, pattern 
                @Params
                  (forall (A C : Type) (_ : Elements A C) (_ : C), list A)
                  (@elements) (S (S (S O))), id 0)
                exact Params_instance_48 (cost 0, pattern 
                @Params (forall (A : Type) (_ : Join A) (_ : A) (_ : A), A)
                  (@join) (S (S O)), id 0)
                exact Params_instance_47 (cost 0, pattern 
                @Params (forall (A : Type) (_ : Meet A) (_ : A) (_ : A), A)
                  (@meet) (S (S O)), id 0)
                exact Params_instance_46 (cost 0, pattern 
                @Params (forall (A : Type) (_ : SqSubsetEq A), relation A)
                  (@sqsubseteq) (S (S O)), id 0)
                exact Params_instance_45 (cost 0, pattern 
                @Params
                  (forall (A M : Type) (_ : DifferenceWith A M)
                     (_ : forall (_ : A) (_ : A), option A) 
                     (_ : M) (_ : M),
                   M)
                  (@difference_with) (S (S (S O))), id 0)
                exact Params_instance_44 (cost 0, pattern 
                @Params
                  (forall (A M : Type) (_ : IntersectionWith A M)
                     (_ : forall (_ : A) (_ : A), option A) 
                     (_ : M) (_ : M),
                   M)
                  (@intersection_with) (S (S (S O))), id 0)
                exact Params_instance_43 (cost 0, pattern 
                @Params
                  (forall (A M : Type) (_ : UnionWith A M)
                     (_ : forall (_ : A) (_ : A), option A) 
                     (_ : M) (_ : M),
                   M)
                  (@union_with) (S (S (S O))), id 0)
                exact Params_instance_42 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : Merge M) (A B C : Type)
                     (_ : forall (_ : option A) (_ : option B), option C)
                     (_ : M A) (_ : M B),
                   M C)
                  (@merge) (S (S (S (S O)))), id 0)
                exact Params_instance_41 (cost 0, pattern 
                @Params (forall (M D : Type) (_ : Dom M D) (_ : M), D) 
                  (@dom) (S (S (S O))), id 0)
                exact Params_instance_40 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : PartialAlter K A M)
                     (_ : forall _ : option A, option A) 
                     (_ : K) (_ : M),
                   M)
                  (@partial_alter) (S (S (S (S O)))), id 0)
                exact Params_instance_39 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : Alter K A M)
                     (_ : forall _ : A, A) (_ : K) 
                     (_ : M),
                   M)
                  (@alter) (S (S (S (S O)))), id 0)
                exact Params_instance_38 (cost 0, pattern 
                @Params
                  (forall (K M : Type) (_ : Delete K M) (_ : K) (_ : M), M)
                  (@delete) (S (S (S (S O)))), id 0)
                exact Params_instance_37 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : Insert K A M) 
                     (_ : K) (_ : A) (_ : M),
                   M)
                  (@insert) (S (S (S (S (S O))))), id 0)
                exact Params_instance_36 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : SingletonM K A M) 
                     (_ : K) (_ : A),
                   M)
                  (@singletonM) (S (S (S (S (S O))))), id 0)
                exact Params_instance_35 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : LookupTotal K A M) 
                     (_ : K) (_ : M),
                   A)
                  (@lookup_total) (S (S (S (S (S O))))), id 0)
                exact Params_instance_34 (cost 0, pattern 
                @Params
                  (forall (K A M : Type) (_ : Lookup K A M) (_ : K) (_ : M),
                   option A)
                  (@lookup) (S (S (S (S (S O))))), id 0)
                exact Params_instance_33 (cost 0, pattern 
                @Params
                  (forall (E : Type) (M : forall _ : Type, Type)
                     (_ : MThrow E M) (A : Type) (_ : E),
                   M A)
                  (@mthrow) (S (S (S (S O)))), id 0)
                exact Params_instance_32 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : OMap M) (A B : Type) (_ : forall _ : A, option B)
                     (_ : M A),
                   M B)
                  (@omap) (S (S (S (S O)))), id 0)
                exact Params_instance_31 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : FMap M) (A B : Type) (_ : forall _ : A, B)
                     (_ : M A),
                   M B)
                  (@fmap) (S (S (S (S O)))), id 0)
                exact Params_instance_30 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : MJoin M) (A : Type) (_ : M (M A)),
                   M A)
                  (@mjoin) (S (S (S O))), id 0)
                exact Params_instance_29 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : MBind M) (A B : Type) (_ : forall _ : A, M B)
                     (_ : M A),
                   M B)
                  (@mbind) (S (S (S (S O)))), id 0)
                exact Params_instance_28 (cost 0, pattern 
                @Params
                  (forall (M : forall _ : Type, Type) 
                     (_ : MRet M) (A : Type) (_ : A),
                   M A)
                  (@mret) (S (S (S O))), id 0)
                exact Params_instance_27 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : Disjoint A) (_ : A) (_ : A), Prop)
                  (@disjoint) (S (S O)), id 0)
                exact Params_instance_26 (cost 0, pattern 
                @Params
                  (forall (A B : Type) (_ : ElemOf A B) (_ : A) (_ : B), Prop)
                  (@elem_of) (S (S (S O))), id 0)
                exact Params_instance_25 (cost 0, pattern 
                @Params
                  (forall (N A : Type) (_ : ScalarMul N A) (_ : N) (_ : A), A)
                  (@scalar_mul) (S (S (S O))), id 0)
                exact Params_instance_24 (cost 0, pattern 
                @Params
                  (forall (A B : Type) (_ : SingletonMS A B) (_ : A), B)
                  (@singletonMS) (S (S (S O))), id 0)
                exact Params_instance_23 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : Empty A) 
                     (_ : DisjUnion A) (_ : list A),
                   A)
                  (@disj_union_list) (S (S (S O))), id 0)
                exact Params_instance_22 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : DisjUnion A) (_ : A) (_ : A), A)
                  (@disj_union) (S (S O)), id 0)
                exact Params_instance_21 (cost 0, pattern 
                @Params (forall (A : Type) (_ : SubsetEq A), relation A)
                  (@subseteq) (S (S O)), id 0)
                exact Params_instance_20 (cost 0, pattern 
                @Params (forall (A B : Type) (_ : Singleton A B) (_ : A), B)
                  (@singleton) (S (S (S O))), id 0)
                exact Params_instance_19 (cost 0, pattern 
                @Params
                  (forall (A B C : Type) (_ : CProd A B C) (_ : A) (_ : B), C)
                  (@cprod) (S (S (S (S O)))), id 0)
                exact Params_instance_18 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : Difference A) (_ : A) (_ : A), A)
                  (@difference) (S (S O)), id 0)
                exact Params_instance_17 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : Intersection A) (_ : A) (_ : A), A)
                  (@intersection) (S (S O)), id 0)
                exact Params_instance_16 (cost 0, pattern 
                @Params
                  (forall (A : Type) (_ : Empty A) (_ : Union A) (_ : list A),
                   A)
                  (@union_list) (S (S (S O))), id 0)
                exact Params_instance_15 (cost 0, pattern 
                @Params (forall (A : Type) (_ : Union A) (_ : A) (_ : A), A)
                  (@union) (S (S O)), id 0)
                exact Params_instance_14 (cost 0, pattern 
                @Params (forall (A : Type) (_ : option A), Prop) 
                  (@is_Some) (S O), id 0)
                exact Params_instance_13 (cost 0, pattern 
                @Params (forall (A B : Type) (_ : prod A B), prod B A)
                  (@prod_swap) (S (S O)), id 0)
                exact Params_instance_12 (cost 0, pattern 
                @Params
                  (forall (A A' A'' B B' B'' : Type)
                     (_ : forall (_ : A) (_ : A'), A'')
                     (_ : forall (_ : B) (_ : B'), B'') 
                     (_ : prod A B) (_ : prod A' B'),
                   prod A'' B'')
                  (@prod_zip) (S (S (S (S (S (S O)))))), id 0)
                exact base.Params_instance_11 (cost 0, pattern 
                @Params
                  (forall (A A' B B' : Type) (_ : forall _ : A, A')
                     (_ : forall _ : B, B') (_ : prod A B),
                   prod A' B')
                  (@prod_map) (S (S (S (S O)))), id 0)
                exact base.Params_instance_10 (cost 0, pattern 
                @Params
                  (forall (A B C D E : Type)
                     (_ : forall _ : prod (prod (prod A B) C) D, E) 
                     (_ : A) (_ : B) (_ : C) (_ : D),
                   E)
                  (@curry4) (S (S (S (S (S O))))), id 0)
                exact base.Params_instance_9 (cost 0, pattern 
                @Params
                  (forall (A B C D : Type)
                     (_ : forall _ : prod (prod A B) C, D) 
                     (_ : A) (_ : B) (_ : C),
                   D)
                  (@curry3) (S (S (S (S O)))), id 0)
                exact base.Params_instance_8 (cost 0, pattern 
                @Params
                  (forall (A B C D E : Type)
                     (_ : forall (_ : A) (_ : B) (_ : C) (_ : D), E)
                     (_ : prod (prod (prod A B) C) D),
                   E)
                  (@uncurry4) (S (S (S (S (S O))))), id 0)
                exact base.Params_instance_7 (cost 0, pattern 
                @Params
                  (forall (A B C D : Type)
                     (_ : forall (_ : A) (_ : B) (_ : C), D)
                     (_ : prod (prod A B) C),
                   D)
                  (@uncurry3) (S (S (S (S O)))), id 0)
                exact base.Params_instance_6 (cost 0, pattern 
                @Params
                  (forall (A B C : Type) (_ : forall (_ : A) (_ : B), C)
                     (_ : prod A B),
                   C)
                  (@uncurry) (S (S (S O))), id 0)
                exact base.Params_instance_5 (cost 0, pattern 
                @Params
                  (forall (A B C : Type) (_ : forall _ : prod A B, C) 
                     (_ : A) (_ : B),
                   C)
                  (@curry) (S (S (S O))), id 0)
                exact base.Params_instance_4 (cost 0, pattern 
                @Params (forall (A B : Type) (_ : prod A B), B) 
                  (@snd) (S (S O)), id 0)
                exact base.Params_instance_3 (cost 0, pattern 
                @Params (forall (A B : Type) (_ : prod A B), A) 
                  (@fst) (S (S O)), id 0)
                exact base.Params_instance_2 (cost 0, pattern 
                @Params (forall (A B : Type) (_ : A) (_ : B), prod A B)
                  (@pair) (S (S O)), id 0)
                exact base.Params_instance_1 (cost 0, pattern 
                @Params (forall (A : Type) (_ : relation A), relation A)
                  (@strict) (S (S O)), id 0)
                exact base.Params_instance_0 (cost 0, pattern 
                @Params (forall (A : Type) (_ : Equiv A), relation A)
                  (@equiv) (S (S O)), id 0)
                exact flip_pars (cost 0, pattern @Params
                                                 (forall 
                                                 (A B C : Type)
                                                 (_ : 
                                                 forall (_ : A) (_ : B), C)
                                                 (_ : B) 
                                                 (_ : A), C) 
                                                 (@flip) 
                                                 (S (S (S (S O)))), id 0)
                exact impl_pars (cost 0, pattern @Params
                                                 (forall 
                                                 (_ : Prop) 
                                                 (_ : Prop), Prop) impl O, id 0)
                exact iff_pars (cost 0, pattern @Params
                                                 (forall 
                                                 (_ : Prop) 
                                                 (_ : Prop), Prop) iff O, id 0)
                exact eq_pars (cost 0, pattern @Params
                                                 (forall 
                                                 (A : Type) 
                                                 (_ : A) 
                                                 (_ : A), Prop) 
                                                 (@eq) 
                                                 (S O), id 0)
For PartialAlter (modes - -
!) ->   simple apply @Nmap_partial_alter (cost 0, pattern 
        PartialAlter N ?M5823 (Nmap ?M5823), id 0)
        simple apply @natmap_partial_alter (cost 0, pattern 
        PartialAlter nat ?M5816 (natmap ?M5816), id 0)
        simple apply @Zmap_partial_alter (cost 0, pattern 
        PartialAlter Z ?M5639 (Zmap ?M5639), id 0)
        simple apply @gmap_partial_alter (cost 0, pattern 
        PartialAlter ?M5123 ?M5126 (@gmap ?M5123 ?M5124 ?M5125 ?M5126), id 0)
        simple apply @Pmap_partial_alter (cost 0, pattern 
        PartialAlter positive ?M5092 (Pmap ?M5092), id 0)
For CRelationClasses.PartialOrder ->   (*external*) (
                                       class_apply
                                        @CRelationClasses.PartialOrder_inverse) (cost 3, pattern 
                                       @CRelationClasses.PartialOrder _
                                         (@CRelationClasses.flip _ _ _ _) _, id 0)
                                       (*external*) (
                                       class_apply
                                        @CMorphisms.StrictOrder_PartialOrder) (cost 4, pattern 
                                       @CRelationClasses.PartialOrder _ _ _
                                         (@CRelationClasses.relation_disjunction
                                            _ _ _)
                                         _, id 0)
For PartialOrder (modes !
!) ->   simple apply @gmultiset_po (cost 0, pattern 
        @PartialOrder (@gmultiset ?M5595 ?M5596 ?M5597)
          (@subseteq (@gmultiset ?M5595 ?M5596 ?M5597)
             (@gmultiset_subseteq ?M5595 ?M5596 ?M5597)), id 0)
        exact String.le_po (cost 0, pattern @PartialOrder string String.le, id 0)
        simple apply @PartialOrder_instance_2 (cost 0, pattern 
        @PartialOrder (list ?M2153) (@sublist ?M2153), id 0)
        simple apply @PartialOrder_instance_1 (cost 0, pattern 
        @PartialOrder (list ?M2148) (@suffix ?M2148), id 0)
        simple apply @PartialOrder_instance_0 (cost 0, pattern 
        @PartialOrder (list ?M2147) (@prefix ?M2147), id 0)
        exact Qp.le_po (cost 0, pattern @PartialOrder Qp Qp.le, id 0)
        exact Qc_le_po (cost 0, pattern @PartialOrder Qcanon.Qc Qcanon.Qcle, id 0)
        exact Z.le_po (cost 0, pattern @PartialOrder Z Z.le, id 0)
        exact N.le_po (cost 0, pattern @PartialOrder N N.le, id 0)
        exact Nat.divide_po (cost 0, pattern @PartialOrder nat Nat.divide, id 0)
        exact Nat.le_po (cost 0, pattern @PartialOrder nat le, id 0)
        exact base.PartialOrder_instance_0 (cost 0, pattern 
        @PartialOrder bool bool_le, id 0)
        simple apply @total_order_partial (cost 1, pattern 
        @PartialOrder ?M5960 ?M5961, id 0)
        simple eapply @set_subseteq_partialorder (cost 5, pattern 
        @PartialOrder ?M3041
          (@subseteq ?M3041 (@set_subseteq_instance ?M3040 ?M3041 ?M3042)), id 0)
        simple eapply @map_subseteq_po (cost 8, pattern 
        @PartialOrder (?M3762 ?M3772)
          (@subseteq (?M3762 ?M3772)
             (@map_subseteq ?M3761 ?M3762 ?M3764 ?M3772)), id 0)
For RelationClasses.PartialOrder ->   exact Positive_as_OT.le_partorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder positive
                                        (@eq positive)
                                        (@eq_equivalence positive)
                                        Positive_as_OT.le
                                        Positive_as_OT.le_preorder, id 0)
                                      exact Positive_as_DT.le_partorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder positive
                                        (@eq positive)
                                        (@eq_equivalence positive)
                                        Positive_as_DT.le
                                        Positive_as_DT.le_preorder, id 0)
                                      exact Z.le_partialorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder Z 
                                        (@eq Z) Z.eq_equiv Z.le Z.le_preorder, id 0)
                                      exact N.le_partialorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder N 
                                        (@eq N) N.eq_equiv N.le N.le_preorder, id 0)
                                      exact Pos.le_partorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder positive
                                        (@eq positive)
                                        (@eq_equivalence positive) Pos.le
                                        Pos.le_preorder, id 0)
                                      exact Nat.le_partialorder (cost 0, pattern 
                                      @RelationClasses.PartialOrder nat
                                        (@eq nat) Nat.eq_equiv le
                                        Nat.le_preorder, id 0)
                                      simple apply @subrelation_partial_order (cost 0, pattern 
                                      @RelationClasses.PartialOrder
                                        (relation ?M273)
                                        (@relation_equivalence ?M273)
                                        (@relation_equivalence_equivalence
                                           ?M273)
                                        (@subrelation ?M273)
                                        (@relation_implication_preorder ?M273), id 0)
                                      (*external*) (
                                      class_apply @PartialOrder_inverse) (cost 3, pattern 
                                      @RelationClasses.PartialOrder _
                                        (@flip _ _ _ _) _, id 0)
                                      (*external*) (
                                      class_apply @StrictOrder_PartialOrder) (cost 4, pattern 
                                      @RelationClasses.PartialOrder _ _ _
                                        (@relation_disjunction _ _ _) _, id 0)
For CRelationClasses.PreOrder ->   simple apply @CRelationClasses.relation_implication_preorder (cost 0, pattern 
                                   @CRelationClasses.PreOrder
                                     (CRelationClasses.crelation ?M427)
                                     (@CRelationClasses.subrelation ?M427), id 0)
                                   (*external*) (class_apply
                                                 @CRelationClasses.flip_PreOrder) (cost 3, pattern 
                                   @CRelationClasses.PreOrder _
                                     (@CRelationClasses.flip _ _ _ _), id 0)
                                   (*external*) (class_apply
                                                 @CMorphisms.StrictOrder_PreOrder) (cost 4, pattern 
                                   @CRelationClasses.PreOrder _
                                     (@CRelationClasses.relation_disjunction
                                        _ _ _), id 0)
For PreOrder (modes -
!) ->   simple apply @rtc_po (cost 0, pattern @PreOrder 
                                                ?M3383 
                                                (@rtc ?M3383 ?M3384), id 0)
        simple apply @list_subseteq_po (cost 0, pattern 
        @PreOrder (list ?M2237)
          (@subseteq (list ?M2237) (@list_subseteq ?M2237)), id 0)
        simple apply @PreOrder_instance_0 (cost 0, pattern 
        @PreOrder (list ?M2154) (@submseteq ?M2154), id 0)
        exact Positive_as_OT.le_preorder (cost 0, pattern 
        @PreOrder positive Positive_as_OT.le, id 0)
        exact Positive_as_DT.le_preorder (cost 0, pattern 
        @PreOrder positive Positive_as_DT.le, id 0)
        exact Z.le_preorder (cost 0, pattern @PreOrder Z Z.le, id 0)
        exact N.le_preorder (cost 0, pattern @PreOrder N N.le, id 0)
        exact Pos.le_preorder (cost 0, pattern @PreOrder positive Pos.le, id 0)
        simple apply base.PreOrder_instance_0 (cost 0, pattern 
        @PreOrder ?M1145 (@eq ?M1145), id 0)
        exact Nat.le_preorder (cost 0, pattern @PreOrder nat le, id 0)
        simple apply @relation_implication_preorder (cost 0, pattern 
        @PreOrder (relation ?M266) (@subrelation ?M266), id 0)
        simple apply @predicate_implication_preorder (cost 0, pattern 
        @PreOrder (arrows ?M263 Prop) (@predicate_implication ?M263), id 0)
        simple apply @partial_order_pre (cost 1, pattern 
        @PreOrder ?M5954 ?M5955, id 0)
        simple apply @map_included_preorder (cost 1, pattern 
        @PreOrder (?M3756 ?M3758)
          (@map_included ?M3755 ?M3756 ?M3757 ?M3758 ?M3758 ?M3759), id 0)
        simple apply @PreOrder_instance_1 (cost 1, pattern 
        @PreOrder (list ?M2189) (@Forall2 ?M2189 ?M2189 ?M2190), id 0)
        (*external*) (class_apply @flip_PreOrder) (cost 3, pattern 
        @PreOrder _ (@flip _ _ _ _), id 0)
        simple eapply @set_subseteq_preorder (cost 4, pattern 
        @PreOrder ?M2985
          (@subseteq ?M2985 (@set_subseteq_instance ?M2984 ?M2985 ?M2986)), id 0)
        (*external*) (class_apply @StrictOrder_PreOrder) (cost 4, pattern 
        @PreOrder _ (@relation_disjunction _ _ _), id 0)
        simple apply @Equivalence_PreOrder (cost 10, pattern 
        @PreOrder ?M251 ?M252, id 0)
For Pretty (modes !) ->   exact pretty_Z (cost 0, pattern 
                          Pretty Z, id 0)
                          exact pretty_positive (cost 0, pattern 
                          Pretty positive, id 0)
                          exact pretty_nat (cost 0, pattern 
                          Pretty nat, id 0)
                          exact pretty_N (cost 0, pattern 
                          Pretty N, id 0)
For ProofIrrel (modes !) ->   simple apply @natmap_wf_pi (cost 0, pattern 
                              ProofIrrel (@natmap_wf ?M5810 ?M5811), id 0)
                              simple apply @gmap_key_pi (cost 0, pattern 
                              ProofIrrel
                                (@gmap_key ?M5098 ?M5099 ?M5100 ?M5101), id 0)
                              simple apply String.le_pi (cost 0, pattern 
                              ProofIrrel (String.le ?M2484 ?M2485), id 0)
                              simple apply Qp.lt_pi (cost 0, pattern 
                              ProofIrrel (Qp.lt ?M2093 ?M2094), id 0)
                              simple apply Qc_lt_pi (cost 0, pattern 
                              ProofIrrel (Qcanon.Qclt ?M2089 ?M2090), id 0)
                              simple apply Z.lt_pi (cost 0, pattern 
                              ProofIrrel (Z.lt ?M2050 ?M2051), id 0)
                              simple apply N.lt_pi (cost 0, pattern 
                              ProofIrrel (N.lt ?M2048 ?M2049), id 0)
                              simple apply Nat.lt_pi (cost 0, pattern 
                              ProofIrrel (lt ?M2045 ?M2046), id 0)
                              simple apply Nat.le_pi (cost 0, pattern 
                              ProofIrrel (le ?M2043 ?M2044), id 0)
                              simple apply @is_Some_pi (cost 0, pattern 
                              ProofIrrel (@is_Some ?M1935 ?M1936), id 0)
                              simple apply Is_true_pi (cost 0, pattern 
                              ProofIrrel (Is_true ?M1873), id 0)
                              exact unit_pi (cost 0, pattern 
                              ProofIrrel unit, id 0)
                              exact False_pi (cost 0, pattern 
                              ProofIrrel False, id 0)
                              exact True_pi (cost 0, pattern 
                              ProofIrrel True, id 0)
                              simple apply @eq_pi (cost 1, pattern 
                              ProofIrrel (@eq ?M1869 ?M1870 ?M1872), id 0)
                              simple apply prod_pi (cost 2, pattern 
                              ProofIrrel (prod ?M1865 ?M1866), id 0)
                              simple apply and_pi (cost 2, pattern 
                              ProofIrrel (and ?M1861 ?M1862), id 0)
                              (*external*) (progress lazy beta) (cost 200, pattern 
                              ProofIrrel _, id 0)
For CMorphisms.Proper ->   simple apply @CMorphisms.proper_proper (cost 0, pattern 
                           @CMorphisms.Proper
                             (forall (_ : CRelationClasses.crelation ?M485)
                                (_ : ?M485),
                              Type)
                             (@CMorphisms.respectful
                                (CRelationClasses.crelation ?M485)
                                (forall _ : ?M485, Type)
                                (@CRelationClasses.relation_equivalence ?M485)
                                (@CMorphisms.respectful 
                                   ?M485 Type (@eq ?M485)
                                   CRelationClasses.iffT))
                             (@CMorphisms.Proper ?M485), id 0)
                           simple apply @CMorphisms.respectful_morphism (cost 0, pattern 
                           @CMorphisms.Proper
                             (forall (_ : CRelationClasses.crelation ?M483)
                                (_ : CRelationClasses.crelation ?M484),
                              CRelationClasses.crelation
                                (forall _ : ?M483, ?M484))
                             (@CMorphisms.respectful
                                (CRelationClasses.crelation ?M483)
                                (forall _ : CRelationClasses.crelation ?M484,
                                 CRelationClasses.crelation
                                   (forall _ : ?M483, ?M484))
                                (@CRelationClasses.relation_equivalence ?M483)
                                (@CMorphisms.respectful
                                   (CRelationClasses.crelation ?M484)
                                   (CRelationClasses.crelation
                                      (forall _ : ?M483, ?M484))
                                   (@CRelationClasses.relation_equivalence
                                      ?M484)
                                   (@CRelationClasses.relation_equivalence
                                      (forall _ : ?M483, ?M484))))
                             (@CMorphisms.respectful ?M483 ?M484), id 0)
                           simple apply CMorphisms.compose_proper (cost 0, pattern 
                           @CMorphisms.Proper
                             (forall (_ : forall _ : ?M474, ?M475)
                                (_ : forall _ : ?M473, ?M474) 
                                (_ : ?M473),
                              ?M475)
                             (@CMorphisms.respectful
                                (forall _ : ?M474, ?M475)
                                (forall (_ : forall _ : ?M473, ?M474)
                                   (_ : ?M473),
                                 ?M475)
                                (@CMorphisms.respectful 
                                   ?M474 ?M475 ?M477 
                                   ?M478)
                                (@CMorphisms.respectful
                                   (forall _ : ?M473, ?M474)
                                   (forall _ : ?M473, ?M475)
                                   (@CMorphisms.respectful 
                                      ?M473 ?M474 
                                      ?M476 ?M477)
                                   (@CMorphisms.respectful 
                                      ?M473 ?M475 
                                      ?M476 ?M478)))
                             (@compose ?M473 ?M474 ?M475), id 0)
                           simple apply @CMorphisms.proper_subrelation_proper_arrow (cost 0, pattern 
                           @CMorphisms.Proper
                             (forall (_ : CRelationClasses.crelation ?M438)
                                (_ : ?M438),
                              Type)
                             (@CMorphisms.respectful
                                (CRelationClasses.crelation ?M438)
                                (forall _ : ?M438, Type)
                                (@CRelationClasses.subrelation ?M438)
                                (@CMorphisms.respectful 
                                   ?M438 Type (@eq ?M438)
                                   CRelationClasses.arrow))
                             (@CMorphisms.Proper ?M438), id 0)
                           (*external*) (apply @CMorphisms.flip_proper) (cost 1, pattern 
                           @CMorphisms.Proper _ _
                             (@CRelationClasses.flip _ _ _ _), id 0)
                           simple apply @CMorphisms.PER_type_morphism (cost 1, pattern 
                           @CMorphisms.Proper
                             (forall (_ : ?M470) (_ : ?M470), Type)
                             (@CMorphisms.respectful 
                                ?M470 (forall _ : ?M470, Type) 
                                ?M471
                                (@CMorphisms.respectful 
                                   ?M470 Type ?M471 CRelationClasses.iffT))
                             ?M471, id 0)
                           simple apply @CMorphisms.trans_contra_co_type_morphism (cost 1, pattern 
                           @CMorphisms.Proper
                             (forall (_ : ?M444) (_ : ?M444), Type)
                             (@CMorphisms.respectful 
                                ?M444 (forall _ : ?M444, Type)
                                (@CRelationClasses.flip 
                                   ?M444 ?M444 Type 
                                   ?M445)
                                (@CMorphisms.respectful 
                                   ?M444 Type ?M445 CRelationClasses.arrow))
                             ?M445, id 0)
                           simple apply @CMorphisms.subrelation_id_proper (cost 1, pattern 
                           @CMorphisms.Proper (forall _ : ?M434, ?M434)
                             (@CMorphisms.respectful ?M434 ?M434 ?M435 ?M436)
                             (@id ?M434), id 0)
                           (*external*) (class_apply
                                          @CMorphisms.proper_flip_proper) (cost 2, pattern 
                           @CMorphisms.Proper _
                             (@CRelationClasses.flip _ _ _ _) _, id 0)
                           simple apply @CMorphisms.trans_co_eq_inv_arrow_morphism (cost 2, pattern 
                           @CMorphisms.Proper
                             (forall (_ : ?M467) (_ : ?M467), Type)
                             (@CMorphisms.respectful 
                                ?M467 (forall _ : ?M467, Type) 
                                ?M468
                                (@CMorphisms.respectful 
                                   ?M467 Type (@eq ?M467)
                                   (@CRelationClasses.flip Type Type Type
                                      CRelationClasses.arrow)))
                             ?M468, id 0)
                           simple apply @CMorphisms.per_partial_app_type_morphism (cost 2, pattern 
                           @CMorphisms.Proper (forall _ : ?M463, Type)
                             (@CMorphisms.respectful 
                                ?M463 Type ?M464 CRelationClasses.iffT)
                             (?M464 ?M466), id 0)
                           simple eapply @CMorphisms.PartialOrder_proper_type (cost 3, pattern 
                           @CMorphisms.Proper
                             (forall (_ : ?M486) (_ : ?M486), Type)
                             (@CMorphisms.respectful 
                                ?M486 (forall _ : ?M486, Type) 
                                ?M487
                                (@CMorphisms.respectful 
                                   ?M486 Type ?M487 CRelationClasses.iffT))
                             ?M489, id 0)
                           simple apply @CMorphisms.trans_sym_contra_arrow_morphism (cost 3, pattern 
                           @CMorphisms.Proper (forall _ : ?M459, Type)
                             (@CMorphisms.respectful 
                                ?M459 Type
                                (@CRelationClasses.flip 
                                   ?M459 ?M459 Type 
                                   ?M460)
                                CRelationClasses.arrow)
                             (?M460 ?M462), id 0)
                           simple apply @CMorphisms.trans_sym_co_inv_impl_type_morphism (cost 3, pattern 
                           @CMorphisms.Proper (forall _ : ?M455, Type)
                             (@CMorphisms.respectful 
                                ?M455 Type ?M456
                                (@CRelationClasses.flip Type Type Type
                                   CRelationClasses.arrow))
                             (?M456 ?M458), id 0)
                           simple apply @CMorphisms.trans_co_impl_type_morphism (cost 3, pattern 
                           @CMorphisms.Proper (forall _ : ?M451, Type)
                             (@CMorphisms.respectful 
                                ?M451 Type ?M452 CRelationClasses.arrow)
                             (?M452 ?M454), id 0)
                           simple apply @CMorphisms.trans_contra_inv_impl_type_morphism (cost 3, pattern 
                           @CMorphisms.Proper (forall _ : ?M447, Type)
                             (@CMorphisms.respectful 
                                ?M447 Type
                                (@CRelationClasses.flip 
                                   ?M447 ?M447 Type 
                                   ?M448)
                                (@CRelationClasses.flip Type Type Type
                                   CRelationClasses.arrow))
                             (?M448 ?M450), id 0)
                           (*external*) CMorphisms.partial_application_tactic (cost 4, pattern 
                           @CMorphisms.Proper _ _ _, id 0)
                           (*external*) CMorphisms.proper_subrelation (cost 5, pattern 
                           @CMorphisms.Proper _ ?H _, id 0)
                           (*external*) CMorphisms.proper_normalization (cost 6, pattern 
                           @CMorphisms.Proper _ _ _, id 0)
                           (*external*) CMorphisms.proper_reflexive (cost 7, pattern 
                           @CMorphisms.Proper _ _ _, id 0)
For Proper ->   simple apply Permutation_app' (cost 0, pattern 
                @Proper
                  (forall (_ : list ?M6002) (_ : list ?M6002), list ?M6002)
                  (@respectful (list ?M6002)
                     (forall _ : list ?M6002, list ?M6002)
                     (@Permutation ?M6002)
                     (@respectful (list ?M6002) (list ?M6002)
                        (@Permutation ?M6002) (@Permutation ?M6002)))
                  (@app ?M6002), id 0)
                simple apply Permutation_cons (cost 0, pattern 
                @Proper (forall (_ : ?M6001) (_ : list ?M6001), list ?M6001)
                  (@respectful ?M6001 (forall _ : list ?M6001, list ?M6001)
                     (@eq ?M6001)
                     (@respectful (list ?M6001) (list ?M6001)
                        (@Permutation ?M6001) (@Permutation ?M6001)))
                  (@cons ?M6001), id 0)
                simple apply @infinite_fresh_Permutation (cost 0, pattern 
                @Proper (forall _ : list ?M5999, ?M5999)
                  (@respectful (list ?M5999) ?M5999 
                     (@Permutation ?M5999) (@eq ?M5999))
                  (@fresh ?M5999 (list ?M5999)
                     (@infinite_fresh ?M5999 ?M6000)), id 0)
                simple apply @slookup_proper (cost 0, pattern 
                @Proper (forall _ : stream ?M5894, ?M5894)
                  (@respectful (stream ?M5894) ?M5894
                     (@equiv (stream ?M5894) (@stream_equiv ?M5894))
                     (@eq ?M5894))
                  (@slookup ?M5894 ?M5895), id 0)
                simple apply @stail_proper (cost 0, pattern 
                @Proper (forall _ : stream ?M5893, stream ?M5893)
                  (@respectful (stream ?M5893) (stream ?M5893)
                     (@equiv (stream ?M5893) (@stream_equiv ?M5893))
                     (@equiv (stream ?M5893) (@stream_equiv ?M5893)))
                  (@stail ?M5893), id 0)
                simple apply @shead_proper (cost 0, pattern 
                @Proper (forall _ : stream ?M5892, ?M5892)
                  (@respectful (stream ?M5892) ?M5892
                     (@equiv (stream ?M5892) (@stream_equiv ?M5892))
                     (@eq ?M5892))
                  (@shead ?M5892), id 0)
                simple apply @scons_proper (cost 0, pattern 
                @Proper (forall _ : stream ?M5890, stream ?M5890)
                  (@respectful (stream ?M5890) (stream ?M5890)
                     (@equiv (stream ?M5890) (@stream_equiv ?M5890))
                     (@equiv (stream ?M5890) (@stream_equiv ?M5890)))
                  (@scons ?M5890 ?M5891), id 0)
                simple apply @gmultiset_disj_union_list_permutation_proper (cost 0, pattern 
                @Proper
                  (forall _ : list (@gmultiset ?M5632 ?M5633 ?M5634),
                   @gmultiset ?M5632 ?M5633 ?M5634)
                  (@respectful (list (@gmultiset ?M5632 ?M5633 ?M5634))
                     (@gmultiset ?M5632 ?M5633 ?M5634)
                     (@Permutation (@gmultiset ?M5632 ?M5633 ?M5634))
                     (@eq (@gmultiset ?M5632 ?M5633 ?M5634)))
                  (@disj_union_list (@gmultiset ?M5632 ?M5633 ?M5634)
                     (@gmultiset_empty ?M5632 ?M5633 ?M5634)
                     (@gmultiset_disj_union ?M5632 ?M5633 ?M5634)), id 0)
                simple apply @list_to_set_disj_perm (cost 0, pattern 
                @Proper
                  (forall _ : list ?M5592, @gmultiset ?M5592 ?M5593 ?M5594)
                  (@respectful (list ?M5592)
                     (@gmultiset ?M5592 ?M5593 ?M5594) 
                     (@Permutation ?M5592)
                     (@eq (@gmultiset ?M5592 ?M5593 ?M5594)))
                  (@list_to_set_disj ?M5592 (@gmultiset ?M5592 ?M5593 ?M5594)
                     (@gmultiset_singleton ?M5592 ?M5593 ?M5594)
                     (@gmultiset_empty ?M5592 ?M5593 ?M5594)
                     (@gmultiset_disj_union ?M5592 ?M5593 ?M5594)), id 0)
                simple eapply @dom_proper_L (cost 0, pattern 
                @Proper (forall _ : ?M4705 ?M4723, ?M4706)
                  (@respectful (?M4705 ?M4723) ?M4706
                     (@equiv (?M4705 ?M4723)
                        (@map_equiv ?M4704 ?M4705 ?M4709 ?M4723 ?M4724))
                     (@eq ?M4706))
                  (@dom (?M4705 ?M4723) ?M4706 (?M4707 ?M4723)), id 0)
                exact app_binder_Permutation (cost 0, pattern 
                @Proper
                  (forall (_ : list binder) (_ : list string), list string)
                  (@respectful (list binder)
                     (forall _ : list string, list string)
                     (@Permutation binder)
                     (@respectful (list string) (list string)
                        (@Permutation string) (@Permutation string)))
                  app_binder, id 0)
                simple apply cons_binder_Permutation (cost 0, pattern 
                @Proper (forall _ : list string, list string)
                  (@respectful (list string) (list string)
                     (@Permutation string) (@Permutation string))
                  (cons_binder ?M4572), id 0)
                simple apply @map_disjoint_proper (cost 0, pattern 
                @Proper
                  (forall (_ : ?M4365 ?M4367) (_ : ?M4365 ?M4367), Prop)
                  (@respectful (?M4365 ?M4367)
                     (forall _ : ?M4365 ?M4367, Prop)
                     (@equiv (?M4365 ?M4367)
                        (@map_equiv ?M4364 ?M4365 ?M4366 ?M4367 ?M4368))
                     (@respectful (?M4365 ?M4367) Prop
                        (@equiv (?M4365 ?M4367)
                           (@map_equiv ?M4364 ?M4365 ?M4366 ?M4367 ?M4368))
                        iff))
                  (@map_disjoint ?M4364 ?M4365 ?M4366 ?M4367), id 0)
                simple apply @lookup_proper (cost 0, pattern 
                @Proper (forall _ : ?M4171 ?M4173, option ?M4173)
                  (@respectful (?M4171 ?M4173) (option ?M4173)
                     (@equiv (?M4171 ?M4173)
                        (@map_equiv ?M4170 ?M4171 ?M4172 ?M4173 ?M4174))
                     (@equiv (option ?M4173) (@option_equiv ?M4173 ?M4174)))
                  (@lookup ?M4170 ?M4173 (?M4171 ?M4173) 
                     (?M4172 ?M4173) ?M4175), id 0)
                simple apply @map_disjoint_list_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list (?M4047 ?M4049), Prop)
                  (@respectful (list (?M4047 ?M4049)) Prop
                     (@Permutation (?M4047 ?M4049)) iff)
                  (@map_disjoint_list ?M4046 ?M4047 ?M4048 ?M4049), id 0)
                simple apply @set_infinite_proper (cost 0, pattern 
                @Proper (forall _ : ?M3363, Prop)
                  (@respectful ?M3363 Prop
                     (@equiv ?M3363
                        (@set_equiv_instance ?M3362 ?M3363 ?M3364))
                     iff)
                  (@set_infinite ?M3362 ?M3363 ?M3364), id 0)
                simple apply @set_infinite_subseteq (cost 0, pattern 
                @Proper (forall _ : ?M3360, Prop)
                  (@respectful ?M3360 Prop
                     (@subseteq ?M3360
                        (@set_subseteq_instance ?M3359 ?M3360 ?M3361))
                     impl)
                  (@set_infinite ?M3359 ?M3360 ?M3361), id 0)
                simple apply @set_finite_proper (cost 0, pattern 
                @Proper (forall _ : ?M3357, Prop)
                  (@respectful ?M3357 Prop
                     (@equiv ?M3357
                        (@set_equiv_instance ?M3356 ?M3357 ?M3358))
                     iff)
                  (@set_finite ?M3356 ?M3357 ?M3358), id 0)
                simple apply @set_finite_subseteq (cost 0, pattern 
                @Proper (forall _ : ?M3354, Prop)
                  (@respectful ?M3354 Prop
                     (@flip ?M3354 ?M3354 Prop
                        (@subseteq ?M3354
                           (@set_subseteq_instance ?M3353 ?M3354 ?M3355)))
                     impl)
                  (@set_finite ?M3353 ?M3354 ?M3355), id 0)
                simple apply @subset_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2602) (_ : ?M2602), Prop)
                  (@respectful ?M2602 (forall _ : ?M2602, Prop)
                     (@equiv ?M2602
                        (@set_equiv_instance ?M2601 ?M2602 ?M2603))
                     (@respectful ?M2602 Prop
                        (@equiv ?M2602
                           (@set_equiv_instance ?M2601 ?M2602 ?M2603))
                        iff))
                  (@strict ?M2602
                     (@subseteq ?M2602
                        (@set_subseteq_instance ?M2601 ?M2602 ?M2603))), id 0)
                simple apply @subseteq_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2599) (_ : ?M2599), Prop)
                  (@respectful ?M2599 (forall _ : ?M2599, Prop)
                     (@equiv ?M2599
                        (@set_equiv_instance ?M2598 ?M2599 ?M2600))
                     (@respectful ?M2599 Prop
                        (@equiv ?M2599
                           (@set_equiv_instance ?M2598 ?M2599 ?M2600))
                        iff))
                  (@subseteq ?M2599
                     (@set_subseteq_instance ?M2598 ?M2599 ?M2600)), id 0)
                simple apply @disjoint_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2582) (_ : ?M2582), Prop)
                  (@respectful ?M2582 (forall _ : ?M2582, Prop)
                     (@equiv ?M2582
                        (@set_equiv_instance ?M2581 ?M2582 ?M2583))
                     (@respectful ?M2582 Prop
                        (@equiv ?M2582
                           (@set_equiv_instance ?M2581 ?M2582 ?M2583))
                        iff))
                  (@disjoint ?M2582
                     (@set_disjoint_instance ?M2581 ?M2582 ?M2583)), id 0)
                simple apply @singleton_proper (cost 0, pattern 
                @Proper (forall _ : ?M2574, ?M2575)
                  (@respectful ?M2574 ?M2575 (@eq ?M2574)
                     (@equiv ?M2575
                        (@set_equiv_instance ?M2574 ?M2575 ?M2576)))
                  (@singleton ?M2574 ?M2575 ?M2577), id 0)
                simple apply @max_list_with_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2434, nat)
                  (@respectful (list ?M2434) nat (@Permutation ?M2434)
                     (@eq nat))
                  (@max_list_with ?M2434 ?M2435), id 0)
                simple apply @sum_list_with_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2432, nat)
                  (@respectful (list ?M2432) nat (@Permutation ?M2432)
                     (@eq nat))
                  (@sum_list_with ?M2432 ?M2433), id 0)
                simple apply @rotate_take_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2388, list ?M2388)
                  (@respectful (list ?M2388) (list ?M2388)
                     (@equiv (list ?M2388) (@list_equiv ?M2388 ?M2389))
                     (@equiv (list ?M2388) (@list_equiv ?M2388 ?M2389)))
                  (@rotate_take ?M2388 ?M2390 ?M2391), id 0)
                simple apply @list_misc.list.Proper_instance_2 (cost 0, pattern 
                @Proper (forall _ : list ?M2384, list ?M2384)
                  (@respectful (list ?M2384) (list ?M2384)
                     (@Forall2 ?M2384 ?M2384 ?M2385)
                     (@Forall2 ?M2384 ?M2384 ?M2385))
                  (@rotate_take ?M2384 ?M2386 ?M2387), id 0)
                simple apply @rotate_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2381, list ?M2381)
                  (@respectful (list ?M2381) (list ?M2381)
                     (@equiv (list ?M2381) (@list_equiv ?M2381 ?M2382))
                     (@equiv (list ?M2381) (@list_equiv ?M2381 ?M2382)))
                  (@rotate ?M2381 ?M2383), id 0)
                simple apply @list_misc.list.Proper_instance_1 (cost 0, pattern 
                @Proper (forall _ : list ?M2378, list ?M2378)
                  (@respectful (list ?M2378) (list ?M2378)
                     (@Forall2 ?M2378 ?M2378 ?M2379)
                     (@Forall2 ?M2378 ?M2378 ?M2379))
                  (@rotate ?M2378 ?M2380), id 0)
                simple apply @resize_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2375) (_ : list ?M2375), list ?M2375)
                  (@respectful ?M2375 (forall _ : list ?M2375, list ?M2375)
                     (@equiv ?M2375 ?M2376)
                     (@respectful (list ?M2375) (list ?M2375)
                        (@equiv (list ?M2375) (@list_equiv ?M2375 ?M2376))
                        (@equiv (list ?M2375) (@list_equiv ?M2375 ?M2376))))
                  (@resize ?M2375 ?M2377), id 0)
                simple apply @list_misc.list.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : ?M2372) (_ : list ?M2372), list ?M2372)
                  (@respectful ?M2372 (forall _ : list ?M2372, list ?M2372)
                     ?M2373
                     (@respectful (list ?M2372) (list ?M2372)
                        (@Forall2 ?M2372 ?M2372 ?M2373)
                        (@Forall2 ?M2372 ?M2372 ?M2373)))
                  (@resize ?M2372 ?M2374), id 0)
                simple apply @zip_with_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall (_ : ?M2366) (_ : ?M2368), ?M2370)
                     (_ : list ?M2366) (_ : list ?M2368),
                   list ?M2370)
                  (@respectful (forall (_ : ?M2366) (_ : ?M2368), ?M2370)
                     (forall (_ : list ?M2366) (_ : list ?M2368), list ?M2370)
                     (@respectful ?M2366 (forall _ : ?M2368, ?M2370)
                        (@equiv ?M2366 ?M2367)
                        (@respectful ?M2368 ?M2370 
                           (@equiv ?M2368 ?M2369) 
                           (@equiv ?M2370 ?M2371)))
                     (@respectful (list ?M2366)
                        (forall _ : list ?M2368, list ?M2370)
                        (@equiv (list ?M2366) (@list_equiv ?M2366 ?M2367))
                        (@respectful (list ?M2368) 
                           (list ?M2370)
                           (@equiv (list ?M2368) (@list_equiv ?M2368 ?M2369))
                           (@equiv (list ?M2370) (@list_equiv ?M2370 ?M2371)))))
                  (@zip_with ?M2366 ?M2368 ?M2370), id 0)
                simple apply @imap_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall (_ : nat) (_ : ?M2354), ?M2356)
                     (_ : list ?M2354),
                   list ?M2356)
                  (@respectful (forall (_ : nat) (_ : ?M2354), ?M2356)
                     (forall _ : list ?M2354, list ?M2356)
                     (@pointwise_relation nat (forall _ : ?M2354, ?M2356)
                        (@respectful ?M2354 ?M2356 
                           (@equiv ?M2354 ?M2355) 
                           (@equiv ?M2356 ?M2357)))
                     (@respectful (list ?M2354) (list ?M2356)
                        (@equiv (list ?M2354) (@list_equiv ?M2354 ?M2355))
                        (@equiv (list ?M2356) (@list_equiv ?M2356 ?M2357))))
                  (@imap ?M2354 ?M2356), id 0)
                simple apply @mapM_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2350, option ?M2352)
                     (_ : list ?M2350),
                   option (list ?M2352))
                  (@respectful (forall _ : ?M2350, option ?M2352)
                     (forall _ : list ?M2350, option (list ?M2352))
                     (@respectful ?M2350 (option ?M2352)
                        (@equiv ?M2350 ?M2351)
                        (@equiv (option ?M2352) (@option_equiv ?M2352 ?M2353)))
                     (@respectful (list ?M2350) (option (list ?M2352))
                        (@equiv (list ?M2350) (@list_equiv ?M2350 ?M2351))
                        (@equiv (option (list ?M2352))
                           (@option_equiv (list ?M2352)
                              (@list_equiv ?M2352 ?M2353)))))
                  (@mapM option option_bind option_ret ?M2350 ?M2352), id 0)
                simple apply @join_Permutation (cost 0, pattern 
                @Proper (forall _ : list (list ?M2349), list ?M2349)
                  (@respectful (list (list ?M2349)) 
                     (list ?M2349) (@Permutation (list ?M2349))
                     (@Permutation ?M2349))
                  (@mjoin list list_join ?M2349), id 0)
                simple apply @list_join_proper (cost 0, pattern 
                @Proper (forall _ : list (list ?M2347), list ?M2347)
                  (@respectful (list (list ?M2347)) 
                     (list ?M2347)
                     (@equiv (list (list ?M2347))
                        (@list_equiv (list ?M2347)
                           (@list_equiv ?M2347 ?M2348)))
                     (@equiv (list ?M2347) (@list_equiv ?M2347 ?M2348)))
                  (@mjoin list list_join ?M2347), id 0)
                simple apply @bind_Permutation (cost 0, pattern 
                @Proper (forall _ : list ?M2344, list ?M2345)
                  (@respectful (list ?M2344) (list ?M2345)
                     (@Permutation ?M2344) (@Permutation ?M2345))
                  (@mbind list list_bind ?M2344 ?M2345 ?M2346), id 0)
                simple apply @bind_submseteq (cost 0, pattern 
                @Proper (forall _ : list ?M2341, list ?M2342)
                  (@respectful (list ?M2341) (list ?M2342)
                     (@submseteq ?M2341) (@submseteq ?M2342))
                  (@mbind list list_bind ?M2341 ?M2342 ?M2343), id 0)
                simple apply @bind_sublist (cost 0, pattern 
                @Proper (forall _ : list ?M2338, list ?M2339)
                  (@respectful (list ?M2338) (list ?M2339) 
                     (@sublist ?M2338) (@sublist ?M2339))
                  (@mbind list list_bind ?M2338 ?M2339 ?M2340), id 0)
                simple apply @list_bind_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2334, list ?M2336)
                     (_ : list ?M2334),
                   list ?M2336)
                  (@respectful (forall _ : ?M2334, list ?M2336)
                     (forall _ : list ?M2334, list ?M2336)
                     (@respectful ?M2334 (list ?M2336) 
                        (@equiv ?M2334 ?M2335)
                        (@equiv (list ?M2336) (@list_equiv ?M2336 ?M2337)))
                     (@respectful (list ?M2334) (list ?M2336)
                        (@equiv (list ?M2334) (@list_equiv ?M2334 ?M2335))
                        (@equiv (list ?M2336) (@list_equiv ?M2336 ?M2337))))
                  (@mbind list list_bind ?M2334 ?M2336), id 0)
                simple apply @omap_Permutation (cost 0, pattern 
                @Proper (forall _ : list ?M2331, list ?M2332)
                  (@respectful (list ?M2331) (list ?M2332)
                     (@Permutation ?M2331) (@Permutation ?M2332))
                  (@omap list list_omap ?M2331 ?M2332 ?M2333), id 0)
                simple apply @list_omap_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2327, option ?M2329)
                     (_ : list ?M2327),
                   list ?M2329)
                  (@respectful (forall _ : ?M2327, option ?M2329)
                     (forall _ : list ?M2327, list ?M2329)
                     (@respectful ?M2327 (option ?M2329)
                        (@equiv ?M2327 ?M2328)
                        (@equiv (option ?M2329) (@option_equiv ?M2329 ?M2330)))
                     (@respectful (list ?M2327) (list ?M2329)
                        (@equiv (list ?M2327) (@list_equiv ?M2327 ?M2328))
                        (@equiv (list ?M2329) (@list_equiv ?M2329 ?M2330))))
                  (@omap list list_omap ?M2327 ?M2329), id 0)
                simple apply @fmap_Permutation (cost 0, pattern 
                @Proper (forall _ : list ?M2324, list ?M2325)
                  (@respectful (list ?M2324) (list ?M2325)
                     (@Permutation ?M2324) (@Permutation ?M2325))
                  (@fmap list list_fmap ?M2324 ?M2325 ?M2326), id 0)
                simple apply @fmap_submseteq (cost 0, pattern 
                @Proper (forall _ : list ?M2321, list ?M2322)
                  (@respectful (list ?M2321) (list ?M2322)
                     (@submseteq ?M2321) (@submseteq ?M2322))
                  (@fmap list list_fmap ?M2321 ?M2322 ?M2323), id 0)
                simple apply @fmap_sublist (cost 0, pattern 
                @Proper (forall _ : list ?M2318, list ?M2319)
                  (@respectful (list ?M2318) (list ?M2319) 
                     (@sublist ?M2318) (@sublist ?M2319))
                  (@fmap list list_fmap ?M2318 ?M2319 ?M2320), id 0)
                simple apply @list_fmap_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2304, ?M2306) (_ : list ?M2304),
                   list ?M2306)
                  (@respectful (forall _ : ?M2304, ?M2306)
                     (forall _ : list ?M2304, list ?M2306)
                     (@respectful ?M2304 ?M2306 (@equiv ?M2304 ?M2305)
                        (@equiv ?M2306 ?M2307))
                     (@respectful (list ?M2304) (list ?M2306)
                        (@equiv (list ?M2304) (@list_equiv ?M2304 ?M2305))
                        (@equiv (list ?M2306) (@list_equiv ?M2306 ?M2307))))
                  (@fmap list list_fmap ?M2304 ?M2306), id 0)
                simple apply @last_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2292, option ?M2292)
                  (@respectful (list ?M2292) (option ?M2292)
                     (@equiv (list ?M2292) (@list_equiv ?M2292 ?M2293))
                     (@equiv (option ?M2292) (@option_equiv ?M2292 ?M2293)))
                  (@last ?M2292), id 0)
                simple apply @reverse_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2290, list ?M2290)
                  (@respectful (list ?M2290) (list ?M2290)
                     (@equiv (list ?M2290) (@list_equiv ?M2290 ?M2291))
                     (@equiv (list ?M2290) (@list_equiv ?M2290 ?M2291)))
                  (@reverse ?M2290), id 0)
                simple apply @replicate_proper (cost 0, pattern 
                @Proper (forall _ : ?M2287, list ?M2287)
                  (@respectful ?M2287 (list ?M2287) 
                     (@equiv ?M2287 ?M2288)
                     (@equiv (list ?M2287) (@list_equiv ?M2287 ?M2288)))
                  (@replicate ?M2287 ?M2289), id 0)
                simple apply @option_list_proper (cost 0, pattern 
                @Proper (forall _ : option ?M2280, list ?M2280)
                  (@respectful (option ?M2280) (list ?M2280)
                     (@equiv (option ?M2280) (@option_equiv ?M2280 ?M2281))
                     (@equiv (list ?M2280) (@list_equiv ?M2280 ?M2281)))
                  (@option_list ?M2280), id 0)
                simple apply @list_delete_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2277, list ?M2277)
                  (@respectful (list ?M2277) (list ?M2277)
                     (@equiv (list ?M2277) (@list_equiv ?M2277 ?M2278))
                     (@equiv (list ?M2277) (@list_equiv ?M2277 ?M2278)))
                  (@delete nat (list ?M2277) (@list_delete ?M2277) ?M2279), id 0)
                simple apply @list_inserts_proper (cost 0, pattern 
                @Proper
                  (forall (_ : list ?M2274) (_ : list ?M2274), list ?M2274)
                  (@respectful (list ?M2274)
                     (forall _ : list ?M2274, list ?M2274)
                     (@equiv (list ?M2274) (@list_equiv ?M2274 ?M2275))
                     (@respectful (list ?M2274) (list ?M2274)
                        (@equiv (list ?M2274) (@list_equiv ?M2274 ?M2275))
                        (@equiv (list ?M2274) (@list_equiv ?M2274 ?M2275))))
                  (@list_inserts ?M2274 ?M2276), id 0)
                simple apply @list_insert_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2271) (_ : list ?M2271), list ?M2271)
                  (@respectful ?M2271 (forall _ : list ?M2271, list ?M2271)
                     (@equiv ?M2271 ?M2272)
                     (@respectful (list ?M2271) (list ?M2271)
                        (@equiv (list ?M2271) (@list_equiv ?M2271 ?M2272))
                        (@equiv (list ?M2271) (@list_equiv ?M2271 ?M2272))))
                  (@insert nat ?M2271 (list ?M2271) 
                     (@list_insert ?M2271) ?M2273), id 0)
                simple apply @list_alter_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2269, ?M2269) 
                     (_ : nat) (_ : list ?M2269),
                   list ?M2269)
                  (@respectful (forall _ : ?M2269, ?M2269)
                     (forall (_ : nat) (_ : list ?M2269), list ?M2269)
                     (@respectful ?M2269 ?M2269 (@equiv ?M2269 ?M2270)
                        (@equiv ?M2269 ?M2270))
                     (@respectful nat (forall _ : list ?M2269, list ?M2269)
                        (@eq nat)
                        (@respectful (list ?M2269) 
                           (list ?M2269)
                           (@equiv (list ?M2269) (@list_equiv ?M2269 ?M2270))
                           (@equiv (list ?M2269) (@list_equiv ?M2269 ?M2270)))))
                  (@alter nat ?M2269 (list ?M2269) (@list_alter ?M2269)), id 0)
                simple apply @list_lookup_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2261, option ?M2261)
                  (@respectful (list ?M2261) (option ?M2261)
                     (@equiv (list ?M2261) (@list_equiv ?M2261 ?M2262))
                     (@equiv (option ?M2261) (@option_equiv ?M2261 ?M2262)))
                  (@lookup nat ?M2261 (list ?M2261) 
                     (@list_lookup ?M2261) ?M2263), id 0)
                simple apply @drop_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2258, list ?M2258)
                  (@respectful (list ?M2258) (list ?M2258)
                     (@equiv (list ?M2258) (@list_equiv ?M2258 ?M2259))
                     (@equiv (list ?M2258) (@list_equiv ?M2258 ?M2259)))
                  (@skipn ?M2258 ?M2260), id 0)
                simple apply @take_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2255, list ?M2255)
                  (@respectful (list ?M2255) (list ?M2255)
                     (@equiv (list ?M2255) (@list_equiv ?M2255 ?M2256))
                     (@equiv (list ?M2255) (@list_equiv ?M2255 ?M2256)))
                  (@firstn ?M2255 ?M2257), id 0)
                simple apply @tail_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2253, list ?M2253)
                  (@respectful (list ?M2253) (list ?M2253)
                     (@equiv (list ?M2253) (@list_equiv ?M2253 ?M2254))
                     (@equiv (list ?M2253) (@list_equiv ?M2253 ?M2254)))
                  (@tl ?M2253), id 0)
                simple apply @length_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2251, nat)
                  (@respectful (list ?M2251) nat
                     (@equiv (list ?M2251) (@list_equiv ?M2251 ?M2252))
                     (@eq nat))
                  (@length ?M2251), id 0)
                simple apply @app_proper (cost 0, pattern 
                @Proper
                  (forall (_ : list ?M2249) (_ : list ?M2249), list ?M2249)
                  (@respectful (list ?M2249)
                     (forall _ : list ?M2249, list ?M2249)
                     (@equiv (list ?M2249) (@list_equiv ?M2249 ?M2250))
                     (@respectful (list ?M2249) (list ?M2249)
                        (@equiv (list ?M2249) (@list_equiv ?M2249 ?M2250))
                        (@equiv (list ?M2249) (@list_equiv ?M2249 ?M2250))))
                  (@app ?M2249), id 0)
                simple apply @cons_proper (cost 0, pattern 
                @Proper (forall (_ : ?M2247) (_ : list ?M2247), list ?M2247)
                  (@respectful ?M2247 (forall _ : list ?M2247, list ?M2247)
                     (@equiv ?M2247 ?M2248)
                     (@respectful (list ?M2247) (list ?M2247)
                        (@equiv (list ?M2247) (@list_equiv ?M2247 ?M2248))
                        (@equiv (list ?M2247) (@list_equiv ?M2247 ?M2248))))
                  (@cons ?M2247), id 0)
                simple apply @list_subseteq_Permutation (cost 0, pattern 
                @Proper (forall (_ : list ?M2238) (_ : list ?M2238), Prop)
                  (@respectful (list ?M2238) (forall _ : list ?M2238, Prop)
                     (@Permutation ?M2238)
                     (@respectful (list ?M2238) Prop 
                        (@Permutation ?M2238) iff))
                  (@subseteq (list ?M2238) (@list_subseteq ?M2238)), id 0)
                simple apply @Proper_instance_16 (cost 0, pattern 
                @Proper (forall _ : list ?M2235, option ?M2235)
                  (@respectful (list ?M2235) (option ?M2235)
                     (@Forall2 ?M2235 ?M2235 ?M2236)
                     (@option_Forall2 ?M2235 ?M2235 ?M2236))
                  (@last ?M2235), id 0)
                simple apply @Proper_instance_15 (cost 0, pattern 
                @Proper (forall _ : list ?M2233, list ?M2233)
                  (@respectful (list ?M2233) (list ?M2233)
                     (@Forall2 ?M2233 ?M2233 ?M2234)
                     (@Forall2 ?M2233 ?M2233 ?M2234))
                  (@reverse ?M2233), id 0)
                simple apply @Proper_instance_14 (cost 0, pattern 
                @Proper (forall _ : ?M2230, list ?M2230)
                  (@respectful ?M2230 (list ?M2230) 
                     ?M2231 (@Forall2 ?M2230 ?M2230 ?M2231))
                  (@replicate ?M2230 ?M2232), id 0)
                simple apply @Proper_instance_12 (cost 0, pattern 
                @Proper (forall _ : option ?M2223, list ?M2223)
                  (@respectful (option ?M2223) (list ?M2223)
                     (@option_Forall2 ?M2223 ?M2223 ?M2224)
                     (@Forall2 ?M2223 ?M2223 ?M2224))
                  (@option_list ?M2223), id 0)
                simple apply @Proper_instance_11 (cost 0, pattern 
                @Proper (forall _ : list ?M2220, list ?M2220)
                  (@respectful (list ?M2220) (list ?M2220)
                     (@Forall2 ?M2220 ?M2220 ?M2221)
                     (@Forall2 ?M2220 ?M2220 ?M2221))
                  (@delete nat (list ?M2220) (@list_delete ?M2220) ?M2222), id 0)
                simple apply @Proper_instance_10 (cost 0, pattern 
                @Proper
                  (forall (_ : list ?M2217) (_ : list ?M2217), list ?M2217)
                  (@respectful (list ?M2217)
                     (forall _ : list ?M2217, list ?M2217)
                     (@Forall2 ?M2217 ?M2217 ?M2218)
                     (@respectful (list ?M2217) (list ?M2217)
                        (@Forall2 ?M2217 ?M2217 ?M2218)
                        (@Forall2 ?M2217 ?M2217 ?M2218)))
                  (@list_inserts ?M2217 ?M2219), id 0)
                simple apply @Proper_instance_9 (cost 0, pattern 
                @Proper (forall (_ : ?M2214) (_ : list ?M2214), list ?M2214)
                  (@respectful ?M2214 (forall _ : list ?M2214, list ?M2214)
                     ?M2215
                     (@respectful (list ?M2214) (list ?M2214)
                        (@Forall2 ?M2214 ?M2214 ?M2215)
                        (@Forall2 ?M2214 ?M2214 ?M2215)))
                  (@insert nat ?M2214 (list ?M2214) 
                     (@list_insert ?M2214) ?M2216), id 0)
                simple apply @Proper_instance_8 (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2212, ?M2212) 
                     (_ : nat) (_ : list ?M2212),
                   list ?M2212)
                  (@respectful (forall _ : ?M2212, ?M2212)
                     (forall (_ : nat) (_ : list ?M2212), list ?M2212)
                     (@respectful ?M2212 ?M2212 ?M2213 ?M2213)
                     (@respectful nat (forall _ : list ?M2212, list ?M2212)
                        (@eq nat)
                        (@respectful (list ?M2212) 
                           (list ?M2212) (@Forall2 ?M2212 ?M2212 ?M2213)
                           (@Forall2 ?M2212 ?M2212 ?M2213))))
                  (@alter nat ?M2212 (list ?M2212) (@list_alter ?M2212)), id 0)
                simple apply @Proper_instance_7 (cost 0, pattern 
                @Proper (forall _ : list ?M2209, option ?M2209)
                  (@respectful (list ?M2209) (option ?M2209)
                     (@Forall2 ?M2209 ?M2209 ?M2210)
                     (@option_Forall2 ?M2209 ?M2209 ?M2210))
                  (@lookup nat ?M2209 (list ?M2209) 
                     (@list_lookup ?M2209) ?M2211), id 0)
                simple apply @Proper_instance_6 (cost 0, pattern 
                @Proper (forall _ : list ?M2206, list ?M2206)
                  (@respectful (list ?M2206) (list ?M2206)
                     (@Forall2 ?M2206 ?M2206 ?M2207)
                     (@Forall2 ?M2206 ?M2206 ?M2207))
                  (@skipn ?M2206 ?M2208), id 0)
                simple apply @Proper_instance_5 (cost 0, pattern 
                @Proper (forall _ : list ?M2203, list ?M2203)
                  (@respectful (list ?M2203) (list ?M2203)
                     (@Forall2 ?M2203 ?M2203 ?M2204)
                     (@Forall2 ?M2203 ?M2203 ?M2204))
                  (@firstn ?M2203 ?M2205), id 0)
                simple apply @Proper_instance_4 (cost 0, pattern 
                @Proper (forall _ : list ?M2201, list ?M2201)
                  (@respectful (list ?M2201) (list ?M2201)
                     (@Forall2 ?M2201 ?M2201 ?M2202)
                     (@Forall2 ?M2201 ?M2201 ?M2202))
                  (@tl ?M2201), id 0)
                simple apply @Proper_instance_3 (cost 0, pattern 
                @Proper (forall _ : list ?M2199, nat)
                  (@respectful (list ?M2199) nat
                     (@Forall2 ?M2199 ?M2199 ?M2200) 
                     (@eq nat))
                  (@length ?M2199), id 0)
                simple apply @Proper_instance_2 (cost 0, pattern 
                @Proper
                  (forall (_ : list ?M2197) (_ : list ?M2197), list ?M2197)
                  (@respectful (list ?M2197)
                     (forall _ : list ?M2197, list ?M2197)
                     (@Forall2 ?M2197 ?M2197 ?M2198)
                     (@respectful (list ?M2197) (list ?M2197)
                        (@Forall2 ?M2197 ?M2197 ?M2198)
                        (@Forall2 ?M2197 ?M2197 ?M2198)))
                  (@app ?M2197), id 0)
                simple apply @Proper_instance_1 (cost 0, pattern 
                @Proper (forall (_ : ?M2195) (_ : list ?M2195), list ?M2195)
                  (@respectful ?M2195 (forall _ : list ?M2195, list ?M2195)
                     ?M2196
                     (@respectful (list ?M2195) (list ?M2195)
                        (@Forall2 ?M2195 ?M2195 ?M2196)
                        (@Forall2 ?M2195 ?M2195 ?M2196)))
                  (@cons ?M2195), id 0)
                simple apply @Exists_Permutation (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2172, Prop) (_ : list ?M2172),
                   Prop)
                  (@respectful (forall _ : ?M2172, Prop)
                     (forall _ : list ?M2172, Prop)
                     (@pointwise_relation ?M2172 Prop iff)
                     (@respectful (list ?M2172) Prop 
                        (@Permutation ?M2172) iff))
                  (@Exists ?M2172), id 0)
                simple apply @Forall_Permutation (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2171, Prop) (_ : list ?M2171),
                   Prop)
                  (@respectful (forall _ : ?M2171, Prop)
                     (forall _ : list ?M2171, Prop)
                     (@pointwise_relation ?M2171 Prop iff)
                     (@respectful (list ?M2171) Prop 
                        (@Permutation ?M2171) iff))
                  (@Forall ?M2171), id 0)
                simple apply @Exists_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2162, Prop) (_ : list ?M2162),
                   Prop)
                  (@respectful (forall _ : ?M2162, Prop)
                     (forall _ : list ?M2162, Prop)
                     (@pointwise_relation ?M2162 Prop iff)
                     (@respectful (list ?M2162) Prop (@eq (list ?M2162)) iff))
                  (@Exists ?M2162), id 0)
                simple apply @Forall_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2161, Prop) (_ : list ?M2161),
                   Prop)
                  (@respectful (forall _ : ?M2161, Prop)
                     (forall _ : list ?M2161, Prop)
                     (@pointwise_relation ?M2161 Prop iff)
                     (@respectful (list ?M2161) Prop (@eq (list ?M2161)) iff))
                  (@Forall ?M2161), id 0)
                simple apply @Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : list ?M2155) (_ : list ?M2155), Prop)
                  (@respectful (list ?M2155) (forall _ : list ?M2155, Prop)
                     (@Permutation ?M2155)
                     (@respectful (list ?M2155) Prop 
                        (@Permutation ?M2155) iff))
                  (@submseteq ?M2155), id 0)
                simple apply @filter_Permutation (cost 0, pattern 
                @Proper (forall _ : list ?M2144, list ?M2144)
                  (@respectful (list ?M2144) (list ?M2144)
                     (@Permutation ?M2144) (@Permutation ?M2144))
                  (@filter ?M2144 (list ?M2144) (@list_filter ?M2144) 
                     ?M2145 ?M2146), id 0)
                simple apply @NoDup_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2134, Prop)
                  (@respectful (list ?M2134) Prop (@Permutation ?M2134) iff)
                  (@NoDup ?M2134), id 0)
                simple apply @elem_of_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2132, Prop)
                  (@respectful (list ?M2132) Prop (@Permutation ?M2132) iff)
                  (@elem_of ?M2132 (list ?M2132) (@list_elem_of ?M2132)
                     ?M2133), id 0)
                simple apply @length_Permutation_proper (cost 0, pattern 
                @Proper (forall _ : list ?M2131, nat)
                  (@respectful (list ?M2131) nat (@Permutation ?M2131)
                     (@eq nat))
                  (@length ?M2131), id 0)
                simple apply @option.union_proper (cost 0, pattern 
                @Proper
                  (forall (_ : option ?M2041) (_ : option ?M2041),
                   option ?M2041)
                  (@respectful (option ?M2041)
                     (forall _ : option ?M2041, option ?M2041)
                     (@equiv (option ?M2041) (@option_equiv ?M2041 ?M2042))
                     (@respectful (option ?M2041) 
                        (option ?M2041)
                        (@equiv (option ?M2041) (@option_equiv ?M2041 ?M2042))
                        (@equiv (option ?M2041) (@option_equiv ?M2041 ?M2042))))
                  (@union (option ?M2041) (@option_union ?M2041)), id 0)
                simple apply @option.difference_with_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M2039) (_ : ?M2039), option ?M2039)
                     (_ : option ?M2039) (_ : option ?M2039),
                   option ?M2039)
                  (@respectful
                     (forall (_ : ?M2039) (_ : ?M2039), option ?M2039)
                     (forall (_ : option ?M2039) (_ : option ?M2039),
                      option ?M2039)
                     (@respectful ?M2039 (forall _ : ?M2039, option ?M2039)
                        (@equiv ?M2039 ?M2040)
                        (@respectful ?M2039 (option ?M2039)
                           (@equiv ?M2039 ?M2040)
                           (@equiv (option ?M2039)
                              (@option_equiv ?M2039 ?M2040))))
                     (@respectful (option ?M2039)
                        (forall _ : option ?M2039, option ?M2039)
                        (@equiv (option ?M2039) (@option_equiv ?M2039 ?M2040))
                        (@respectful (option ?M2039) 
                           (option ?M2039)
                           (@equiv (option ?M2039)
                              (@option_equiv ?M2039 ?M2040))
                           (@equiv (option ?M2039)
                              (@option_equiv ?M2039 ?M2040)))))
                  (@difference_with ?M2039 (option ?M2039)
                     (@option_difference_with ?M2039)), id 0)
                simple apply @option.intersection_with_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M2037) (_ : ?M2037), option ?M2037)
                     (_ : option ?M2037) (_ : option ?M2037),
                   option ?M2037)
                  (@respectful
                     (forall (_ : ?M2037) (_ : ?M2037), option ?M2037)
                     (forall (_ : option ?M2037) (_ : option ?M2037),
                      option ?M2037)
                     (@respectful ?M2037 (forall _ : ?M2037, option ?M2037)
                        (@equiv ?M2037 ?M2038)
                        (@respectful ?M2037 (option ?M2037)
                           (@equiv ?M2037 ?M2038)
                           (@equiv (option ?M2037)
                              (@option_equiv ?M2037 ?M2038))))
                     (@respectful (option ?M2037)
                        (forall _ : option ?M2037, option ?M2037)
                        (@equiv (option ?M2037) (@option_equiv ?M2037 ?M2038))
                        (@respectful (option ?M2037) 
                           (option ?M2037)
                           (@equiv (option ?M2037)
                              (@option_equiv ?M2037 ?M2038))
                           (@equiv (option ?M2037)
                              (@option_equiv ?M2037 ?M2038)))))
                  (@intersection_with ?M2037 (option ?M2037)
                     (@option_intersection_with ?M2037)), id 0)
                simple apply @option.union_with_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M2035) (_ : ?M2035), option ?M2035)
                     (_ : option ?M2035) (_ : option ?M2035),
                   option ?M2035)
                  (@respectful
                     (forall (_ : ?M2035) (_ : ?M2035), option ?M2035)
                     (forall (_ : option ?M2035) (_ : option ?M2035),
                      option ?M2035)
                     (@respectful ?M2035 (forall _ : ?M2035, option ?M2035)
                        (@equiv ?M2035 ?M2036)
                        (@respectful ?M2035 (option ?M2035)
                           (@equiv ?M2035 ?M2036)
                           (@equiv (option ?M2035)
                              (@option_equiv ?M2035 ?M2036))))
                     (@respectful (option ?M2035)
                        (forall _ : option ?M2035, option ?M2035)
                        (@equiv (option ?M2035) (@option_equiv ?M2035 ?M2036))
                        (@respectful (option ?M2035) 
                           (option ?M2035)
                           (@equiv (option ?M2035)
                              (@option_equiv ?M2035 ?M2036))
                           (@equiv (option ?M2035)
                              (@option_equiv ?M2035 ?M2036)))))
                  (@union_with ?M2035 (option ?M2035)
                     (@option_union_with ?M2035)), id 0)
                simple apply @option_join_proper (cost 0, pattern 
                @Proper
                  (forall _ : option (option (option ?M1993)),
                   option (option ?M1993))
                  (@respectful (option (option (option ?M1993)))
                     (option (option ?M1993))
                     (@equiv (option (option (option ?M1993)))
                        (@option_equiv (option (option ?M1993))
                           (@option_equiv (option ?M1993)
                              (@option_equiv ?M1993 ?M1994))))
                     (@equiv (option (option ?M1993))
                        (@option_equiv (option ?M1993)
                           (@option_equiv ?M1993 ?M1994))))
                  (@mjoin option option_join (option ?M1993)), id 0)
                simple apply @option_bind_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M1989, option ?M1991)
                     (_ : option ?M1989),
                   option ?M1991)
                  (@respectful (forall _ : ?M1989, option ?M1991)
                     (forall _ : option ?M1989, option ?M1991)
                     (@respectful ?M1989 (option ?M1991)
                        (@equiv ?M1989 ?M1990)
                        (@equiv (option ?M1991) (@option_equiv ?M1991 ?M1992)))
                     (@respectful (option ?M1989) 
                        (option ?M1991)
                        (@equiv (option ?M1989) (@option_equiv ?M1989 ?M1990))
                        (@equiv (option ?M1991) (@option_equiv ?M1991 ?M1992))))
                  (@mbind option option_bind ?M1989 ?M1991), id 0)
                simple apply @option_fmap_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M1985, ?M1987) (_ : option ?M1985),
                   option ?M1987)
                  (@respectful (forall _ : ?M1985, ?M1987)
                     (forall _ : option ?M1985, option ?M1987)
                     (@respectful ?M1985 ?M1987 (@equiv ?M1985 ?M1986)
                        (@equiv ?M1987 ?M1988))
                     (@respectful (option ?M1985) 
                        (option ?M1987)
                        (@equiv (option ?M1985) (@option_equiv ?M1985 ?M1986))
                        (@equiv (option ?M1987) (@option_equiv ?M1987 ?M1988))))
                  (@fmap option option_fmap ?M1985 ?M1987), id 0)
                simple apply @from_option_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M1965, ?M1967) 
                     (_ : ?M1967) (_ : option ?M1965),
                   ?M1967)
                  (@respectful (forall _ : ?M1965, ?M1967)
                     (forall (_ : ?M1967) (_ : option ?M1965), ?M1967)
                     (@respectful ?M1965 ?M1967 (@equiv ?M1965 ?M1966) ?M1968)
                     (@respectful ?M1967 (forall _ : option ?M1965, ?M1967)
                        ?M1968
                        (@respectful (option ?M1965) 
                           ?M1967
                           (@equiv (option ?M1965)
                              (@option_equiv ?M1965 ?M1966))
                           ?M1968)))
                  (@from_option ?M1965 ?M1967), id 0)
                simple apply @is_Some_proper (cost 0, pattern 
                @Proper (forall _ : option ?M1963, Prop)
                  (@respectful (option ?M1963) Prop
                     (@equiv (option ?M1963) (@option_equiv ?M1963 ?M1964))
                     iff)
                  (@is_Some ?M1963), id 0)
                simple apply @Some_proper (cost 0, pattern 
                @Proper (forall _ : ?M1959, option ?M1959)
                  (@respectful ?M1959 (option ?M1959) 
                     (@equiv ?M1959 ?M1960)
                     (@equiv (option ?M1959) (@option_equiv ?M1959 ?M1960)))
                  (@Some ?M1959), id 0)
                simple apply @option_Forall_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M1929, Prop) (_ : option ?M1929),
                   Prop)
                  (@respectful (forall _ : ?M1929, Prop)
                     (forall _ : option ?M1929, Prop)
                     (@pointwise_relation ?M1929 Prop iff)
                     (@respectful (option ?M1929) Prop 
                        (@eq (option ?M1929)) iff))
                  (@option_Forall ?M1929), id 0)
                exact Qreduction.Qminus'_comp_Proper (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  Qreduction.Qminus', id 0)
                exact Qreduction.Qmult'_comp_Proper (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  Qreduction.Qmult', id 0)
                exact Qreduction.Qplus'_comp_Proper (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  Qreduction.Qplus', id 0)
                exact Qreduction.Qred_comp_Proper (cost 0, pattern 
                @Proper (forall _ : QArith_base.Q, QArith_base.Q)
                  (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                     QArith_base.Qeq)
                  Qreduction.Qred, id 0)
                exact QArith_base.Qpower_comp (cost 0, pattern 
                @Proper (forall (_ : QArith_base.Q) (_ : Z), QArith_base.Q)
                  (@respectful QArith_base.Q (forall _ : Z, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful Z QArith_base.Q (@eq Z) QArith_base.Qeq))
                  QArith_base.Qpower, id 0)
                exact QArith_base.Qpower_positive_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : positive), QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : positive, QArith_base.Q) QArith_base.Qeq
                     (@respectful positive QArith_base.Q 
                        (@eq positive) QArith_base.Qeq))
                  QArith_base.Qpower_positive, id 0)
                exact QArith_base.Qleb_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q), bool)
                  (@respectful QArith_base.Q (forall _ : QArith_base.Q, bool)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q bool QArith_base.Qeq
                        (@eq bool)))
                  QArith_base.Qle_bool, id 0)
                exact QArith_base.Qeqb_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q), bool)
                  (@respectful QArith_base.Q (forall _ : QArith_base.Q, bool)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q bool QArith_base.Qeq
                        (@eq bool)))
                  QArith_base.Qeq_bool, id 0)
                exact QArith_base.Qlt_compat (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q), Prop)
                  (@respectful QArith_base.Q (forall _ : QArith_base.Q, Prop)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q Prop QArith_base.Qeq iff))
                  QArith_base.Qlt, id 0)
                exact QArith_base.Qle_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q), Prop)
                  (@respectful QArith_base.Q (forall _ : QArith_base.Q, Prop)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q Prop QArith_base.Qeq iff))
                  QArith_base.Qle, id 0)
                exact QArith_base.Qcompare_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q), comparison)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, comparison) QArith_base.Qeq
                     (@respectful QArith_base.Q comparison QArith_base.Qeq
                        (@eq comparison)))
                  QArith_base.Qcompare, id 0)
                exact QArith_base.Qdiv_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  QArith_base.Qdiv, id 0)
                exact QArith_base.Qinv_comp (cost 0, pattern 
                @Proper (forall _ : QArith_base.Q, QArith_base.Q)
                  (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                     QArith_base.Qeq)
                  QArith_base.Qinv, id 0)
                exact QArith_base.Qmult_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  QArith_base.Qmult, id 0)
                exact QArith_base.Qminus_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  QArith_base.Qminus, id 0)
                exact QArith_base.Qopp_comp (cost 0, pattern 
                @Proper (forall _ : QArith_base.Q, QArith_base.Q)
                  (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                     QArith_base.Qeq)
                  QArith_base.Qopp, id 0)
                exact QArith_base.Qplus_comp (cost 0, pattern 
                @Proper
                  (forall (_ : QArith_base.Q) (_ : QArith_base.Q),
                   QArith_base.Q)
                  (@respectful QArith_base.Q
                     (forall _ : QArith_base.Q, QArith_base.Q)
                     QArith_base.Qeq
                     (@respectful QArith_base.Q QArith_base.Q QArith_base.Qeq
                        QArith_base.Qeq))
                  QArith_base.Qplus, id 0)
                exact PositiveOrder.TO.lt_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  (fun x y : positive =>
                   @eq comparison (Positive_as_OT.compare x y) Lt), id 0)
                exact Positive_as_OT.min_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Positive_as_OT.min, id 0)
                exact Positive_as_OT.max_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Positive_as_OT.max, id 0)
                exact Positive_as_OT.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Positive_as_OT.le, id 0)
                exact Positive_as_OT.lt_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Positive_as_OT.lt, id 0)
                exact Positive_as_OT.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), bool)
                  (@respectful positive (forall _ : positive, bool)
                     (@eq positive)
                     (@respectful positive bool (@eq positive) (@eq bool)))
                  Positive_as_OT.eqb, id 0)
                exact Positive_as_DT.min_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Positive_as_DT.min, id 0)
                exact Positive_as_DT.max_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Positive_as_DT.max, id 0)
                exact Positive_as_DT.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Positive_as_DT.le, id 0)
                exact Positive_as_DT.lt_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Positive_as_DT.lt, id 0)
                exact Positive_as_DT.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), bool)
                  (@respectful positive (forall _ : positive, bool)
                     (@eq positive)
                     (@respectful positive bool (@eq positive) (@eq bool)))
                  Positive_as_DT.eqb, id 0)
                exact Z.ones_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.ones, id 0)
                exact Z.lnot_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.lnot, id 0)
                exact Z.clearbit_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.clearbit, id 0)
                exact Z.setbit_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.setbit, id 0)
                exact Z.ldiff_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.ldiff, id 0)
                exact Z.lor_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z), Z)
                                                 (@respectful Z
                                                 (forall _ : Z, Z) 
                                                 (@eq Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z))) Z.lor, id 0)
                exact Z.land_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z), Z)
                                                 (@respectful Z
                                                 (forall _ : Z, Z) 
                                                 (@eq Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z))) Z.land, id 0)
                exact Z.lxor_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z), Z)
                                                 (@respectful Z
                                                 (forall _ : Z, Z) 
                                                 (@eq Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z))) Z.lxor, id 0)
                exact Z.div2_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.div2, id 0)
                exact Z.shiftl_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.shiftl, id 0)
                exact Z.shiftr_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.shiftr, id 0)
                exact Z.testbit_eqf (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), bool)
                  (@respectful Z (forall _ : Z, bool) (@eq Z) Z.eqf)
                  Z.testbit, id 0)
                exact Z.b2z_wd (cost 0, pattern @Proper 
                                                 (forall _ : bool, Z)
                                                 (@respectful bool Z
                                                 (@eq bool) 
                                                 (@eq Z)) Z.b2z, id 0)
                exact Z.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), bool)
                  (@respectful Z (forall _ : Z, bool) 
                     (@eq Z) (@respectful Z bool (@eq Z) (@eq bool)))
                  Z.eqb, id 0)
                exact Z.lcm_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z), Z)
                                                 (@respectful Z
                                                 (forall _ : Z, Z) 
                                                 (@eq Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z))) Z.lcm, id 0)
                exact Z.Bezout_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z) (_ : Z), Prop)
                  (@respectful Z (forall (_ : Z) (_ : Z), Prop) 
                     (@eq Z)
                     (@respectful Z (forall _ : Z, Prop) 
                        (@eq Z) (@respectful Z Prop (@eq Z) iff)))
                  Z.Bezout, id 0)
                exact Z.gcd_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z), Z)
                                                 (@respectful Z
                                                 (forall _ : Z, Z) 
                                                 (@eq Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z))) Z.gcd, id 0)
                exact Z.divide_wd (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Prop)
                  (@respectful Z (forall _ : Z, Prop) 
                     (@eq Z) (@respectful Z Prop (@eq Z) iff))
                  Z.divide, id 0)
                exact Z.log2_up_wd (cost 0, pattern 
                @Proper (forall _ : Z, Z) (@respectful Z Z (@eq Z) (@eq Z))
                  Z.log2_up, id 0)
                exact Z.log2_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.log2, id 0)
                exact Z.sqrt_up_wd (cost 0, pattern 
                @Proper (forall _ : Z, Z) (@respectful Z Z (@eq Z) (@eq Z))
                  Z.sqrt_up, id 0)
                exact Z.sqrt_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.sqrt, id 0)
                exact Z.odd_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, bool)
                                                 (@respectful Z bool 
                                                 (@eq Z) 
                                                 (@eq bool)) Z.odd, id 0)
                exact Z.even_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, bool)
                                                 (@respectful Z bool 
                                                 (@eq Z) 
                                                 (@eq bool)) Z.even, id 0)
                exact Z.Odd_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Prop)
                                                 (@respectful Z Prop 
                                                 (@eq Z) iff) Z.Odd, id 0)
                exact Z.Even_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Prop)
                                                 (@respectful Z Prop 
                                                 (@eq Z) iff) Z.Even, id 0)
                exact Z.sgn_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.sgn, id 0)
                exact Z.abs_wd (cost 0, pattern @Proper 
                                                 (forall _ : Z, Z)
                                                 (@respectful Z Z 
                                                 (@eq Z) 
                                                 (@eq Z)) Z.abs, id 0)
                exact Z.min_compat (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.min, id 0)
                exact Z.max_compat (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Z)
                  (@respectful Z (forall _ : Z, Z) 
                     (@eq Z) (@respectful Z Z (@eq Z) (@eq Z)))
                  Z.max, id 0)
                exact Z.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : Z) (_ : Z), Prop)
                  (@respectful Z (forall _ : Z, Prop) 
                     (@eq Z) (@respectful Z Prop (@eq Z) iff))
                  Z.le, id 0)
                exact Z.le_wd (cost 0, pattern @Proper
                                                 (forall (_ : Z) (_ : Z),
                                                 Prop)
                                                 (@respectful Z
                                                 (forall _ : Z, Prop) 
                                                 (@eq Z)
                                                 (@respectful Z Prop 
                                                 (@eq Z) iff)) Z.le, id 0)
                exact N.lnot_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.lnot, id 0)
                exact N.ones_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N)) N.ones, id 0)
                exact N.clearbit_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.clearbit, id 0)
                exact N.setbit_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.setbit, id 0)
                exact N.ldiff_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.ldiff, id 0)
                exact N.lor_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.lor, id 0)
                exact N.land_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.land, id 0)
                exact N.lxor_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.lxor, id 0)
                exact N.div2_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N)) N.div2, id 0)
                exact N.shiftl_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.shiftl, id 0)
                exact N.shiftr_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.shiftr, id 0)
                exact N.testbit_eqf (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), bool)
                  (@respectful N (forall _ : N, bool) (@eq N) N.eqf)
                  N.testbit, id 0)
                exact N.b2n_proper (cost 0, pattern 
                @Proper (forall _ : bool, N)
                  (@respectful bool N (@eq bool) (@eq N)) N.b2n, id 0)
                exact N.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), bool)
                  (@respectful N (forall _ : N, bool) 
                     (@eq N) (@respectful N bool (@eq N) (@eq bool)))
                  N.eqb, id 0)
                exact N.lcm_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.lcm, id 0)
                exact N.Private_NLcmProp.lcm_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.Private_NLcmProp.lcm, id 0)
                exact N.Bezout_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N) (_ : N), Prop)
                  (@respectful N (forall (_ : N) (_ : N), Prop) 
                     (@eq N)
                     (@respectful N (forall _ : N, Prop) 
                        (@eq N) (@respectful N Prop (@eq N) iff)))
                  N.Bezout, id 0)
                exact N.gcd_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N), N)
                                                 (@respectful N
                                                 (forall _ : N, N) 
                                                 (@eq N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N))) N.gcd, id 0)
                exact N.divide_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), Prop)
                  (@respectful N (forall _ : N, Prop) 
                     (@eq N) (@respectful N Prop (@eq N) iff))
                  N.divide, id 0)
                exact N.Private_NZGcdProp.gcd_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.gcd, id 0)
                exact N.Private_NZGcdProp.divide_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), Prop)
                  (@respectful N (forall _ : N, Prop) 
                     (@eq N) (@respectful N Prop (@eq N) iff))
                  N.divide, id 0)
                exact N.log2_up_wd (cost 0, pattern 
                @Proper (forall _ : N, N) (@respectful N N (@eq N) (@eq N))
                  N.log2_up, id 0)
                exact N.log2_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, N)
                                                 (@respectful N N 
                                                 (@eq N) 
                                                 (@eq N)) N.log2, id 0)
                exact N.sqrt_up_wd (cost 0, pattern 
                @Proper (forall _ : N, N) (@respectful N N (@eq N) (@eq N))
                  N.sqrt_up, id 0)
                exact N.Private_NZSqrt.sqrt_wd (cost 0, pattern 
                @Proper (forall _ : N, N) (@respectful N N (@eq N) (@eq N))
                  N.sqrt, id 0)
                exact N.odd_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, bool)
                                                 (@respectful N bool 
                                                 (@eq N) 
                                                 (@eq bool)) N.odd, id 0)
                exact N.even_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, bool)
                                                 (@respectful N bool 
                                                 (@eq N) 
                                                 (@eq bool)) N.even, id 0)
                exact N.Odd_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, Prop)
                                                 (@respectful N Prop 
                                                 (@eq N) iff) N.Odd, id 0)
                exact N.Even_wd (cost 0, pattern @Proper 
                                                 (forall _ : N, Prop)
                                                 (@respectful N Prop 
                                                 (@eq N) iff) N.Even, id 0)
                exact N.min_compat (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.min, id 0)
                exact N.max_compat (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), N)
                  (@respectful N (forall _ : N, N) 
                     (@eq N) (@respectful N N (@eq N) (@eq N)))
                  N.max, id 0)
                exact N.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), Prop)
                  (@respectful N (forall _ : N, Prop) 
                     (@eq N) (@respectful N Prop (@eq N) iff))
                  N.le, id 0)
                exact N.lt_alt_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), Prop)
                  (@respectful N (forall _ : N, Prop) 
                     (@eq N) (@respectful N Prop (@eq N) iff))
                  N.lt_alt, id 0)
                exact N.le_alt_wd (cost 0, pattern 
                @Proper (forall (_ : N) (_ : N), Prop)
                  (@respectful N (forall _ : N, Prop) 
                     (@eq N) (@respectful N Prop (@eq N) iff))
                  N.le_alt, id 0)
                exact N.le_wd (cost 0, pattern @Proper
                                                 (forall (_ : N) (_ : N),
                                                 Prop)
                                                 (@respectful N
                                                 (forall _ : N, Prop) 
                                                 (@eq N)
                                                 (@respectful N Prop 
                                                 (@eq N) iff)) N.le, id 0)
                simple apply @N.recursion_wd (cost 0, pattern 
                @Proper
                  (forall (_ : ?M1505)
                     (_ : forall (_ : N) (_ : ?M1505), ?M1505) 
                     (_ : N),
                   ?M1505)
                  (@respectful ?M1505
                     (forall (_ : forall (_ : N) (_ : ?M1505), ?M1505)
                        (_ : N),
                      ?M1505)
                     ?M1506
                     (@respectful (forall (_ : N) (_ : ?M1505), ?M1505)
                        (forall _ : N, ?M1505)
                        (@respectful N (forall _ : ?M1505, ?M1505) 
                           (@eq N) (@respectful ?M1505 ?M1505 ?M1506 ?M1506))
                        (@respectful N ?M1505 (@eq N) ?M1506)))
                  (@N.recursion ?M1505), id 0)
                exact Pos.min_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Pos.min, id 0)
                exact Pos.max_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), positive)
                  (@respectful positive (forall _ : positive, positive)
                     (@eq positive)
                     (@respectful positive positive 
                        (@eq positive) (@eq positive)))
                  Pos.max, id 0)
                exact Pos.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Pos.le, id 0)
                exact Pos.lt_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), Prop)
                  (@respectful positive (forall _ : positive, Prop)
                     (@eq positive)
                     (@respectful positive Prop (@eq positive) iff))
                  Pos.lt, id 0)
                exact Pos.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : positive) (_ : positive), bool)
                  (@respectful positive (forall _ : positive, bool)
                     (@eq positive)
                     (@respectful positive bool (@eq positive) (@eq bool)))
                  Pos.eqb, id 0)
                simple apply @inr_proper (cost 0, pattern 
                @Proper (forall _ : ?M1481, sum ?M1479 ?M1481)
                  (@respectful ?M1481 (sum ?M1479 ?M1481)
                     (@equiv ?M1481 ?M1482)
                     (@equiv (sum ?M1479 ?M1481)
                        (@sum_equiv ?M1479 ?M1480 ?M1481 ?M1482)))
                  (@inr ?M1479 ?M1481), id 0)
                simple apply @inl_proper (cost 0, pattern 
                @Proper (forall _ : ?M1475, sum ?M1475 ?M1477)
                  (@respectful ?M1475 (sum ?M1475 ?M1477)
                     (@equiv ?M1475 ?M1476)
                     (@equiv (sum ?M1475 ?M1477)
                        (@sum_equiv ?M1475 ?M1476 ?M1477 ?M1478)))
                  (@inl ?M1475 ?M1477), id 0)
                simple apply @inr_proper' (cost 0, pattern 
                @Proper (forall _ : ?M1461, sum ?M1459 ?M1461)
                  (@respectful ?M1461 (sum ?M1459 ?M1461) 
                     ?M1462 (@sum_relation ?M1459 ?M1461 ?M1460 ?M1462))
                  (@inr ?M1459 ?M1461), id 0)
                simple apply @inl_proper' (cost 0, pattern 
                @Proper (forall _ : ?M1455, sum ?M1455 ?M1457)
                  (@respectful ?M1455 (sum ?M1455 ?M1457) 
                     ?M1456 (@sum_relation ?M1455 ?M1457 ?M1456 ?M1458))
                  (@inl ?M1455 ?M1457), id 0)
                simple apply @uncurry4_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M1397) (_ : ?M1399) 
                            (_ : ?M1401) (_ : ?M1403),
                          ?M1405)
                     (_ : prod (prod (prod ?M1397 ?M1399) ?M1401) ?M1403),
                   ?M1405)
                  (@respectful
                     (forall (_ : ?M1397) (_ : ?M1399) 
                        (_ : ?M1401) (_ : ?M1403),
                      ?M1405)
                     (forall
                        _ : prod (prod (prod ?M1397 ?M1399) ?M1401) ?M1403,
                      ?M1405)
                     (@respectful ?M1397
                        (forall (_ : ?M1399) (_ : ?M1401) (_ : ?M1403),
                         ?M1405)
                        (@equiv ?M1397 ?M1398)
                        (@respectful ?M1399
                           (forall (_ : ?M1401) (_ : ?M1403), ?M1405)
                           (@equiv ?M1399 ?M1400)
                           (@respectful ?M1401 (forall _ : ?M1403, ?M1405)
                              (@equiv ?M1401 ?M1402)
                              (@respectful ?M1403 
                                 ?M1405 (@equiv ?M1403 ?M1404)
                                 (@equiv ?M1405 ?M1406)))))
                     (@respectful
                        (prod (prod (prod ?M1397 ?M1399) ?M1401) ?M1403)
                        ?M1405
                        (@equiv
                           (prod (prod (prod ?M1397 ?M1399) ?M1401) ?M1403)
                           (@prod_equiv (prod (prod ?M1397 ?M1399) ?M1401)
                              (@prod_equiv (prod ?M1397 ?M1399)
                                 (@prod_equiv ?M1397 ?M1398 ?M1399 ?M1400)
                                 ?M1401 ?M1402)
                              ?M1403 ?M1404))
                        (@equiv ?M1405 ?M1406)))
                  (@uncurry4 ?M1397 ?M1399 ?M1401 ?M1403 ?M1405), id 0)
                simple apply @curry4_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall
                            _ : prod (prod (prod ?M1387 ?M1389) ?M1391)
                                  ?M1393,
                          ?M1395)
                     (_ : ?M1387) (_ : ?M1389) (_ : ?M1391) 
                     (_ : ?M1393),
                   ?M1395)
                  (@respectful
                     (forall
                        _ : prod (prod (prod ?M1387 ?M1389) ?M1391) ?M1393,
                      ?M1395)
                     (forall (_ : ?M1387) (_ : ?M1389) 
                        (_ : ?M1391) (_ : ?M1393),
                      ?M1395)
                     (@respectful
                        (prod (prod (prod ?M1387 ?M1389) ?M1391) ?M1393)
                        ?M1395
                        (@equiv
                           (prod (prod (prod ?M1387 ?M1389) ?M1391) ?M1393)
                           (@prod_equiv (prod (prod ?M1387 ?M1389) ?M1391)
                              (@prod_equiv (prod ?M1387 ?M1389)
                                 (@prod_equiv ?M1387 ?M1388 ?M1389 ?M1390)
                                 ?M1391 ?M1392)
                              ?M1393 ?M1394))
                        (@equiv ?M1395 ?M1396))
                     (@respectful ?M1387
                        (forall (_ : ?M1389) (_ : ?M1391) (_ : ?M1393),
                         ?M1395)
                        (@equiv ?M1387 ?M1388)
                        (@respectful ?M1389
                           (forall (_ : ?M1391) (_ : ?M1393), ?M1395)
                           (@equiv ?M1389 ?M1390)
                           (@respectful ?M1391 (forall _ : ?M1393, ?M1395)
                              (@equiv ?M1391 ?M1392)
                              (@respectful ?M1393 
                                 ?M1395 (@equiv ?M1393 ?M1394)
                                 (@equiv ?M1395 ?M1396))))))
                  (@curry4 ?M1387 ?M1389 ?M1391 ?M1393 ?M1395), id 0)
                simple apply @uncurry3_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M1379) (_ : ?M1381) (_ : ?M1383),
                          ?M1385)
                     (_ : prod (prod ?M1379 ?M1381) ?M1383),
                   ?M1385)
                  (@respectful
                     (forall (_ : ?M1379) (_ : ?M1381) (_ : ?M1383), ?M1385)
                     (forall _ : prod (prod ?M1379 ?M1381) ?M1383, ?M1385)
                     (@respectful ?M1379
                        (forall (_ : ?M1381) (_ : ?M1383), ?M1385)
                        (@equiv ?M1379 ?M1380)
                        (@respectful ?M1381 (forall _ : ?M1383, ?M1385)
                           (@equiv ?M1381 ?M1382)
                           (@respectful ?M1383 ?M1385 
                              (@equiv ?M1383 ?M1384) 
                              (@equiv ?M1385 ?M1386))))
                     (@respectful (prod (prod ?M1379 ?M1381) ?M1383) 
                        ?M1385
                        (@equiv (prod (prod ?M1379 ?M1381) ?M1383)
                           (@prod_equiv (prod ?M1379 ?M1381)
                              (@prod_equiv ?M1379 ?M1380 ?M1381 ?M1382)
                              ?M1383 ?M1384))
                        (@equiv ?M1385 ?M1386)))
                  (@uncurry3 ?M1379 ?M1381 ?M1383 ?M1385), id 0)
                simple apply @curry3_proper (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall _ : prod (prod ?M1371 ?M1373) ?M1375, ?M1377)
                     (_ : ?M1371) (_ : ?M1373) (_ : ?M1375),
                   ?M1377)
                  (@respectful
                     (forall _ : prod (prod ?M1371 ?M1373) ?M1375, ?M1377)
                     (forall (_ : ?M1371) (_ : ?M1373) (_ : ?M1375), ?M1377)
                     (@respectful (prod (prod ?M1371 ?M1373) ?M1375) 
                        ?M1377
                        (@equiv (prod (prod ?M1371 ?M1373) ?M1375)
                           (@prod_equiv (prod ?M1371 ?M1373)
                              (@prod_equiv ?M1371 ?M1372 ?M1373 ?M1374)
                              ?M1375 ?M1376))
                        (@equiv ?M1377 ?M1378))
                     (@respectful ?M1371
                        (forall (_ : ?M1373) (_ : ?M1375), ?M1377)
                        (@equiv ?M1371 ?M1372)
                        (@respectful ?M1373 (forall _ : ?M1375, ?M1377)
                           (@equiv ?M1373 ?M1374)
                           (@respectful ?M1375 ?M1377 
                              (@equiv ?M1375 ?M1376) 
                              (@equiv ?M1377 ?M1378)))))
                  (@curry3 ?M1371 ?M1373 ?M1375 ?M1377), id 0)
                simple apply @uncurry_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall (_ : ?M1365) (_ : ?M1367), ?M1369)
                     (_ : prod ?M1365 ?M1367),
                   ?M1369)
                  (@respectful (forall (_ : ?M1365) (_ : ?M1367), ?M1369)
                     (forall _ : prod ?M1365 ?M1367, ?M1369)
                     (@respectful ?M1365 (forall _ : ?M1367, ?M1369)
                        (@equiv ?M1365 ?M1366)
                        (@respectful ?M1367 ?M1369 
                           (@equiv ?M1367 ?M1368) 
                           (@equiv ?M1369 ?M1370)))
                     (@respectful (prod ?M1365 ?M1367) 
                        ?M1369
                        (@equiv (prod ?M1365 ?M1367)
                           (@prod_equiv ?M1365 ?M1366 ?M1367 ?M1368))
                        (@equiv ?M1369 ?M1370)))
                  (@uncurry ?M1365 ?M1367 ?M1369), id 0)
                simple apply @curry_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : prod ?M1359 ?M1361, ?M1363)
                     (_ : ?M1359) (_ : ?M1361),
                   ?M1363)
                  (@respectful (forall _ : prod ?M1359 ?M1361, ?M1363)
                     (forall (_ : ?M1359) (_ : ?M1361), ?M1363)
                     (@respectful (prod ?M1359 ?M1361) 
                        ?M1363
                        (@equiv (prod ?M1359 ?M1361)
                           (@prod_equiv ?M1359 ?M1360 ?M1361 ?M1362))
                        (@equiv ?M1363 ?M1364))
                     (@respectful ?M1359 (forall _ : ?M1361, ?M1363)
                        (@equiv ?M1359 ?M1360)
                        (@respectful ?M1361 ?M1363 
                           (@equiv ?M1361 ?M1362) 
                           (@equiv ?M1363 ?M1364))))
                  (@curry ?M1359 ?M1361 ?M1363), id 0)
                simple apply @prod_swap_proper (cost 0, pattern 
                @Proper (forall _ : prod ?M1355 ?M1357, prod ?M1357 ?M1355)
                  (@respectful (prod ?M1355 ?M1357) 
                     (prod ?M1357 ?M1355)
                     (@equiv (prod ?M1355 ?M1357)
                        (@prod_equiv ?M1355 ?M1356 ?M1357 ?M1358))
                     (@equiv (prod ?M1357 ?M1355)
                        (@prod_equiv ?M1357 ?M1358 ?M1355 ?M1356)))
                  (@prod_swap ?M1355 ?M1357), id 0)
                simple apply @snd_proper (cost 0, pattern 
                @Proper (forall _ : prod ?M1351 ?M1353, ?M1353)
                  (@respectful (prod ?M1351 ?M1353) 
                     ?M1353
                     (@equiv (prod ?M1351 ?M1353)
                        (@prod_equiv ?M1351 ?M1352 ?M1353 ?M1354))
                     (@equiv ?M1353 ?M1354))
                  (@snd ?M1351 ?M1353), id 0)
                simple apply @fst_proper (cost 0, pattern 
                @Proper (forall _ : prod ?M1347 ?M1349, ?M1347)
                  (@respectful (prod ?M1347 ?M1349) 
                     ?M1347
                     (@equiv (prod ?M1347 ?M1349)
                        (@prod_equiv ?M1347 ?M1348 ?M1349 ?M1350))
                     (@equiv ?M1347 ?M1348))
                  (@fst ?M1347 ?M1349), id 0)
                simple apply @pair_proper (cost 0, pattern 
                @Proper
                  (forall (_ : ?M1339) (_ : ?M1341), prod ?M1339 ?M1341)
                  (@respectful ?M1339 (forall _ : ?M1341, prod ?M1339 ?M1341)
                     (@equiv ?M1339 ?M1340)
                     (@respectful ?M1341 (prod ?M1339 ?M1341)
                        (@equiv ?M1341 ?M1342)
                        (@equiv (prod ?M1339 ?M1341)
                           (@prod_equiv ?M1339 ?M1340 ?M1341 ?M1342))))
                  (@pair ?M1339 ?M1341), id 0)
                simple apply @uncurry4_proper' (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M1319) (_ : ?M1321) 
                            (_ : ?M1323) (_ : ?M1325),
                          ?M1327)
                     (_ : prod (prod (prod ?M1319 ?M1321) ?M1323) ?M1325),
                   ?M1327)
                  (@respectful
                     (forall (_ : ?M1319) (_ : ?M1321) 
                        (_ : ?M1323) (_ : ?M1325),
                      ?M1327)
                     (forall
                        _ : prod (prod (prod ?M1319 ?M1321) ?M1323) ?M1325,
                      ?M1327)
                     (@respectful ?M1319
                        (forall (_ : ?M1321) (_ : ?M1323) (_ : ?M1325),
                         ?M1327)
                        ?M1320
                        (@respectful ?M1321
                           (forall (_ : ?M1323) (_ : ?M1325), ?M1327) 
                           ?M1322
                           (@respectful ?M1323 (forall _ : ?M1325, ?M1327)
                              ?M1324
                              (@respectful ?M1325 ?M1327 ?M1326 ?M1328))))
                     (@respectful
                        (prod (prod (prod ?M1319 ?M1321) ?M1323) ?M1325)
                        ?M1327
                        (@prod_relation (prod (prod ?M1319 ?M1321) ?M1323)
                           ?M1325
                           (@prod_relation (prod ?M1319 ?M1321) 
                              ?M1323
                              (@prod_relation ?M1319 ?M1321 ?M1320 ?M1322)
                              ?M1324)
                           ?M1326)
                        ?M1328))
                  (@uncurry4 ?M1319 ?M1321 ?M1323 ?M1325 ?M1327), id 0)
                simple apply @curry4_proper' (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall
                            _ : prod (prod (prod ?M1309 ?M1311) ?M1313)
                                  ?M1315,
                          ?M1317)
                     (_ : ?M1309) (_ : ?M1311) (_ : ?M1313) 
                     (_ : ?M1315),
                   ?M1317)
                  (@respectful
                     (forall
                        _ : prod (prod (prod ?M1309 ?M1311) ?M1313) ?M1315,
                      ?M1317)
                     (forall (_ : ?M1309) (_ : ?M1311) 
                        (_ : ?M1313) (_ : ?M1315),
                      ?M1317)
                     (@respectful
                        (prod (prod (prod ?M1309 ?M1311) ?M1313) ?M1315)
                        ?M1317
                        (@prod_relation (prod (prod ?M1309 ?M1311) ?M1313)
                           ?M1315
                           (@prod_relation (prod ?M1309 ?M1311) 
                              ?M1313
                              (@prod_relation ?M1309 ?M1311 ?M1310 ?M1312)
                              ?M1314)
                           ?M1316)
                        ?M1318)
                     (@respectful ?M1309
                        (forall (_ : ?M1311) (_ : ?M1313) (_ : ?M1315),
                         ?M1317)
                        ?M1310
                        (@respectful ?M1311
                           (forall (_ : ?M1313) (_ : ?M1315), ?M1317) 
                           ?M1312
                           (@respectful ?M1313 (forall _ : ?M1315, ?M1317)
                              ?M1314
                              (@respectful ?M1315 ?M1317 ?M1316 ?M1318)))))
                  (@curry4 ?M1309 ?M1311 ?M1313 ?M1315 ?M1317), id 0)
                simple apply @uncurry3_proper' (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M1301) (_ : ?M1303) (_ : ?M1305),
                          ?M1307)
                     (_ : prod (prod ?M1301 ?M1303) ?M1305),
                   ?M1307)
                  (@respectful
                     (forall (_ : ?M1301) (_ : ?M1303) (_ : ?M1305), ?M1307)
                     (forall _ : prod (prod ?M1301 ?M1303) ?M1305, ?M1307)
                     (@respectful ?M1301
                        (forall (_ : ?M1303) (_ : ?M1305), ?M1307) 
                        ?M1302
                        (@respectful ?M1303 (forall _ : ?M1305, ?M1307)
                           ?M1304 (@respectful ?M1305 ?M1307 ?M1306 ?M1308)))
                     (@respectful (prod (prod ?M1301 ?M1303) ?M1305) 
                        ?M1307
                        (@prod_relation (prod ?M1301 ?M1303) 
                           ?M1305
                           (@prod_relation ?M1301 ?M1303 ?M1302 ?M1304)
                           ?M1306)
                        ?M1308))
                  (@uncurry3 ?M1301 ?M1303 ?M1305 ?M1307), id 0)
                simple apply @curry3_proper' (cost 0, pattern 
                @Proper
                  (forall
                     (_ : forall _ : prod (prod ?M1293 ?M1295) ?M1297, ?M1299)
                     (_ : ?M1293) (_ : ?M1295) (_ : ?M1297),
                   ?M1299)
                  (@respectful
                     (forall _ : prod (prod ?M1293 ?M1295) ?M1297, ?M1299)
                     (forall (_ : ?M1293) (_ : ?M1295) (_ : ?M1297), ?M1299)
                     (@respectful (prod (prod ?M1293 ?M1295) ?M1297) 
                        ?M1299
                        (@prod_relation (prod ?M1293 ?M1295) 
                           ?M1297
                           (@prod_relation ?M1293 ?M1295 ?M1294 ?M1296)
                           ?M1298)
                        ?M1300)
                     (@respectful ?M1293
                        (forall (_ : ?M1295) (_ : ?M1297), ?M1299) 
                        ?M1294
                        (@respectful ?M1295 (forall _ : ?M1297, ?M1299)
                           ?M1296 (@respectful ?M1297 ?M1299 ?M1298 ?M1300))))
                  (@curry3 ?M1293 ?M1295 ?M1297 ?M1299), id 0)
                simple apply @uncurry_proper' (cost 0, pattern 
                @Proper
                  (forall (_ : forall (_ : ?M1287) (_ : ?M1289), ?M1291)
                     (_ : prod ?M1287 ?M1289),
                   ?M1291)
                  (@respectful (forall (_ : ?M1287) (_ : ?M1289), ?M1291)
                     (forall _ : prod ?M1287 ?M1289, ?M1291)
                     (@respectful ?M1287 (forall _ : ?M1289, ?M1291) 
                        ?M1288 (@respectful ?M1289 ?M1291 ?M1290 ?M1292))
                     (@respectful (prod ?M1287 ?M1289) 
                        ?M1291 (@prod_relation ?M1287 ?M1289 ?M1288 ?M1290)
                        ?M1292))
                  (@uncurry ?M1287 ?M1289 ?M1291), id 0)
                simple apply @curry_proper' (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : prod ?M1281 ?M1283, ?M1285)
                     (_ : ?M1281) (_ : ?M1283),
                   ?M1285)
                  (@respectful (forall _ : prod ?M1281 ?M1283, ?M1285)
                     (forall (_ : ?M1281) (_ : ?M1283), ?M1285)
                     (@respectful (prod ?M1281 ?M1283) 
                        ?M1285 (@prod_relation ?M1281 ?M1283 ?M1282 ?M1284)
                        ?M1286)
                     (@respectful ?M1281 (forall _ : ?M1283, ?M1285) 
                        ?M1282 (@respectful ?M1283 ?M1285 ?M1284 ?M1286)))
                  (@curry ?M1281 ?M1283 ?M1285), id 0)
                simple apply @prod_swap_proper' (cost 0, pattern 
                @Proper (forall _ : prod ?M1277 ?M1279, prod ?M1279 ?M1277)
                  (@respectful (prod ?M1277 ?M1279) 
                     (prod ?M1279 ?M1277)
                     (@prod_relation ?M1277 ?M1279 ?M1278 ?M1280)
                     (@prod_relation ?M1279 ?M1277 ?M1280 ?M1278))
                  (@prod_swap ?M1277 ?M1279), id 0)
                simple apply @snd_proper' (cost 0, pattern 
                @Proper (forall _ : prod ?M1273 ?M1275, ?M1275)
                  (@respectful (prod ?M1273 ?M1275) 
                     ?M1275 (@prod_relation ?M1273 ?M1275 ?M1274 ?M1276)
                     ?M1276)
                  (@snd ?M1273 ?M1275), id 0)
                simple apply @fst_proper' (cost 0, pattern 
                @Proper (forall _ : prod ?M1269 ?M1271, ?M1269)
                  (@respectful (prod ?M1269 ?M1271) 
                     ?M1269 (@prod_relation ?M1269 ?M1271 ?M1270 ?M1272)
                     ?M1270)
                  (@fst ?M1269 ?M1271), id 0)
                simple apply @pair_proper' (cost 0, pattern 
                @Proper
                  (forall (_ : ?M1261) (_ : ?M1263), prod ?M1261 ?M1263)
                  (@respectful ?M1261 (forall _ : ?M1263, prod ?M1261 ?M1263)
                     ?M1262
                     (@respectful ?M1263 (prod ?M1261 ?M1263) 
                        ?M1264 (@prod_relation ?M1261 ?M1263 ?M1262 ?M1264)))
                  (@pair ?M1261 ?M1263), id 0)
                simple apply Permutation_flat_map (cost 0, pattern 
                @Proper (forall _ : list ?M1083, list ?M1084)
                  (@respectful (list ?M1083) (list ?M1084)
                     (@Permutation ?M1083) (@Permutation ?M1084))
                  (@flat_map ?M1083 ?M1084 ?M1085), id 0)
                simple apply Permutation_map' (cost 0, pattern 
                @Proper (forall _ : list ?M1080, list ?M1081)
                  (@respectful (list ?M1080) (list ?M1081)
                     (@Permutation ?M1080) (@Permutation ?M1081))
                  (@map ?M1080 ?M1081 ?M1082), id 0)
                simple apply Permutation_NoDup' (cost 0, pattern 
                @Proper (forall _ : list ?M1079, Prop)
                  (@respectful (list ?M1079) Prop (@Permutation ?M1079) iff)
                  (@List.NoDup ?M1079), id 0)
                simple apply Permutation_Exists (cost 0, pattern 
                @Proper (forall _ : list ?M1077, Prop)
                  (@respectful (list ?M1077) Prop (@Permutation ?M1077) impl)
                  (@Exists ?M1077 ?M1078), id 0)
                simple apply Permutation_Forall (cost 0, pattern 
                @Proper (forall _ : list ?M1075, Prop)
                  (@respectful (list ?M1075) Prop (@Permutation ?M1075) impl)
                  (@Forall ?M1075 ?M1076), id 0)
                simple apply Permutation_rev' (cost 0, pattern 
                @Proper (forall _ : list ?M1073, list ?M1073)
                  (@respectful (list ?M1073) (list ?M1073)
                     (@Permutation ?M1073) (@Permutation ?M1073))
                  (@rev ?M1073), id 0)
                simple apply Permutation_in' (cost 0, pattern 
                @Proper (forall (_ : ?M1072) (_ : list ?M1072), Prop)
                  (@respectful ?M1072 (forall _ : list ?M1072, Prop)
                     (@eq ?M1072)
                     (@respectful (list ?M1072) Prop 
                        (@Permutation ?M1072) iff))
                  (@In ?M1072), id 0)
                simple apply @Proper_map (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M643, ?M644) (_ : list ?M643),
                   list ?M644)
                  (@respectful (forall _ : ?M643, ?M644)
                     (forall _ : list ?M643, list ?M644)
                     (@pointwise_relation ?M643 ?M644 (@eq ?M644))
                     (@respectful (list ?M643) (list ?M644)
                        (@eq (list ?M643)) (@eq (list ?M644))))
                  (@map ?M643 ?M644), id 0)
                exact Nat.lnot_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.lnot, id 0)
                exact Nat.ones_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.ones, id 0)
                exact Nat.clearbit_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.clearbit, id 0)
                exact Nat.setbit_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.setbit, id 0)
                exact Nat.ldiff_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.ldiff, id 0)
                exact Nat.lor_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.lor, id 0)
                exact Nat.land_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.land, id 0)
                exact Nat.lxor_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.lxor, id 0)
                exact Nat.div2_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.div2, id 0)
                exact Nat.shiftl_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.shiftl, id 0)
                exact Nat.shiftr_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.shiftr, id 0)
                exact Nat.testbit_eqf (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), bool)
                  (@respectful nat (forall _ : nat, bool) (@eq nat) Nat.eqf)
                  Nat.testbit, id 0)
                exact Nat.b2n_proper (cost 0, pattern 
                @Proper (forall _ : bool, nat)
                  (@respectful bool nat (@eq bool) (@eq nat)) Nat.b2n, id 0)
                exact Nat.eqb_compat (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), bool)
                  (@respectful nat (forall _ : nat, bool) 
                     (@eq nat) (@respectful nat bool (@eq nat) (@eq bool)))
                  Nat.eqb, id 0)
                exact Nat.lcm_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.lcm, id 0)
                exact Nat.Private_NLcmProp.lcm_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.Private_NLcmProp.lcm, id 0)
                exact Nat.Bezout_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall (_ : nat) (_ : nat), Prop)
                     (@eq nat)
                     (@respectful nat (forall _ : nat, Prop) 
                        (@eq nat) (@respectful nat Prop (@eq nat) iff)))
                  Nat.Bezout, id 0)
                exact Nat.gcd_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.gcd, id 0)
                exact Nat.divide_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall _ : nat, Prop) 
                     (@eq nat) (@respectful nat Prop (@eq nat) iff))
                  Nat.divide, id 0)
                exact Nat.Private_NZGcdProp.gcd_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.gcd, id 0)
                exact Nat.Private_NZGcdProp.divide_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall _ : nat, Prop) 
                     (@eq nat) (@respectful nat Prop (@eq nat) iff))
                  Nat.divide, id 0)
                exact Nat.log2_up_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.log2_up, id 0)
                exact Nat.log2_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.log2, id 0)
                exact Nat.sqrt_up_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.sqrt_up, id 0)
                exact Nat.Private_NZSqrt.sqrt_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.sqrt, id 0)
                exact Nat.odd_wd (cost 0, pattern 
                @Proper (forall _ : nat, bool)
                  (@respectful nat bool (@eq nat) (@eq bool)) Nat.odd, id 0)
                exact Nat.even_wd (cost 0, pattern 
                @Proper (forall _ : nat, bool)
                  (@respectful nat bool (@eq nat) (@eq bool)) Nat.even, id 0)
                exact Nat.Odd_wd (cost 0, pattern 
                @Proper (forall _ : nat, Prop)
                  (@respectful nat Prop (@eq nat) iff) Nat.Odd, id 0)
                exact Nat.Even_wd (cost 0, pattern 
                @Proper (forall _ : nat, Prop)
                  (@respectful nat Prop (@eq nat) iff) Nat.Even, id 0)
                exact Nat.min_compat (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.min, id 0)
                exact Nat.max_compat (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.max, id 0)
                exact Nat.Proper_instance_0 (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall _ : nat, Prop) 
                     (@eq nat) (@respectful nat Prop (@eq nat) iff))
                  le, id 0)
                exact Nat.lt_alt_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall _ : nat, Prop) 
                     (@eq nat) (@respectful nat Prop (@eq nat) iff))
                  Nat.lt_alt, id 0)
                exact Nat.le_alt_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), Prop)
                  (@respectful nat (forall _ : nat, Prop) 
                     (@eq nat) (@respectful nat Prop (@eq nat) iff))
                  Nat.le_alt, id 0)
                exact Nat.le_wd (cost 0, pattern @Proper
                                                 (forall (_ : nat) (_ : nat),
                                                 Prop)
                                                 (@respectful nat
                                                 (forall _ : nat, Prop)
                                                 (@eq nat)
                                                 (@respectful nat Prop
                                                 (@eq nat) iff)) le, id 0)
                simple apply @Nat.recursion_wd (cost 0, pattern 
                @Proper
                  (forall (_ : ?M581)
                     (_ : forall (_ : nat) (_ : ?M581), ?M581) 
                     (_ : nat),
                   ?M581)
                  (@respectful ?M581
                     (forall (_ : forall (_ : nat) (_ : ?M581), ?M581)
                        (_ : nat),
                      ?M581)
                     ?M582
                     (@respectful (forall (_ : nat) (_ : ?M581), ?M581)
                        (forall _ : nat, ?M581)
                        (@respectful nat (forall _ : ?M581, ?M581) 
                           (@eq nat) (@respectful ?M581 ?M581 ?M582 ?M582))
                        (@respectful nat ?M581 (@eq nat) ?M582)))
                  (@Nat.recursion ?M581), id 0)
                exact Nat.testbit_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), bool)
                  (@respectful nat (forall _ : nat, bool) 
                     (@eq nat) (@respectful nat bool (@eq nat) (@eq bool)))
                  Nat.testbit, id 0)
                exact Nat.lt_wd (cost 0, pattern @Proper
                                                 (forall (_ : nat) (_ : nat),
                                                 Prop)
                                                 (@respectful nat
                                                 (forall _ : nat, Prop)
                                                 (@eq nat)
                                                 (@respectful nat Prop
                                                 (@eq nat) iff)) lt, id 0)
                exact Nat.mod_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.modulo, id 0)
                exact Nat.div_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.div, id 0)
                exact Nat.pow_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Nat.pow, id 0)
                exact Nat.mul_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Init.Nat.mul, id 0)
                exact Nat.sub_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Init.Nat.sub, id 0)
                exact Nat.add_wd (cost 0, pattern 
                @Proper (forall (_ : nat) (_ : nat), nat)
                  (@respectful nat (forall _ : nat, nat) 
                     (@eq nat) (@respectful nat nat (@eq nat) (@eq nat)))
                  Init.Nat.add, id 0)
                exact Nat.pred_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) Nat.pred, id 0)
                exact Nat.succ_wd (cost 0, pattern 
                @Proper (forall _ : nat, nat)
                  (@respectful nat nat (@eq nat) (@eq nat)) S, id 0)
                simple apply @Morphisms_Prop.well_founded_morphism (cost 0, pattern 
                @Proper (forall _ : relation ?M504, Prop)
                  (@respectful (relation ?M504) Prop
                     (@relation_equivalence ?M504) iff)
                  (@well_founded ?M504), id 0)
                simple apply @Morphisms_Prop.Acc_rel_morphism (cost 0, pattern 
                @Proper (forall (_ : relation ?M503) (_ : ?M503), Prop)
                  (@respectful (relation ?M503) (forall _ : ?M503, Prop)
                     (@relation_equivalence ?M503)
                     (@respectful ?M503 Prop (@eq ?M503) iff))
                  (@Acc ?M503), id 0)
                simple apply @Morphisms_Prop.all_iff_morphism (cost 0, pattern 
                @Proper (forall _ : forall _ : ?M495, Prop, Prop)
                  (@respectful (forall _ : ?M495, Prop) Prop
                     (@pointwise_relation ?M495 Prop iff) iff)
                  (@all ?M495), id 0)
                simple apply @Morphisms_Prop.ex_iff_morphism (cost 0, pattern 
                @Proper (forall _ : forall _ : ?M492, Prop, Prop)
                  (@respectful (forall _ : ?M492, Prop) Prop
                     (@pointwise_relation ?M492 Prop iff) iff)
                  (@ex ?M492), id 0)
                exact Morphisms_Prop.iff_iff_iff_impl_morphism (cost 0, pattern 
                @Proper (forall (_ : Prop) (_ : Prop), Prop)
                  (@respectful Prop (forall _ : Prop, Prop) iff
                     (@respectful Prop Prop iff iff))
                  impl, id 0)
                exact Morphisms_Prop.or_iff_morphism (cost 0, pattern 
                @Proper (forall (_ : Prop) (_ : Prop), Prop)
                  (@respectful Prop (forall _ : Prop, Prop) iff
                     (@respectful Prop Prop iff iff))
                  or, id 0)
                exact Morphisms_Prop.and_iff_morphism (cost 0, pattern 
                @Proper (forall (_ : Prop) (_ : Prop), Prop)
                  (@respectful Prop (forall _ : Prop, Prop) iff
                     (@respectful Prop Prop iff iff))
                  and, id 0)
                exact Morphisms_Prop.not_iff_morphism (cost 0, pattern 
                @Proper (forall _ : Prop, Prop)
                  (@respectful Prop Prop iff iff) not, id 0)
                simple apply @proper_proper (cost 0, pattern 
                @Proper (forall (_ : relation ?M325) (_ : ?M325), Prop)
                  (@respectful (relation ?M325) (forall _ : ?M325, Prop)
                     (@relation_equivalence ?M325)
                     (@respectful ?M325 Prop (@eq ?M325) iff))
                  (@Proper ?M325), id 0)
                simple apply @respectful_morphism (cost 0, pattern 
                @Proper
                  (forall (_ : relation ?M323) (_ : relation ?M324),
                   relation (forall _ : ?M323, ?M324))
                  (@respectful (relation ?M323)
                     (forall _ : relation ?M324,
                      relation (forall _ : ?M323, ?M324))
                     (@relation_equivalence ?M323)
                     (@respectful (relation ?M324)
                        (relation (forall _ : ?M323, ?M324))
                        (@relation_equivalence ?M324)
                        (@relation_equivalence (forall _ : ?M323, ?M324))))
                  (@respectful ?M323 ?M324), id 0)
                simple apply @compose_proper (cost 0, pattern 
                @Proper
                  (forall (_ : forall _ : ?M314, ?M315)
                     (_ : forall _ : ?M313, ?M314) 
                     (_ : ?M313),
                   ?M315)
                  (@respectful (forall _ : ?M314, ?M315)
                     (forall (_ : forall _ : ?M313, ?M314) (_ : ?M313), ?M315)
                     (@respectful ?M314 ?M315 ?M317 ?M318)
                     (@respectful (forall _ : ?M313, ?M314)
                        (forall _ : ?M313, ?M315)
                        (@respectful ?M313 ?M314 ?M316 ?M317)
                        (@respectful ?M313 ?M315 ?M316 ?M318)))
                  (@compose ?M313 ?M314 ?M315), id 0)
                simple apply @proper_subrelation_proper (cost 0, pattern 
                @Proper (forall (_ : relation ?M278) (_ : ?M278), Prop)
                  (@respectful (relation ?M278) (forall _ : ?M278, Prop)
                     (@subrelation ?M278)
                     (@respectful ?M278 Prop (@eq ?M278) impl))
                  (@Proper ?M278), id 0)
                simple apply @lookup_total_proper (cost 1, pattern 
                @Proper (forall _ : ?M4177 ?M4179, ?M4179)
                  (@respectful (?M4177 ?M4179) ?M4179
                     (@equiv (?M4177 ?M4179)
                        (@map_equiv ?M4176 ?M4177 ?M4178 ?M4179 ?M4180))
                     (@equiv ?M4179 ?M4180))
                  (@lookup_total ?M4176 ?M4179 (?M4177 ?M4179)
                     (@map_lookup_total ?M4176 ?M4179 
                        ?M4177 (?M4178 ?M4179) ?M4182)
                     ?M4181), id 0)
                simple apply @list_to_set_perm (cost 1, pattern 
                @Proper (forall _ : list ?M3212, ?M3213)
                  (@respectful (list ?M3212) ?M3213 
                     (@Permutation ?M3212)
                     (@equiv ?M3213
                        (@set_equiv_instance ?M3212 ?M3213 ?M3214)))
                  (@list_to_set ?M3212 ?M3213 ?M3216 ?M3215 ?M3217), id 0)
                simple apply @list_filter_proper (cost 1, pattern 
                @Proper (forall _ : list ?M2282, list ?M2282)
                  (@respectful (list ?M2282) (list ?M2282)
                     (@equiv (list ?M2282) (@list_equiv ?M2282 ?M2283))
                     (@equiv (list ?M2282) (@list_equiv ?M2282 ?M2283)))
                  (@filter ?M2282 (list ?M2282) (@list_filter ?M2282) 
                     ?M2284 ?M2285), id 0)
                simple apply @list_lookup_total_proper (cost 1, pattern 
                @Proper (forall _ : list ?M2264, ?M2264)
                  (@respectful (list ?M2264) ?M2264
                     (@equiv (list ?M2264) (@list_equiv ?M2264 ?M2265))
                     (@equiv ?M2264 ?M2265))
                  (@lookup_total nat ?M2264 (list ?M2264)
                     (@list_lookup_total ?M2264 ?M2266) 
                     ?M2267), id 0)
                simple apply @Proper_instance_13 (cost 1, pattern 
                @Proper (forall _ : list ?M2225, list ?M2225)
                  (@respectful (list ?M2225) (list ?M2225)
                     (@Forall2 ?M2225 ?M2225 ?M2226)
                     (@Forall2 ?M2225 ?M2225 ?M2226))
                  (@filter ?M2225 (list ?M2225) (@list_filter ?M2225) 
                     ?M2227 ?M2228), id 0)
                simple apply @const_proper (cost 1, pattern 
                @Proper (forall _ : ?M1173, ?M1175)
                  (@respectful ?M1173 ?M1175 ?M1174 ?M1176)
                  (fun _ : ?M1173 => ?M1177), id 0)
                simple apply @Morphisms_Prop.all_flip_impl_morphism (cost 1, pattern 
                @Proper (forall _ : forall _ : ?M497, Prop, Prop)
                  (@respectful (forall _ : ?M497, Prop) Prop
                     (@pointwise_relation ?M497 Prop
                        (@flip Prop Prop Prop impl))
                     (@flip Prop Prop Prop impl))
                  (@all ?M497), id 0)
                simple apply @Morphisms_Prop.all_impl_morphism (cost 1, pattern 
                @Proper (forall _ : forall _ : ?M496, Prop, Prop)
                  (@respectful (forall _ : ?M496, Prop) Prop
                     (@pointwise_relation ?M496 Prop impl) impl)
                  (@all ?M496), id 0)
                simple apply @Morphisms_Prop.ex_flip_impl_morphism (cost 1, pattern 
                @Proper (forall _ : forall _ : ?M494, Prop, Prop)
                  (@respectful (forall _ : ?M494, Prop) Prop
                     (@pointwise_relation ?M494 Prop
                        (@flip Prop Prop Prop impl))
                     (@flip Prop Prop Prop impl))
                  (@ex ?M494), id 0)
                simple apply @Morphisms_Prop.ex_impl_morphism (cost 1, pattern 
                @Proper (forall _ : forall _ : ?M493, Prop, Prop)
                  (@respectful (forall _ : ?M493, Prop) Prop
                     (@pointwise_relation ?M493 Prop impl) impl)
                  (@ex ?M493), id 0)
                exact Morphisms_Prop.or_impl_morphism (cost 1, pattern 
                @Proper (forall (_ : Prop) (_ : Prop), Prop)
                  (@respectful Prop (forall _ : Prop, Prop) impl
                     (@respectful Prop Prop impl impl))
                  or, id 0)
                exact Morphisms_Prop.and_impl_morphism (cost 1, pattern 
                @Proper (forall (_ : Prop) (_ : Prop), Prop)
                  (@respectful Prop (forall _ : Prop, Prop) impl
                     (@respectful Prop Prop impl impl))
                  and, id 0)
                exact Morphisms_Prop.not_impl_morphism (cost 1, pattern 
                @Proper (forall _ : Prop, Prop)
                  (@respectful Prop Prop (@flip Prop Prop Prop impl) impl)
                  not, id 0)
                (*external*) (apply @flip_proper) (cost 1, pattern 
                @Proper _ _ (@flip _ _ _ _), id 0)
                (*external*) (apply @complement_proper) (cost 1, pattern 
                @Proper _ _ (@complement _ _), id 0)
                simple apply @PER_morphism (cost 1, pattern 
                @Proper (forall (_ : ?M310) (_ : ?M310), Prop)
                  (@respectful ?M310 (forall _ : ?M310, Prop) 
                     ?M311 (@respectful ?M310 Prop ?M311 iff))
                  ?M311, id 0)
                simple apply @trans_contra_co_morphism (cost 1, pattern 
                @Proper (forall (_ : ?M284) (_ : ?M284), Prop)
                  (@respectful ?M284 (forall _ : ?M284, Prop)
                     (@flip ?M284 ?M284 Prop ?M285)
                     (@respectful ?M284 Prop ?M285 impl))
                  ?M285, id 0)
                simple apply @subrelation_id_proper (cost 1, pattern 
                @Proper (forall _ : ?M274, ?M274)
                  (@respectful ?M274 ?M274 ?M275 ?M276) 
                  (@id ?M274), id 0)
                simple eapply @union_list_permutation_proper (cost 2, pattern 
                @Proper (forall _ : list ?M3034, ?M3034)
                  (@respectful (list ?M3034) ?M3034 
                     (@Permutation ?M3034)
                     (@equiv ?M3034
                        (@set_equiv_instance ?M3033 ?M3034 ?M3035)))
                  (@union_list ?M3034 ?M3036 ?M3038), id 0)
                simple eapply @union_list_proper (cost 2, pattern 
                @Proper (forall _ : list ?M2592, ?M2592)
                  (@respectful (list ?M2592) ?M2592
                     (@equiv (list ?M2592)
                        (@list_equiv ?M2592
                           (@set_equiv_instance ?M2591 ?M2592 ?M2593)))
                     (@equiv ?M2592
                        (@set_equiv_instance ?M2591 ?M2592 ?M2593)))
                  (@union_list ?M2592 ?M2594 ?M2596), id 0)
                simple apply @Morphisms_Prop.Acc_pt_morphism (cost 2, pattern 
                @Proper (forall _ : ?M498, Prop)
                  (@respectful ?M498 Prop ?M499 iff) 
                  (@Acc ?M498 ?M500), id 0)
                (*external*) (class_apply @proper_flip_proper) (cost 2, pattern 
                @Proper _ (@flip _ _ _ _) _, id 0)
                simple apply @trans_co_eq_inv_impl_morphism (cost 2, pattern 
                @Proper (forall (_ : ?M307) (_ : ?M307), Prop)
                  (@respectful ?M307 (forall _ : ?M307, Prop) 
                     ?M308
                     (@respectful ?M307 Prop (@eq ?M307)
                        (@flip Prop Prop Prop impl)))
                  ?M308, id 0)
                simple apply @per_partial_app_morphism (cost 2, pattern 
                @Proper (forall _ : ?M303, Prop)
                  (@respectful ?M303 Prop ?M304 iff) 
                  (?M304 ?M306), id 0)
                simple eapply @list_to_set_perm_L (cost 3, pattern 
                @Proper (forall _ : list ?M3219, ?M3220)
                  (@respectful (list ?M3219) ?M3220 
                     (@Permutation ?M3219) (@eq ?M3220))
                  (@list_to_set ?M3219 ?M3220 ?M3223 ?M3222 ?M3224), id 0)
                simple eapply @sets.union_proper (cost 3, pattern 
                @Proper (forall (_ : ?M2585) (_ : ?M2585), ?M2585)
                  (@respectful ?M2585 (forall _ : ?M2585, ?M2585)
                     (@equiv ?M2585
                        (@set_equiv_instance ?M2584 ?M2585 ?M2586))
                     (@respectful ?M2585 ?M2585
                        (@equiv ?M2585
                           (@set_equiv_instance ?M2584 ?M2585 ?M2586))
                        (@equiv ?M2585
                           (@set_equiv_instance ?M2584 ?M2585 ?M2586))))
                  (@union ?M2585 ?M2589), id 0)
                simple eapply @PartialOrder_proper (cost 3, pattern 
                @Proper (forall (_ : ?M326) (_ : ?M326), Prop)
                  (@respectful ?M326 (forall _ : ?M326, Prop) 
                     ?M327 (@respectful ?M326 Prop ?M327 iff))
                  ?M329, id 0)
                simple apply @trans_sym_contra_impl_morphism (cost 3, pattern 
                @Proper (forall _ : ?M299, Prop)
                  (@respectful ?M299 Prop (@flip ?M299 ?M299 Prop ?M300) impl)
                  (?M300 ?M302), id 0)
                simple apply @trans_sym_co_inv_impl_morphism (cost 3, pattern 
                @Proper (forall _ : ?M295, Prop)
                  (@respectful ?M295 Prop ?M296 (@flip Prop Prop Prop impl))
                  (?M296 ?M298), id 0)
                simple apply @trans_co_impl_morphism (cost 3, pattern 
                @Proper (forall _ : ?M291, Prop)
                  (@respectful ?M291 Prop ?M292 impl) 
                  (?M292 ?M294), id 0)
                simple apply @trans_contra_inv_impl_morphism (cost 3, pattern 
                @Proper (forall _ : ?M287, Prop)
                  (@respectful ?M287 Prop (@flip ?M287 ?M287 Prop ?M288)
                     (@flip Prop Prop Prop impl))
                  (?M288 ?M290), id 0)
                simple eapply @minimal_proper (cost 4, pattern 
                @Proper (forall _ : ?M3375, Prop)
                  (@respectful ?M3375 Prop
                     (@equiv ?M3375
                        (@set_equiv_instance ?M3374 ?M3375 ?M3376))
                     iff)
                  (@minimal ?M3374 ?M3375 ?M3376 ?M3381 ?M3382), id 0)
                simple apply @foldr_permutation_proper' (cost 4, pattern 
                @Proper (forall _ : list ?M2358, ?M2358)
                  (@respectful (list ?M2358) ?M2358 
                     (@Permutation ?M2358) ?M2359)
                  (@fold_right ?M2358 ?M2358 ?M2361 ?M2362), id 0)
                (*external*) partial_application_tactic (cost 4, pattern 
                @Proper _ _ _, id 0)
                simple eapply @fresh_list_proper (cost 5, pattern 
                @Proper (forall _ : ?M3684, list ?M3683)
                  (@respectful ?M3684 (list ?M3683)
                     (@equiv ?M3684
                        (@set_equiv_instance ?M3683 ?M3684 ?M3685))
                     (@eq (list ?M3683)))
                  (@fresh_list ?M3683 ?M3684
                     (@set_fresh ?M3683 ?M3684 ?M3691
                        (@infinite_fresh ?M3683 ?M3694))
                     ?M3688 ?M3687 ?M3695), id 0)
                simple eapply @sets.difference_proper (cost 5, pattern 
                @Proper (forall (_ : ?M2614) (_ : ?M2614), ?M2614)
                  (@respectful ?M2614 (forall _ : ?M2614, ?M2614)
                     (@equiv ?M2614
                        (@set_equiv_instance ?M2613 ?M2614 ?M2615))
                     (@respectful ?M2614 ?M2614
                        (@equiv ?M2614
                           (@set_equiv_instance ?M2613 ?M2614 ?M2615))
                        (@equiv ?M2614
                           (@set_equiv_instance ?M2613 ?M2614 ?M2615))))
                  (@difference ?M2614 ?M2620), id 0)
                simple eapply @sets.intersection_proper (cost 5, pattern 
                @Proper (forall (_ : ?M2605) (_ : ?M2605), ?M2605)
                  (@respectful ?M2605 (forall _ : ?M2605, ?M2605)
                     (@equiv ?M2605
                        (@set_equiv_instance ?M2604 ?M2605 ?M2606))
                     (@respectful ?M2605 ?M2605
                        (@equiv ?M2605
                           (@set_equiv_instance ?M2604 ?M2605 ?M2606))
                        (@equiv ?M2605
                           (@set_equiv_instance ?M2604 ?M2605 ?M2606))))
                  (@intersection ?M2605 ?M2610), id 0)
                simple apply @elem_of_proper (cost 5, pattern 
                @Proper (forall (_ : ?M2578) (_ : ?M2579), Prop)
                  (@respectful ?M2578 (forall _ : ?M2579, Prop) 
                     (@eq ?M2578)
                     (@respectful ?M2579 Prop
                        (@equiv ?M2579
                           (@set_equiv_instance ?M2578 ?M2579 ?M2580))
                        iff))
                  (@elem_of ?M2578 ?M2579 ?M2580), id 0)
                (*external*) proper_subrelation (cost 5, pattern 
                @Proper _ ?H _, id 0)
                simple eapply @map_seqZ_proper (cost 6, pattern 
                @Proper (forall _ : list ?M4480, ?M4470 ?M4480)
                  (@respectful (list ?M4480) (?M4470 ?M4480)
                     (@equiv (list ?M4480) (@list_equiv ?M4480 ?M4481))
                     (@equiv (?M4470 ?M4480)
                        (@map_equiv Z ?M4470 ?M4472 ?M4480 ?M4481)))
                  (@map_seqZ ?M4480 (?M4470 ?M4480)
                     (@map_insert Z ?M4480 (?M4470 ?M4480) (?M4474 ?M4480))
                     (?M4473 ?M4480) ?M4482), id 0)
                simple eapply @map_seq_proper (cost 6, pattern 
                @Proper (forall _ : list ?M4455, ?M4445 ?M4455)
                  (@respectful (list ?M4455) (?M4445 ?M4455)
                     (@equiv (list ?M4455) (@list_equiv ?M4455 ?M4456))
                     (@equiv (?M4445 ?M4455)
                        (@map_equiv nat ?M4445 ?M4447 ?M4455 ?M4456)))
                  (@map_seq ?M4455 (?M4445 ?M4455)
                     (@map_insert nat ?M4455 (?M4445 ?M4455) (?M4449 ?M4455))
                     (?M4448 ?M4455) ?M4457), id 0)
                simple eapply @map_filter_proper (cost 6, pattern 
                @Proper (forall _ : ?M4400 ?M4410, ?M4400 ?M4410)
                  (@respectful (?M4400 ?M4410) (?M4400 ?M4410)
                     (@equiv (?M4400 ?M4410)
                        (@map_equiv ?M4399 ?M4400 ?M4402 ?M4410 ?M4411))
                     (@equiv (?M4400 ?M4410)
                        (@map_equiv ?M4399 ?M4400 ?M4402 ?M4410 ?M4411)))
                  (@filter (prod ?M4399 ?M4410) (?M4400 ?M4410)
                     (@map_filter ?M4399 ?M4410 (?M4400 ?M4410)
                        (?M4407 ?M4410)
                        (@map_insert ?M4399 ?M4410 
                           (?M4400 ?M4410) (?M4404 ?M4410))
                        (?M4403 ?M4410))
                     ?M4412 ?M4413), id 0)
                simple eapply @singletonM_proper (cost 6, pattern 
                @Proper (forall _ : ?M4222, ?M4212 ?M4222)
                  (@respectful ?M4222 (?M4212 ?M4222) 
                     (@equiv ?M4222 ?M4223)
                     (@equiv (?M4212 ?M4222)
                        (@map_equiv ?M4211 ?M4212 ?M4214 ?M4222 ?M4223)))
                  (@singletonM ?M4211 ?M4222 (?M4212 ?M4222)
                     (@map_singleton ?M4211 ?M4222 
                        (?M4212 ?M4222) (?M4216 ?M4222) 
                        (?M4215 ?M4222))
                     ?M4224), id 0)
                simple eapply @union_list_permutation_proper_L (cost 6, pattern 
                @Proper (forall _ : list ?M3089, ?M3089)
                  (@respectful (list ?M3089) ?M3089 
                     (@Permutation ?M3089) (@eq ?M3089))
                  (@union_list ?M3089 ?M3091 ?M3093), id 0)
                (*external*) proper_normalization (cost 6, pattern 
                @Proper _ _ _, id 0)
                simple eapply @binder_insert_proper (cost 7, pattern 
                @Proper
                  (forall (_ : ?M4583) (_ : ?M4573 ?M4583), ?M4573 ?M4583)
                  (@respectful ?M4583
                     (forall _ : ?M4573 ?M4583, ?M4573 ?M4583)
                     (@equiv ?M4583 ?M4584)
                     (@respectful (?M4573 ?M4583) 
                        (?M4573 ?M4583)
                        (@equiv (?M4573 ?M4583)
                           (@map_equiv string ?M4573 ?M4575 ?M4583 ?M4584))
                        (@equiv (?M4573 ?M4583)
                           (@map_equiv string ?M4573 ?M4575 ?M4583 ?M4584))))
                  (@binder_insert ?M4583 (?M4573 ?M4583)
                     (@map_insert string ?M4583 (?M4573 ?M4583)
                        (?M4577 ?M4583))
                     ?M4585), id 0)
                simple eapply @map_omap_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M4395, option ?M4397)
                     (_ : ?M4385 ?M4395),
                   ?M4385 ?M4397)
                  (@respectful (forall _ : ?M4395, option ?M4397)
                     (forall _ : ?M4385 ?M4395, ?M4385 ?M4397)
                     (@respectful ?M4395 (option ?M4397)
                        (@equiv ?M4395 ?M4396)
                        (@equiv (option ?M4397) (@option_equiv ?M4397 ?M4398)))
                     (@respectful (?M4385 ?M4395) 
                        (?M4385 ?M4397)
                        (@equiv (?M4385 ?M4395)
                           (@map_equiv ?M4384 ?M4385 ?M4387 ?M4395 ?M4396))
                        (@equiv (?M4385 ?M4397)
                           (@map_equiv ?M4384 ?M4385 ?M4387 ?M4397 ?M4398))))
                  (@omap ?M4385 ?M4390 ?M4395 ?M4397), id 0)
                simple eapply @map_fmap_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M4380, ?M4382) (_ : ?M4370 ?M4380),
                   ?M4370 ?M4382)
                  (@respectful (forall _ : ?M4380, ?M4382)
                     (forall _ : ?M4370 ?M4380, ?M4370 ?M4382)
                     (@respectful ?M4380 ?M4382 (@equiv ?M4380 ?M4381)
                        (@equiv ?M4382 ?M4383))
                     (@respectful (?M4370 ?M4380) 
                        (?M4370 ?M4382)
                        (@equiv (?M4370 ?M4380)
                           (@map_equiv ?M4369 ?M4370 ?M4372 ?M4380 ?M4381))
                        (@equiv (?M4370 ?M4382)
                           (@map_equiv ?M4369 ?M4370 ?M4372 ?M4382 ?M4383))))
                  (@fmap ?M4370 ?M4371 ?M4380 ?M4382), id 0)
                simple eapply @map_zip_with_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall (_ : ?M4358) (_ : ?M4360), ?M4362)
                     (_ : ?M4348 ?M4358) (_ : ?M4348 ?M4360),
                   ?M4348 ?M4362)
                  (@respectful (forall (_ : ?M4358) (_ : ?M4360), ?M4362)
                     (forall (_ : ?M4348 ?M4358) (_ : ?M4348 ?M4360),
                      ?M4348 ?M4362)
                     (@respectful ?M4358 (forall _ : ?M4360, ?M4362)
                        (@equiv ?M4358 ?M4359)
                        (@respectful ?M4360 ?M4362 
                           (@equiv ?M4360 ?M4361) 
                           (@equiv ?M4362 ?M4363)))
                     (@respectful (?M4348 ?M4358)
                        (forall _ : ?M4348 ?M4360, ?M4348 ?M4362)
                        (@equiv (?M4348 ?M4358)
                           (@map_equiv ?M4347 ?M4348 ?M4350 ?M4358 ?M4359))
                        (@respectful (?M4348 ?M4360) 
                           (?M4348 ?M4362)
                           (@equiv (?M4348 ?M4360)
                              (@map_equiv ?M4347 ?M4348 ?M4350 ?M4360 ?M4361))
                           (@equiv (?M4348 ?M4362)
                              (@map_equiv ?M4347 ?M4348 ?M4350 ?M4362 ?M4363)))))
                  (@map_zip_with ?M4348 ?M4354 ?M4358 ?M4360 ?M4362), id 0)
                simple eapply @difference_proper (cost 7, pattern 
                @Proper
                  (forall (_ : ?M4335 ?M4345) (_ : ?M4335 ?M4345),
                   ?M4335 ?M4345)
                  (@respectful (?M4335 ?M4345)
                     (forall _ : ?M4335 ?M4345, ?M4335 ?M4345)
                     (@equiv (?M4335 ?M4345)
                        (@map_equiv ?M4334 ?M4335 ?M4337 ?M4345 ?M4346))
                     (@respectful (?M4335 ?M4345) 
                        (?M4335 ?M4345)
                        (@equiv (?M4335 ?M4345)
                           (@map_equiv ?M4334 ?M4335 ?M4337 ?M4345 ?M4346))
                        (@equiv (?M4335 ?M4345)
                           (@map_equiv ?M4334 ?M4335 ?M4337 ?M4345 ?M4346))))
                  (@difference (?M4335 ?M4345)
                     (@map_difference ?M4335 ?M4341 ?M4345)), id 0)
                simple eapply @intersection_proper (cost 7, pattern 
                @Proper
                  (forall (_ : ?M4322 ?M4332) (_ : ?M4322 ?M4332),
                   ?M4322 ?M4332)
                  (@respectful (?M4322 ?M4332)
                     (forall _ : ?M4322 ?M4332, ?M4322 ?M4332)
                     (@equiv (?M4322 ?M4332)
                        (@map_equiv ?M4321 ?M4322 ?M4324 ?M4332 ?M4333))
                     (@respectful (?M4322 ?M4332) 
                        (?M4322 ?M4332)
                        (@equiv (?M4322 ?M4332)
                           (@map_equiv ?M4321 ?M4322 ?M4324 ?M4332 ?M4333))
                        (@equiv (?M4322 ?M4332)
                           (@map_equiv ?M4321 ?M4322 ?M4324 ?M4332 ?M4333))))
                  (@intersection (?M4322 ?M4332)
                     (@map_intersection ?M4322 ?M4328 ?M4332)), id 0)
                simple eapply @union_proper (cost 7, pattern 
                @Proper
                  (forall (_ : ?M4309 ?M4319) (_ : ?M4309 ?M4319),
                   ?M4309 ?M4319)
                  (@respectful (?M4309 ?M4319)
                     (forall _ : ?M4309 ?M4319, ?M4309 ?M4319)
                     (@equiv (?M4309 ?M4319)
                        (@map_equiv ?M4308 ?M4309 ?M4311 ?M4319 ?M4320))
                     (@respectful (?M4309 ?M4319) 
                        (?M4309 ?M4319)
                        (@equiv (?M4309 ?M4319)
                           (@map_equiv ?M4308 ?M4309 ?M4311 ?M4319 ?M4320))
                        (@equiv (?M4309 ?M4319)
                           (@map_equiv ?M4308 ?M4309 ?M4311 ?M4319 ?M4320))))
                  (@union (?M4309 ?M4319) (@map_union ?M4309 ?M4315 ?M4319)), id 0)
                simple eapply @difference_with_proper (cost 7, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M4306) (_ : ?M4306), option ?M4306)
                     (_ : ?M4296 ?M4306) (_ : ?M4296 ?M4306),
                   ?M4296 ?M4306)
                  (@respectful
                     (forall (_ : ?M4306) (_ : ?M4306), option ?M4306)
                     (forall (_ : ?M4296 ?M4306) (_ : ?M4296 ?M4306),
                      ?M4296 ?M4306)
                     (@respectful ?M4306 (forall _ : ?M4306, option ?M4306)
                        (@equiv ?M4306 ?M4307)
                        (@respectful ?M4306 (option ?M4306)
                           (@equiv ?M4306 ?M4307)
                           (@equiv (option ?M4306)
                              (@option_equiv ?M4306 ?M4307))))
                     (@respectful (?M4296 ?M4306)
                        (forall _ : ?M4296 ?M4306, ?M4296 ?M4306)
                        (@equiv (?M4296 ?M4306)
                           (@map_equiv ?M4295 ?M4296 ?M4298 ?M4306 ?M4307))
                        (@respectful (?M4296 ?M4306) 
                           (?M4296 ?M4306)
                           (@equiv (?M4296 ?M4306)
                              (@map_equiv ?M4295 ?M4296 ?M4298 ?M4306 ?M4307))
                           (@equiv (?M4296 ?M4306)
                              (@map_equiv ?M4295 ?M4296 ?M4298 ?M4306 ?M4307)))))
                  (@difference_with ?M4306 (?M4296 ?M4306)
                     (@map_difference_with ?M4296 ?M4302 ?M4306)), id 0)
                simple eapply @intersection_with_proper (cost 7, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M4293) (_ : ?M4293), option ?M4293)
                     (_ : ?M4283 ?M4293) (_ : ?M4283 ?M4293),
                   ?M4283 ?M4293)
                  (@respectful
                     (forall (_ : ?M4293) (_ : ?M4293), option ?M4293)
                     (forall (_ : ?M4283 ?M4293) (_ : ?M4283 ?M4293),
                      ?M4283 ?M4293)
                     (@respectful ?M4293 (forall _ : ?M4293, option ?M4293)
                        (@equiv ?M4293 ?M4294)
                        (@respectful ?M4293 (option ?M4293)
                           (@equiv ?M4293 ?M4294)
                           (@equiv (option ?M4293)
                              (@option_equiv ?M4293 ?M4294))))
                     (@respectful (?M4283 ?M4293)
                        (forall _ : ?M4283 ?M4293, ?M4283 ?M4293)
                        (@equiv (?M4283 ?M4293)
                           (@map_equiv ?M4282 ?M4283 ?M4285 ?M4293 ?M4294))
                        (@respectful (?M4283 ?M4293) 
                           (?M4283 ?M4293)
                           (@equiv (?M4283 ?M4293)
                              (@map_equiv ?M4282 ?M4283 ?M4285 ?M4293 ?M4294))
                           (@equiv (?M4283 ?M4293)
                              (@map_equiv ?M4282 ?M4283 ?M4285 ?M4293 ?M4294)))))
                  (@intersection_with ?M4293 (?M4283 ?M4293)
                     (@map_intersection_with ?M4283 ?M4289 ?M4293)), id 0)
                simple eapply @union_with_proper (cost 7, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : ?M4280) (_ : ?M4280), option ?M4280)
                     (_ : ?M4270 ?M4280) (_ : ?M4270 ?M4280),
                   ?M4270 ?M4280)
                  (@respectful
                     (forall (_ : ?M4280) (_ : ?M4280), option ?M4280)
                     (forall (_ : ?M4270 ?M4280) (_ : ?M4270 ?M4280),
                      ?M4270 ?M4280)
                     (@respectful ?M4280 (forall _ : ?M4280, option ?M4280)
                        (@equiv ?M4280 ?M4281)
                        (@respectful ?M4280 (option ?M4280)
                           (@equiv ?M4280 ?M4281)
                           (@equiv (option ?M4280)
                              (@option_equiv ?M4280 ?M4281))))
                     (@respectful (?M4270 ?M4280)
                        (forall _ : ?M4270 ?M4280, ?M4270 ?M4280)
                        (@equiv (?M4270 ?M4280)
                           (@map_equiv ?M4269 ?M4270 ?M4272 ?M4280 ?M4281))
                        (@respectful (?M4270 ?M4280) 
                           (?M4270 ?M4280)
                           (@equiv (?M4270 ?M4280)
                              (@map_equiv ?M4269 ?M4270 ?M4272 ?M4280 ?M4281))
                           (@equiv (?M4270 ?M4280)
                              (@map_equiv ?M4269 ?M4270 ?M4272 ?M4280 ?M4281)))))
                  (@union_with ?M4280 (?M4270 ?M4280)
                     (@map_union_with ?M4270 ?M4276 ?M4280)), id 0)
                simple eapply @merge_proper (cost 7, pattern 
                @Proper
                  (forall
                     (_ : forall (_ : option ?M4263) (_ : option ?M4265),
                          option ?M4267)
                     (_ : ?M4253 ?M4263) (_ : ?M4253 ?M4265),
                   ?M4253 ?M4267)
                  (@respectful
                     (forall (_ : option ?M4263) (_ : option ?M4265),
                      option ?M4267)
                     (forall (_ : ?M4253 ?M4263) (_ : ?M4253 ?M4265),
                      ?M4253 ?M4267)
                     (@respectful (option ?M4263)
                        (forall _ : option ?M4265, option ?M4267)
                        (@equiv (option ?M4263) (@option_equiv ?M4263 ?M4264))
                        (@respectful (option ?M4265) 
                           (option ?M4267)
                           (@equiv (option ?M4265)
                              (@option_equiv ?M4265 ?M4266))
                           (@equiv (option ?M4267)
                              (@option_equiv ?M4267 ?M4268))))
                     (@respectful (?M4253 ?M4263)
                        (forall _ : ?M4253 ?M4265, ?M4253 ?M4267)
                        (@equiv (?M4253 ?M4263)
                           (@map_equiv ?M4252 ?M4253 ?M4255 ?M4263 ?M4264))
                        (@respectful (?M4253 ?M4265) 
                           (?M4253 ?M4267)
                           (@equiv (?M4253 ?M4265)
                              (@map_equiv ?M4252 ?M4253 ?M4255 ?M4265 ?M4266))
                           (@equiv (?M4253 ?M4267)
                              (@map_equiv ?M4252 ?M4253 ?M4255 ?M4267 ?M4268)))))
                  (@merge ?M4253 ?M4259 ?M4263 ?M4265 ?M4267), id 0)
                simple eapply @alter_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M4250, ?M4250) 
                     (_ : ?M4239) (_ : ?M4240 ?M4250),
                   ?M4240 ?M4250)
                  (@respectful (forall _ : ?M4250, ?M4250)
                     (forall (_ : ?M4239) (_ : ?M4240 ?M4250), ?M4240 ?M4250)
                     (@respectful ?M4250 ?M4250 (@equiv ?M4250 ?M4251)
                        (@equiv ?M4250 ?M4251))
                     (@respectful ?M4239
                        (forall _ : ?M4240 ?M4250, ?M4240 ?M4250)
                        (@eq ?M4239)
                        (@respectful (?M4240 ?M4250) 
                           (?M4240 ?M4250)
                           (@equiv (?M4240 ?M4250)
                              (@map_equiv ?M4239 ?M4240 ?M4242 ?M4250 ?M4251))
                           (@equiv (?M4240 ?M4250)
                              (@map_equiv ?M4239 ?M4240 ?M4242 ?M4250 ?M4251)))))
                  (@alter ?M4239 ?M4250 (?M4240 ?M4250)
                     (@map_alter ?M4239 ?M4250 (?M4240 ?M4250)
                        (?M4244 ?M4250))), id 0)
                simple eapply @delete_proper (cost 7, pattern 
                @Proper (forall _ : ?M4226 ?M4236, ?M4226 ?M4236)
                  (@respectful (?M4226 ?M4236) (?M4226 ?M4236)
                     (@equiv (?M4226 ?M4236)
                        (@map_equiv ?M4225 ?M4226 ?M4228 ?M4236 ?M4237))
                     (@equiv (?M4226 ?M4236)
                        (@map_equiv ?M4225 ?M4226 ?M4228 ?M4236 ?M4237)))
                  (@delete ?M4225 (?M4226 ?M4236)
                     (@map_delete ?M4225 ?M4236 (?M4226 ?M4236)
                        (?M4230 ?M4236))
                     ?M4238), id 0)
                simple eapply @insert_proper (cost 7, pattern 
                @Proper
                  (forall (_ : ?M4208) (_ : ?M4198 ?M4208), ?M4198 ?M4208)
                  (@respectful ?M4208
                     (forall _ : ?M4198 ?M4208, ?M4198 ?M4208)
                     (@equiv ?M4208 ?M4209)
                     (@respectful (?M4198 ?M4208) 
                        (?M4198 ?M4208)
                        (@equiv (?M4198 ?M4208)
                           (@map_equiv ?M4197 ?M4198 ?M4200 ?M4208 ?M4209))
                        (@equiv (?M4198 ?M4208)
                           (@map_equiv ?M4197 ?M4198 ?M4200 ?M4208 ?M4209))))
                  (@insert ?M4197 ?M4208 (?M4198 ?M4208)
                     (@map_insert ?M4197 ?M4208 (?M4198 ?M4208)
                        (?M4202 ?M4208))
                     ?M4210), id 0)
                simple eapply @partial_alter_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : option ?M4195, option ?M4195)
                     (_ : ?M4184) (_ : ?M4185 ?M4195),
                   ?M4185 ?M4195)
                  (@respectful (forall _ : option ?M4195, option ?M4195)
                     (forall (_ : ?M4184) (_ : ?M4185 ?M4195), ?M4185 ?M4195)
                     (@respectful (option ?M4195) 
                        (option ?M4195)
                        (@equiv (option ?M4195) (@option_equiv ?M4195 ?M4196))
                        (@equiv (option ?M4195) (@option_equiv ?M4195 ?M4196)))
                     (@respectful ?M4184
                        (forall _ : ?M4185 ?M4195, ?M4185 ?M4195)
                        (@eq ?M4184)
                        (@respectful (?M4185 ?M4195) 
                           (?M4185 ?M4195)
                           (@equiv (?M4185 ?M4195)
                              (@map_equiv ?M4184 ?M4185 ?M4187 ?M4195 ?M4196))
                           (@equiv (?M4185 ?M4195)
                              (@map_equiv ?M4184 ?M4185 ?M4187 ?M4195 ?M4196)))))
                  (@partial_alter ?M4184 ?M4195 (?M4185 ?M4195)
                     (?M4189 ?M4195)), id 0)
                simple eapply @fresh_proper (cost 7, pattern 
                @Proper (forall _ : ?M3672, ?M3671)
                  (@respectful ?M3672 ?M3671
                     (@equiv ?M3672
                        (@set_equiv_instance ?M3671 ?M3672 ?M3673))
                     (@eq ?M3671))
                  (@fresh ?M3671 ?M3672
                     (@set_fresh ?M3671 ?M3672 ?M3679
                        (@infinite_fresh ?M3671 ?M3682))), id 0)
                simple eapply @set_size_proper (cost 7, pattern 
                @Proper (forall _ : ?M3437, nat)
                  (@respectful ?M3437 nat
                     (@equiv ?M3437
                        (@set_equiv_instance ?M3436 ?M3437 ?M3438))
                     (@eq nat))
                  (@size ?M3437 (@set_size ?M3436 ?M3437 ?M3444)), id 0)
                simple eapply @elements_proper (cost 7, pattern 
                @Proper (forall _ : ?M3426, list ?M3425)
                  (@respectful ?M3426 (list ?M3425)
                     (@equiv ?M3426
                        (@set_equiv_instance ?M3425 ?M3426 ?M3427))
                     (@Permutation ?M3425))
                  (@elements ?M3425 ?M3426 ?M3433), id 0)
                simple eapply @set_join_mono (cost 7, pattern 
                @Proper (forall _ : ?M3318 (?M3318 ?M3328), ?M3318 ?M3328)
                  (@respectful (?M3318 (?M3318 ?M3328)) 
                     (?M3318 ?M3328)
                     (@subseteq (?M3318 (?M3318 ?M3328))
                        (@set_subseteq_instance (?M3318 ?M3328)
                           (?M3318 (?M3318 ?M3328)) 
                           (?M3319 (?M3318 ?M3328))))
                     (@subseteq (?M3318 ?M3328)
                        (@set_subseteq_instance ?M3328 
                           (?M3318 ?M3328) (?M3319 ?M3328))))
                  (@mjoin ?M3318 ?M3326 ?M3328), id 0)
                simple eapply @sets.set_bind_mono (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3316, ?M3306 ?M3317)
                     (_ : ?M3306 ?M3316),
                   ?M3306 ?M3317)
                  (@respectful (forall _ : ?M3316, ?M3306 ?M3317)
                     (forall _ : ?M3306 ?M3316, ?M3306 ?M3317)
                     (@pointwise_relation ?M3316 (?M3306 ?M3317)
                        (@subseteq (?M3306 ?M3317)
                           (@set_subseteq_instance 
                              ?M3317 (?M3306 ?M3317) 
                              (?M3307 ?M3317))))
                     (@respectful (?M3306 ?M3316) 
                        (?M3306 ?M3317)
                        (@subseteq (?M3306 ?M3316)
                           (@set_subseteq_instance 
                              ?M3316 (?M3306 ?M3316) 
                              (?M3307 ?M3316)))
                        (@subseteq (?M3306 ?M3317)
                           (@set_subseteq_instance 
                              ?M3317 (?M3306 ?M3317) 
                              (?M3307 ?M3317)))))
                  (@mbind ?M3306 ?M3311 ?M3316 ?M3317), id 0)
                simple eapply @set_fmap_mono (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3304, ?M3305) (_ : ?M3294 ?M3304),
                   ?M3294 ?M3305)
                  (@respectful (forall _ : ?M3304, ?M3305)
                     (forall _ : ?M3294 ?M3304, ?M3294 ?M3305)
                     (@pointwise_relation ?M3304 ?M3305 (@eq ?M3305))
                     (@respectful (?M3294 ?M3304) 
                        (?M3294 ?M3305)
                        (@subseteq (?M3294 ?M3304)
                           (@set_subseteq_instance 
                              ?M3304 (?M3294 ?M3304) 
                              (?M3295 ?M3304)))
                        (@subseteq (?M3294 ?M3305)
                           (@set_subseteq_instance 
                              ?M3305 (?M3294 ?M3305) 
                              (?M3295 ?M3305)))))
                  (@fmap ?M3294 ?M3301 ?M3304 ?M3305), id 0)
                simple eapply @set_join_proper (cost 7, pattern 
                @Proper (forall _ : ?M2646 (?M2646 ?M2656), ?M2646 ?M2656)
                  (@respectful (?M2646 (?M2646 ?M2656)) 
                     (?M2646 ?M2656)
                     (@equiv (?M2646 (?M2646 ?M2656))
                        (@set_equiv_instance (?M2646 ?M2656)
                           (?M2646 (?M2646 ?M2656)) 
                           (?M2647 (?M2646 ?M2656))))
                     (@equiv (?M2646 ?M2656)
                        (@set_equiv_instance ?M2656 
                           (?M2646 ?M2656) (?M2647 ?M2656))))
                  (@mjoin ?M2646 ?M2654 ?M2656), id 0)
                simple eapply @sets.set_bind_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2644, ?M2634 ?M2645)
                     (_ : ?M2634 ?M2644),
                   ?M2634 ?M2645)
                  (@respectful (forall _ : ?M2644, ?M2634 ?M2645)
                     (forall _ : ?M2634 ?M2644, ?M2634 ?M2645)
                     (@pointwise_relation ?M2644 (?M2634 ?M2645)
                        (@equiv (?M2634 ?M2645)
                           (@set_equiv_instance ?M2645 
                              (?M2634 ?M2645) (?M2635 ?M2645))))
                     (@respectful (?M2634 ?M2644) 
                        (?M2634 ?M2645)
                        (@equiv (?M2634 ?M2644)
                           (@set_equiv_instance ?M2644 
                              (?M2634 ?M2644) (?M2635 ?M2644)))
                        (@equiv (?M2634 ?M2645)
                           (@set_equiv_instance ?M2645 
                              (?M2634 ?M2645) (?M2635 ?M2645)))))
                  (@mbind ?M2634 ?M2639 ?M2644 ?M2645), id 0)
                simple eapply @set_fmap_proper (cost 7, pattern 
                @Proper
                  (forall (_ : forall _ : ?M2632, ?M2633) (_ : ?M2622 ?M2632),
                   ?M2622 ?M2633)
                  (@respectful (forall _ : ?M2632, ?M2633)
                     (forall _ : ?M2622 ?M2632, ?M2622 ?M2633)
                     (@pointwise_relation ?M2632 ?M2633 (@eq ?M2633))
                     (@respectful (?M2622 ?M2632) 
                        (?M2622 ?M2633)
                        (@equiv (?M2622 ?M2632)
                           (@set_equiv_instance ?M2632 
                              (?M2622 ?M2632) (?M2623 ?M2632)))
                        (@equiv (?M2622 ?M2633)
                           (@set_equiv_instance ?M2633 
                              (?M2622 ?M2633) (?M2623 ?M2633)))))
                  (@fmap ?M2622 ?M2629 ?M2632 ?M2633), id 0)
                (*external*) proper_reflexive (cost 7, pattern 
                @Proper _ _ _, id 0)
                simple eapply @set_omap_mono (cost 8, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3625, option ?M3636) (_ : ?M3626),
                   ?M3637)
                  (@respectful (forall _ : ?M3625, option ?M3636)
                     (forall _ : ?M3626, ?M3637)
                     (@pointwise_relation ?M3625 (option ?M3636)
                        (@eq (option ?M3636)))
                     (@respectful ?M3626 ?M3637
                        (@subseteq ?M3626
                           (@set_subseteq_instance ?M3625 ?M3626 ?M3627))
                        (@subseteq ?M3637
                           (@set_subseteq_instance ?M3636 ?M3637 ?M3638))))
                  (@set_omap ?M3625 ?M3626 ?M3633 
                     ?M3636 ?M3637 ?M3640 ?M3639 ?M3641), id 0)
                simple eapply @set_omap_proper (cost 8, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3607, option ?M3618) (_ : ?M3608),
                   ?M3619)
                  (@respectful (forall _ : ?M3607, option ?M3618)
                     (forall _ : ?M3608, ?M3619)
                     (@pointwise_relation ?M3607 (option ?M3618)
                        (@eq (option ?M3618)))
                     (@respectful ?M3608 ?M3619
                        (@equiv ?M3608
                           (@set_equiv_instance ?M3607 ?M3608 ?M3609))
                        (@equiv ?M3619
                           (@set_equiv_instance ?M3618 ?M3619 ?M3620))))
                  (@set_omap ?M3607 ?M3608 ?M3615 
                     ?M3618 ?M3619 ?M3622 ?M3621 ?M3623), id 0)
                simple eapply @set_map_mono (cost 8, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3505, ?M3516) (_ : ?M3506),
                   ?M3517)
                  (@respectful (forall _ : ?M3505, ?M3516)
                     (forall _ : ?M3506, ?M3517)
                     (@pointwise_relation ?M3505 ?M3516 (@eq ?M3516))
                     (@respectful ?M3506 ?M3517
                        (@subseteq ?M3506
                           (@set_subseteq_instance ?M3505 ?M3506 ?M3507))
                        (@subseteq ?M3517
                           (@set_subseteq_instance ?M3516 ?M3517 ?M3518))))
                  (@set_map ?M3505 ?M3506 ?M3513 ?M3516 
                     ?M3517 ?M3520 ?M3519 ?M3521), id 0)
                simple eapply @set_map_proper (cost 8, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3487, ?M3498) (_ : ?M3488),
                   ?M3499)
                  (@respectful (forall _ : ?M3487, ?M3498)
                     (forall _ : ?M3488, ?M3499)
                     (@pointwise_relation ?M3487 ?M3498 (@eq ?M3498))
                     (@respectful ?M3488 ?M3499
                        (@equiv ?M3488
                           (@set_equiv_instance ?M3487 ?M3488 ?M3489))
                        (@equiv ?M3499
                           (@set_equiv_instance ?M3498 ?M3499 ?M3500))))
                  (@set_map ?M3487 ?M3488 ?M3495 ?M3498 
                     ?M3499 ?M3502 ?M3501 ?M3503), id 0)
                simple eapply @set_bind_mono (cost 9, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3566, ?M3578) (_ : ?M3567),
                   ?M3578)
                  (@respectful (forall _ : ?M3566, ?M3578)
                     (forall _ : ?M3567, ?M3578)
                     (@pointwise_relation ?M3566 ?M3578
                        (@subseteq ?M3578
                           (@set_subseteq_instance ?M3577 ?M3578 ?M3579)))
                     (@respectful ?M3567 ?M3578
                        (@subseteq ?M3567
                           (@set_subseteq_instance ?M3566 ?M3567 ?M3568))
                        (@subseteq ?M3578
                           (@set_subseteq_instance ?M3577 ?M3578 ?M3579))))
                  (@set_bind ?M3566 ?M3567 ?M3574 ?M3578 ?M3580 ?M3582), id 0)
                simple eapply @set_bind_proper (cost 9, pattern 
                @Proper
                  (forall (_ : forall _ : ?M3548, ?M3560) (_ : ?M3549),
                   ?M3560)
                  (@respectful (forall _ : ?M3548, ?M3560)
                     (forall _ : ?M3549, ?M3560)
                     (@pointwise_relation ?M3548 ?M3560
                        (@equiv ?M3560
                           (@set_equiv_instance ?M3559 ?M3560 ?M3561)))
                     (@respectful ?M3549 ?M3560
                        (@equiv ?M3549
                           (@set_equiv_instance ?M3548 ?M3549 ?M3550))
                        (@equiv ?M3560
                           (@set_equiv_instance ?M3559 ?M3560 ?M3561))))
                  (@set_bind ?M3548 ?M3549 ?M3556 ?M3560 ?M3562 ?M3564), id 0)
                exact Permutation_list_max (cost 10, pattern 
                @Proper (forall _ : list nat, nat)
                  (@respectful (list nat) nat (@Permutation nat) (@eq nat))
                  list_max, id 0)
                exact Permutation_list_sum (cost 10, pattern 
                @Proper (forall _ : list nat, nat)
                  (@respectful (list nat) nat (@Permutation nat) (@eq nat))
                  list_sum, id 0)
                simple apply Permutation_length' (cost 10, pattern 
                @Proper (forall _ : list ?M1074, nat)
                  (@respectful (list ?M1074) nat (@Permutation ?M1074)
                     (@eq nat))
                  (@length ?M1074), id 0)
                simple eapply @dom_proper (cost 13, pattern 
                @Proper (forall _ : ?M4684 ?M4702, ?M4685)
                  (@respectful (?M4684 ?M4702) ?M4685
                     (@equiv (?M4684 ?M4702)
                        (@map_equiv ?M4683 ?M4684 ?M4688 ?M4702 ?M4703))
                     (@equiv ?M4685
                        (@set_equiv_instance ?M4683 ?M4685 ?M4695)))
                  (@dom (?M4684 ?M4702) ?M4685 (?M4686 ?M4702)), id 0)
For CMorphisms.ProperProxy ->   (*external*) (class_apply
                                               @CMorphisms.eq_proper_proxy ||
                                                class_apply
                                                 @CMorphisms.reflexive_proper_proxy) (cost 1, pattern 
                                @CMorphisms.ProperProxy _ _ _, id 0)
                                (*external*) (not_evar R;
                                               class_apply
                                                @CMorphisms.proper_proper_proxy) (cost 2, pattern 
                                @CMorphisms.ProperProxy _ 
                                  ?R _, id 0)
For ProperProxy ->   (*external*) (class_apply @eq_proper_proxy ||
                                     class_apply @reflexive_proper_proxy) (cost 1, pattern 
                     @ProperProxy _ _ _, id 0)
                     (*external*) (not_evar R;
                                    class_apply @proper_proper_proxy) (cost 2, pattern 
                     @ProperProxy _ ?R _, id 0)
For rlist.Quote ->   simple apply @rlist.quote_nil (cost 0, pattern 
                     @rlist.Quote ?M2404 ?M2405 ?M2405 
                       (@nil ?M2404) (@rnil nat), id 0)
                     simple eapply @rlist.quote_app (cost 3, pattern 
                     @rlist.Quote ?M2422 ?M2423 ?M2425
                       (@app ?M2422 ?M2426 ?M2427) 
                       (@rapp nat ?M2428 ?M2429), id 0)
                     simple eapply @rlist.quote_cons (cost 3, pattern 
                     @rlist.Quote ?M2412 ?M2413 ?M2415
                       (@cons ?M2412 ?M2416 ?M2417)
                       (@rapp nat (@rnode nat ?M2418) ?M2419), id 0)
                     simple apply @rlist.quote_node (cost 1000, pattern 
                     @rlist.Quote ?M2406 ?M2407 ?M2408 
                       ?M2409 (@rnode nat ?M2410), id 0)
For rlist.QuoteLookup ->   simple apply @rlist.quote_lookup_end (cost 0, pattern 
                           @rlist.QuoteLookup ?M2395 
                             (@nil ?M2395)
                             (@cons ?M2395 ?M2396 (@nil ?M2395)) 
                             ?M2396 O, id 0)
                           simple apply @rlist.quote_lookup_here (cost 0, pattern 
                           @rlist.QuoteLookup ?M2392
                             (@cons ?M2392 ?M2394 ?M2393)
                             (@cons ?M2392 ?M2394 ?M2393) 
                             ?M2394 O, id 0)
                           simple apply @rlist.quote_lookup_further (cost 1000, pattern 
                           @rlist.QuoteLookup ?M2397
                             (@cons ?M2397 ?M2402 ?M2398)
                             (@cons ?M2397 ?M2402 ?M2399) 
                             ?M2400 (S ?M2401), id 0)
For CRelationClasses.Reflexive ->   exact CRelationClasses.iffT_Reflexive (cost 0, pattern 
                                    @CRelationClasses.Reflexive Type
                                      CRelationClasses.iffT, id 0)
                                    exact CRelationClasses.arrow_Reflexive (cost 0, pattern 
                                    @CRelationClasses.Reflexive Type
                                      CRelationClasses.arrow, id 0)
                                    exact CRelationClasses.iff_Reflexive (cost 0, pattern 
                                    @CRelationClasses.Reflexive Prop iff, id 0)
                                    exact CRelationClasses.impl_Reflexive (cost 0, pattern 
                                    @CRelationClasses.Reflexive Prop impl, id 0)
                                    simple apply @CRelationClasses.eq_Reflexive (cost 0, pattern 
                                    @CRelationClasses.Reflexive 
                                      ?M418 (@eq ?M418), id 0)
                                    simple apply @CMorphisms.reflexive_eq_dom_reflexive (cost 1, pattern 
                                    @CRelationClasses.Reflexive
                                      (forall _ : ?M482, ?M479)
                                      (@CMorphisms.respectful 
                                         ?M482 ?M479 
                                         (@eq ?M482) 
                                         ?M480), id 0)
                                    (*external*) (
                                    class_apply
                                     @CRelationClasses.irreflexivity) (cost 1, pattern 
                                    @CRelationClasses.Reflexive _
                                      (@CRelationClasses.complement _ _), id 0)
                                    simple apply @CRelationClasses.Equivalence_Reflexive (cost 1, pattern 
                                    @CRelationClasses.Reflexive 
                                      ?M403 ?M404, id 0)
                                    simple apply @CRelationClasses.PreOrder_Reflexive (cost 2, pattern 
                                    @CRelationClasses.Reflexive 
                                      ?M382 ?M383, id 0)
                                    (*external*) (
                                    apply
                                     (@CRelationClasses.flip_Reflexive _ _ _)) (cost 3, pattern 
                                    @CRelationClasses.Reflexive _
                                      (@CRelationClasses.flip _ _ _ _), id 0)
For Reflexive (modes -
!) ->   simple apply @map_agree_refl (cost 0, pattern 
        @Reflexive (?M3947 ?M3949) (@map_agree ?M3946 ?M3947 ?M3948 ?M3949), id 0)
        exact iff_Reflexive (cost 0, pattern @Reflexive Prop iff, id 0)
        exact impl_Reflexive (cost 0, pattern @Reflexive Prop impl, id 0)
        simple apply @eq_Reflexive (cost 0, pattern 
        @Reflexive ?M254 (@eq ?M254), id 0)
        simple apply @sc_reflexive (cost 1, pattern 
        @Reflexive ?M3390 (@sc ?M3390 ?M3391), id 0)
        simple apply @Reflexive_instance_0 (cost 1, pattern 
        @Reflexive (list ?M2177) (@Forall2 ?M2177 ?M2177 ?M2178), id 0)
        simple apply @option_Forall2_refl (cost 1, pattern 
        @Reflexive (option ?M1939) (@option_Forall2 ?M1939 ?M1939 ?M1940), id 0)
        simple apply @Equivalence.equiv_reflexive (cost 1, pattern 
        @Reflexive ?M505 (@Equivalence.equiv ?M505 ?M506 ?M507), id 0)
        simple apply @reflexive_eq_dom_reflexive (cost 1, pattern 
        @Reflexive (forall _ : ?M319, ?M320)
          (@respectful ?M319 ?M320 (@eq ?M319) ?M321), id 0)
        (*external*) (class_apply @irreflexivity) (cost 1, pattern 
        @Reflexive _ (@complement _ _), id 0)
        simple apply @Equivalence_Reflexive (cost 1, pattern 
        @Reflexive ?M239 ?M240, id 0)
        simple apply @sum_relation_refl (cost 2, pattern 
        @Reflexive (sum ?M1431 ?M1433)
          (@sum_relation ?M1431 ?M1433 ?M1432 ?M1434), id 0)
        simple apply @prod_relation_refl (cost 2, pattern 
        @Reflexive (prod ?M1237 ?M1239)
          (@prod_relation ?M1237 ?M1239 ?M1238 ?M1240), id 0)
        simple apply @PreOrder_Reflexive (cost 2, pattern 
        @Reflexive ?M218 ?M219, id 0)
        (*external*) (apply (@flip_Reflexive _ _ _)) (cost 3, pattern 
        @Reflexive _ (@flip _ _ _ _), id 0)
        exact Z.divide_reflexive (cost 5, pattern 
        @Reflexive Z Z.divide, id 0)
        exact N.divide_reflexive (cost 5, pattern 
        @Reflexive N N.divide, id 0)
        exact N.Private_NZGcdProp.divide_reflexive (cost 5, pattern 
        @Reflexive N N.divide, id 0)
        exact Nat.divide_reflexive (cost 5, pattern 
        @Reflexive nat Nat.divide, id 0)
        exact Nat.Private_NZGcdProp.divide_reflexive (cost 5, pattern 
        @Reflexive nat Nat.divide, id 0)
        simple apply @Equivalence.pointwise_reflexive (cost 9, pattern 
        @Reflexive (forall _ : ?M514, ?M515)
          (@pointwise_relation ?M514 ?M515 ?M516), id 0)
For ssrclasses.Reflexive ->   exact ssrclasses.iff_Reflexive (cost 0, pattern 
                              @ssrclasses.Reflexive Prop iff, id 0)
                              simple apply @ssrclasses.eq_Reflexive (cost 0, pattern 
                              @ssrclasses.Reflexive 
                                ?M533 (@eq ?M533), id 0)
                              simple apply @ssrsetoid.compat_Reflexive (cost 12, pattern 
                              @ssrclasses.Reflexive 
                                ?M534 ?M535, id 0)
For ReflexiveProxy ->   (*external*) (reflexive_proxy_tac A R) (cost 1, pattern 
                        @ReflexiveProxy ?A ?R, id 0)
For RelDecision (modes ! !
!) ->   simple apply @topGset_elem_of_dec (cost 0, pattern 
        @RelDecision ?M5924 (@topGset ?M5924 ?M5925 ?M5926)
          (@elem_of ?M5924 (@topGset ?M5924 ?M5925 ?M5926)
             (@topGset_elem_of ?M5924 ?M5925 ?M5926)), id 0)
        simple apply @topGset_eq_dec (cost 0, pattern 
        @RelDecision (@topGset ?M5897 ?M5898 ?M5899)
          (@topGset ?M5897 ?M5898 ?M5899)
          (@eq (@topGset ?M5897 ?M5898 ?M5899)), id 0)
        exact namespace_eq_dec (cost 0, pattern @RelDecision namespace
                                                 namespace 
                                                 (@eq namespace), id 0)
        simple apply @gmultiset_subseteq_dec (cost 0, pattern 
        @RelDecision (@gmultiset ?M5598 ?M5599 ?M5600)
          (@gmultiset ?M5598 ?M5599 ?M5600)
          (@subseteq (@gmultiset ?M5598 ?M5599 ?M5600)
             (@gmultiset_subseteq ?M5598 ?M5599 ?M5600)), id 0)
        simple apply @gmultiset_elem_of_dec (cost 0, pattern 
        @RelDecision ?M5354 (@gmultiset ?M5354 ?M5355 ?M5356)
          (@elem_of ?M5354 (@gmultiset ?M5354 ?M5355 ?M5356)
             (@gmultiset_elem_of ?M5354 ?M5355 ?M5356)), id 0)
        simple apply @gmultiset_eq_dec (cost 0, pattern 
        @RelDecision (@gmultiset ?M5300 ?M5301 ?M5302)
          (@gmultiset ?M5300 ?M5301 ?M5302)
          (@eq (@gmultiset ?M5300 ?M5301 ?M5302)), id 0)
        simple apply @coGset_elem_of_dec (cost 0, pattern 
        @RelDecision ?M5270 (@coGset ?M5270 ?M5271 ?M5272)
          (@elem_of ?M5270 (@coGset ?M5270 ?M5271 ?M5272)
             (@coGset_elem_of ?M5270 ?M5271 ?M5272)), id 0)
        simple apply @coGset_eq_dec (cost 0, pattern 
        @RelDecision (@coGset ?M5237 ?M5238 ?M5239)
          (@coGset ?M5237 ?M5238 ?M5239) (@eq (@coGset ?M5237 ?M5238 ?M5239)), id 0)
        exact mapset_subseteq_dec (cost 0, pattern 
        @RelDecision coPset coPset
          (@subseteq coPset
             (@set_subseteq_instance positive coPset coPset_elem_of)), id 0)
        exact mapset_disjoint_dec (cost 0, pattern 
        @RelDecision coPset coPset
          (@disjoint coPset
             (@set_disjoint_instance positive coPset coPset_elem_of)), id 0)
        exact coPset_equiv_dec (cost 0, pattern @RelDecision coPset coPset
                                                 (@equiv coPset
                                                 (@set_equiv_instance
                                                 positive coPset
                                                 coPset_elem_of)), id 0)
        exact coPset_elem_of_dec (cost 0, pattern 
        @RelDecision positive coPset
          (@elem_of positive coPset coPset_elem_of), id 0)
        exact coPset_eq_dec (cost 0, pattern @RelDecision coPset coPset
                                               (@eq coPset), id 0)
        simple apply @gset_subseteq_dec (cost 0, pattern 
        @RelDecision (@gset ?M5185 ?M5186 ?M5187)
          (@gset ?M5185 ?M5186 ?M5187)
          (@subseteq (@gset ?M5185 ?M5186 ?M5187)
             (@set_subseteq_instance ?M5185 (@gset ?M5185 ?M5186 ?M5187)
                (@gset_elem_of ?M5185 ?M5186 ?M5187))), id 0)
        simple apply @gset_disjoint_dec (cost 0, pattern 
        @RelDecision (@gset ?M5182 ?M5183 ?M5184)
          (@gset ?M5182 ?M5183 ?M5184)
          (@disjoint (@gset ?M5182 ?M5183 ?M5184)
             (@set_disjoint_instance ?M5182 (@gset ?M5182 ?M5183 ?M5184)
                (@gset_elem_of ?M5182 ?M5183 ?M5184))), id 0)
        simple apply @gset_eq_dec (cost 0, pattern 
        @RelDecision (@gset ?M5170 ?M5171 ?M5172)
          (@gset ?M5170 ?M5171 ?M5172) (@eq (@gset ?M5170 ?M5171 ?M5172)), id 0)
        simple apply @boolset_elem_of_dec (cost 0, pattern 
        @RelDecision ?M4655 (boolset ?M4655)
          (@elem_of ?M4655 (boolset ?M4655) (@boolset_elem_of ?M4655)), id 0)
        exact binder_dec_eq (cost 0, pattern @RelDecision binder binder
                                               (@eq binder), id 0)
        exact String.le_dec (cost 0, pattern @RelDecision string string
                                               String.le, id 0)
        exact String.eq_dec (cost 0, pattern @RelDecision string string
                                               (@eq string), id 0)
        exact Ascii.eq_dec (cost 0, pattern @RelDecision Ascii.ascii
                                              Ascii.ascii 
                                              (@eq Ascii.ascii), id 0)
        simple apply @fin_dec (cost 0, pattern @RelDecision 
                                                 (Fin.t ?M2436)
                                                 (Fin.t ?M2436)
                                                 (@eq (Fin.t ?M2436)), id 0)
        exact Qp.lt_dec (cost 0, pattern @RelDecision Qp Qp Qp.lt, id 0)
        exact Qp.le_dec (cost 0, pattern @RelDecision Qp Qp Qp.le, id 0)
        exact Qp.eq_dec (cost 0, pattern @RelDecision Qp Qp (@eq Qp), id 0)
        exact Qc_lt_dec (cost 0, pattern @RelDecision Qcanon.Qc Qcanon.Qc
                                           Qcanon.Qclt, id 0)
        exact Qc_le_dec (cost 0, pattern @RelDecision Qcanon.Qc Qcanon.Qc
                                           Qcanon.Qcle, id 0)
        exact Qc_eq_dec (cost 0, pattern @RelDecision Qcanon.Qc Qcanon.Qc
                                           (@eq Qcanon.Qc), id 0)
        exact Z.gt_dec (cost 0, pattern @RelDecision Z Z Z.gt, id 0)
        exact Z.ge_dec (cost 0, pattern @RelDecision Z Z Z.ge, id 0)
        exact Z.lt_dec (cost 0, pattern @RelDecision Z Z Z.lt, id 0)
        exact Z.le_dec (cost 0, pattern @RelDecision Z Z Z.le, id 0)
        exact Z.eq_dec (cost 0, pattern @RelDecision Z Z (@eq Z), id 0)
        exact N.lt_dec (cost 0, pattern @RelDecision N N N.lt, id 0)
        exact N.le_dec (cost 0, pattern @RelDecision N N N.le, id 0)
        exact N.eq_dec (cost 0, pattern @RelDecision N N (@eq N), id 0)
        exact Pos.lt_dec (cost 0, pattern @RelDecision positive positive
                                            Pos.lt, id 0)
        exact Pos.le_dec (cost 0, pattern @RelDecision positive positive
                                            Pos.le, id 0)
        exact Pos.eq_dec (cost 0, pattern @RelDecision positive positive
                                            (@eq positive), id 0)
        exact Nat.divide_dec (cost 0, pattern @RelDecision nat nat Nat.divide, id 0)
        exact Nat.lt_dec (cost 0, pattern @RelDecision nat nat Nat.lt, id 0)
        exact Nat.le_dec (cost 0, pattern @RelDecision nat nat Nat.le, id 0)
        exact Nat.eq_dec (cost 0, pattern @RelDecision nat nat (@eq nat), id 0)
        exact comparison_eq_dec (cost 0, pattern @RelDecision comparison
                                                 comparison 
                                                 (@eq comparison), id 0)
        exact Empty_set_eq_dec (cost 0, pattern @RelDecision Empty_set
                                                 Empty_set 
                                                 (@eq Empty_set), id 0)
        exact unit_eq_dec (cost 0, pattern @RelDecision unit unit (@eq unit), id 0)
        exact bool_eq_dec (cost 0, pattern @RelDecision bool bool (@eq bool), id 0)
        simple apply @topGset_subseteq_dec (cost 1, pattern 
        @RelDecision (@topGset ?M5939 ?M5940 ?M5941)
          (@topGset ?M5939 ?M5940 ?M5941)
          (@subseteq (@topGset ?M5939 ?M5940 ?M5941)
             (@set_subseteq_instance ?M5939 (@topGset ?M5939 ?M5940 ?M5941)
                (@topGset_elem_of ?M5939 ?M5940 ?M5941))), id 0)
        simple apply @topGset_disjoint_dec (cost 1, pattern 
        @RelDecision (@topGset ?M5935 ?M5936 ?M5937)
          (@topGset ?M5935 ?M5936 ?M5937)
          (@disjoint (@topGset ?M5935 ?M5936 ?M5937)
             (@set_disjoint_instance ?M5935 (@topGset ?M5935 ?M5936 ?M5937)
                (@topGset_elem_of ?M5935 ?M5936 ?M5937))), id 0)
        simple apply @topGset_equiv_dec (cost 1, pattern 
        @RelDecision (@topGset ?M5931 ?M5932 ?M5933)
          (@topGset ?M5931 ?M5932 ?M5933)
          (@equiv (@topGset ?M5931 ?M5932 ?M5933)
             (@set_equiv_instance ?M5931 (@topGset ?M5931 ?M5932 ?M5933)
                (@topGset_elem_of ?M5931 ?M5932 ?M5933))), id 0)
        simple apply @Nmap_eq_dec (cost 1, pattern 
        @RelDecision (Nmap ?M5819) (Nmap ?M5819) (@eq (Nmap ?M5819)), id 0)
        simple apply @natmap_eq_dec (cost 1, pattern 
        @RelDecision (natmap ?M5812) (natmap ?M5812) 
          (@eq (natmap ?M5812)), id 0)
        simple apply @Zmap_eq_dec (cost 1, pattern 
        @RelDecision (Zmap ?M5635) (Zmap ?M5635) (@eq (Zmap ?M5635)), id 0)
        simple apply @coGset_subseteq_dec (cost 1, pattern 
        @RelDecision (@coGset ?M5285 ?M5286 ?M5287)
          (@coGset ?M5285 ?M5286 ?M5287)
          (@subseteq (@coGset ?M5285 ?M5286 ?M5287)
             (@set_subseteq_instance ?M5285 (@coGset ?M5285 ?M5286 ?M5287)
                (@coGset_elem_of ?M5285 ?M5286 ?M5287))), id 0)
        simple apply @coGset_disjoint_dec (cost 1, pattern 
        @RelDecision (@coGset ?M5281 ?M5282 ?M5283)
          (@coGset ?M5281 ?M5282 ?M5283)
          (@disjoint (@coGset ?M5281 ?M5282 ?M5283)
             (@set_disjoint_instance ?M5281 (@coGset ?M5281 ?M5282 ?M5283)
                (@coGset_elem_of ?M5281 ?M5282 ?M5283))), id 0)
        simple apply @coGset_equiv_dec (cost 1, pattern 
        @RelDecision (@coGset ?M5277 ?M5278 ?M5279)
          (@coGset ?M5277 ?M5278 ?M5279)
          (@equiv (@coGset ?M5277 ?M5278 ?M5279)
             (@set_equiv_instance ?M5277 (@coGset ?M5277 ?M5278 ?M5279)
                (@coGset_elem_of ?M5277 ?M5278 ?M5279))), id 0)
        simple apply @gset_elem_of_dec (cost 1, pattern 
        @RelDecision ?M5179 (@gset ?M5179 ?M5180 ?M5181)
          (@elem_of ?M5179 (@gset ?M5179 ?M5180 ?M5181)
             (@gset_elem_of ?M5179 ?M5180 ?M5181)), id 0)
        simple apply @gset_equiv_dec (cost 1, pattern 
        @RelDecision (@gset ?M5176 ?M5177 ?M5178)
          (@gset ?M5176 ?M5177 ?M5178)
          (@equiv (@gset ?M5176 ?M5177 ?M5178)
             (@set_equiv_instance ?M5176 (@gset ?M5176 ?M5177 ?M5178)
                (@gset_elem_of ?M5176 ?M5177 ?M5178))), id 0)
        simple apply @gmap_eq_dec (cost 1, pattern 
        @RelDecision (@gmap ?M5110 ?M5111 ?M5112 ?M5113)
          (@gmap ?M5110 ?M5111 ?M5112 ?M5113)
          (@eq (@gmap ?M5110 ?M5111 ?M5112 ?M5113)), id 0)
        simple apply @Pmap_eq_dec (cost 1, pattern 
        @RelDecision (Pmap ?M5087) (Pmap ?M5087) (@eq (Pmap ?M5087)), id 0)
        simple apply @Pmap_ne_eq_dec (cost 1, pattern 
        @RelDecision (Pmap_ne ?M5085) (Pmap_ne ?M5085) 
          (@eq (Pmap_ne ?M5085)), id 0)
        simple apply @mapset_elem_of_dec (cost 1, pattern 
        @RelDecision ?M5058 (mapset' (?M5059 unit))
          (@elem_of ?M5058 (mapset' (?M5059 unit))
             (@mapset_elem_of ?M5058 ?M5059 ?M5060)), id 0)
        simple eapply @mapset_equiv_dec (cost 1, pattern 
        @RelDecision (mapset' (?M5047 unit)) (mapset' (?M5047 unit))
          (@equiv (mapset' (?M5047 unit))
             (@set_equiv_instance ?M5046 (mapset' (?M5047 unit))
                (@mapset_elem_of ?M5046 ?M5047 ?M5049))), id 0)
        simple apply @mapset_eq_dec (cost 1, pattern 
        @RelDecision (mapset' (?M5040 unit)) (mapset' (?M5040 unit))
          (@eq (mapset' (?M5040 unit))), id 0)
        simple apply @listset_elem_of_dec (cost 1, pattern 
        @RelDecision ?M4593 (listset ?M4593)
          (@elem_of ?M4593 (listset ?M4593) (@listset_elem_of ?M4593)), id 0)
        simple apply @vec_dec (cost 1, pattern @RelDecision
                                                 (Vector.t ?M2508 ?M2510)
                                                 (Vector.t ?M2508 ?M2510)
                                                 (@eq
                                                 (Vector.t ?M2508 ?M2510)), id 0)
        simple apply @gen_tree_dec (cost 1, pattern 
        @RelDecision (gen_tree ?M2479) (gen_tree ?M2479)
          (@eq (gen_tree ?M2479)), id 0)
        simple apply @list_subseteq_dec (cost 1, pattern 
        @RelDecision (list ?M2239) (list ?M2239)
          (@subseteq (list ?M2239) (@list_subseteq ?M2239)), id 0)
        simple apply @Forall2_dec (cost 1, pattern 
        @RelDecision (list ?M2173) (list ?M2174)
          (@Forall2 ?M2173 ?M2174 ?M2175), id 0)
        simple apply @Permutation_dec (cost 1, pattern 
        @RelDecision (list ?M2159) (list ?M2159) (@Permutation ?M2159), id 0)
        simple apply @submseteq_dec (cost 1, pattern 
        @RelDecision (list ?M2157) (list ?M2157) (@submseteq ?M2157), id 0)
        simple apply @suffix_dec (cost 1, pattern 
        @RelDecision (list ?M2151) (list ?M2151) (@suffix ?M2151), id 0)
        simple apply @prefix_dec (cost 1, pattern 
        @RelDecision (list ?M2149) (list ?M2149) (@prefix ?M2149), id 0)
        simple apply @list_eq_dec (cost 1, pattern 
        @RelDecision (list ?M2120) (list ?M2120) (@eq (list ?M2120)), id 0)
        simple apply @list_elem_of_dec (cost 1, pattern 
        @RelDecision ?M2110 (list ?M2110)
          (@elem_of ?M2110 (list ?M2110) (@list_elem_of ?M2110)), id 0)
        simple apply @option_eq_dec (cost 1, pattern 
        @RelDecision (option ?M1973) (option ?M1973) 
          (@eq (option ?M1973)), id 0)
        simple apply @gmap_dep_eq_dec (cost 2, pattern 
        @RelDecision (gmap_dep ?M5106 ?M5107) (gmap_dep ?M5106 ?M5107)
          (@eq (gmap_dep ?M5106 ?M5107)), id 0)
        simple apply @gmap_dep_ne_eq_dec (cost 2, pattern 
        @RelDecision (gmap_dep_ne ?M5102 ?M5103) (gmap_dep_ne ?M5102 ?M5103)
          (@eq (gmap_dep_ne ?M5102 ?M5103)), id 0)
        simple apply @trichotomyT_dec (cost 2, pattern 
        @RelDecision ?M2499 ?M2499 ?M2500, id 0)
        simple apply @sigT_eq_dec (cost 2, pattern 
        @RelDecision (@sigT ?M1917 ?M1918) (@sigT ?M1917 ?M1918)
          (@eq (@sigT ?M1917 ?M1918)), id 0)
        simple apply @sig_eq_dec (cost 2, pattern 
        @RelDecision (@sig ?M1913 ?M1914) (@sig ?M1913 ?M1914)
          (@eq (@sig ?M1913 ?M1914)), id 0)
        simple apply @sum_eq_dec (cost 2, pattern 
        @RelDecision (sum ?M1904 ?M1906) (sum ?M1904 ?M1906)
          (@eq (sum ?M1904 ?M1906)), id 0)
        simple apply @prod_eq_dec (cost 2, pattern 
        @RelDecision (prod ?M1900 ?M1902) (prod ?M1900 ?M1902)
          (@eq (prod ?M1900 ?M1902)), id 0)
        (*external*) (apply (@flip_dec _)) (cost 3, pattern 
        @RelDecision _ _ (@flip _ _ _ _), id 0)
        simple eapply @mapset.mapset_subseteq_dec (cost 9, pattern 
        @RelDecision (mapset' (?M5074 unit)) (mapset' (?M5074 unit))
          (@subseteq (mapset' (?M5074 unit))
             (@set_subseteq_instance ?M5073 (mapset' (?M5074 unit))
                (@mapset_elem_of ?M5073 ?M5074 ?M5076))), id 0)
        simple eapply @mapset.mapset_disjoint_dec (cost 9, pattern 
        @RelDecision (mapset' (?M5062 unit)) (mapset' (?M5062 unit))
          (@disjoint (mapset' (?M5062 unit))
             (@set_disjoint_instance ?M5061 (mapset' (?M5062 unit))
                (@mapset_elem_of ?M5061 ?M5062 ?M5064))), id 0)
        simple eapply @map_relation_dec (cost 11, pattern 
        @RelDecision (?M3928 ?M3938) (?M3928 ?M3939)
          (@map_relation ?M3927 ?M3928 ?M3930 ?M3938 
             ?M3939 ?M3940 ?M3941 ?M3942), id 0)
        simple apply @preorder_subset_dec_slow (cost 100, pattern 
        @RelDecision ?M2492 ?M2492 (@strict ?M2492 ?M2493), id 0)
For CRelationClasses.RewriteRelation ->   simple apply @CRelationClasses.RewriteRelation_instance_2 (cost 0, pattern 
                                          @CRelationClasses.RewriteRelation
                                            (CRelationClasses.crelation ?M425)
                                            (@CRelationClasses.relation_equivalence
                                               ?M425), id 0)
                                          exact CRelationClasses.RewriteRelation_instance_1 (cost 0, pattern 
                                          @CRelationClasses.RewriteRelation
                                            Prop iff, id 0)
                                          exact CRelationClasses.RewriteRelation_instance_0 (cost 0, pattern 
                                          @CRelationClasses.RewriteRelation
                                            Prop impl, id 0)
                                          simple apply @CRelationClasses.equivalence_rewrite_crelation (cost 1, pattern 
                                          @CRelationClasses.RewriteRelation
                                            ?M415 
                                            ?M416, id 0)
For RewriteRelation ->   simple apply @relation_equivalence_rewrite_relation (cost 0, pattern 
                         @RewriteRelation (relation ?M264)
                           (@relation_equivalence ?M264), id 0)
                         (*external*) rewrite_relation_fun (cost 2, pattern 
                         @RewriteRelation (forall H, _) _, id 0)
                         exact iff_rewrite_relation (cost 2, pattern 
                         @RewriteRelation Prop iff, id 0)
                         exact impl_rewrite_relation (cost 3, pattern 
                         @RewriteRelation Prop impl, id 0)
                         exact inverse_impl_rewrite_relation (cost 3, pattern 
                         @RewriteRelation Prop (@flip Prop Prop Prop impl), id 0)
                         (*external*) (equiv_rewrite_relation R) (cost 10, pattern 
                         @RewriteRelation ?A ?R, id 0)
                         (*external*) (eq_rewrite_relation A) (cost 100, pattern 
                         @RewriteRelation ?A _, id 0)
                         simple apply @equiv_rewrite_relation (cost 150, pattern 
                         @RewriteRelation ?M1146 (@equiv ?M1146 ?M1147), id 0)
                         simple apply @sqsubseteq_rewrite (cost 200, pattern 
                         @RewriteRelation ?M1502 (@sqsubseteq ?M1502 ?M1503), id 0)
For RightAbsorb ->   simple apply @gmultiset_intersection_right_absorb (cost 0, pattern 
                     @RightAbsorb (@gmultiset ?M5559 ?M5560 ?M5561)
                       (@eq (@gmultiset ?M5559 ?M5560 ?M5561))
                       (@empty (@gmultiset ?M5559 ?M5560 ?M5561)
                          (@gmultiset_empty ?M5559 ?M5560 ?M5561))
                       (@intersection (@gmultiset ?M5559 ?M5560 ?M5561)
                          (@gmultiset_intersection ?M5559 ?M5560 ?M5561)), id 0)
                     exact Qcmult_right_absorb (cost 0, pattern 
                     @RightAbsorb Qcanon.Qc (@eq Qcanon.Qc)
                       (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)) Qcanon.Qcmult, id 0)
                     exact Z.mul_right_absorb (cost 0, pattern 
                     @RightAbsorb Z (@eq Z) Z0 Z.mul, id 0)
                     exact N.mul_right_absorb (cost 0, pattern 
                     @RightAbsorb N (@eq N) N0 N.mul, id 0)
                     exact Nat.mul_right_absorb (cost 0, pattern 
                     @RightAbsorb nat (@eq nat) O Nat.mul, id 0)
                     simple apply @intersection_with_right_ab (cost 0, pattern 
                     @RightAbsorb (option ?M2025) 
                       (@eq (option ?M2025)) (@None ?M2025)
                       (@intersection_with ?M2025 
                          (option ?M2025) (@option_intersection_with ?M2025)
                          ?M2026), id 0)
                     simple apply @option_intersection_right_absorb (cost 0, pattern 
                     @RightAbsorb (option ?M2014) 
                       (@eq (option ?M2014)) (@None ?M2014)
                       (@intersection (option ?M2014)
                          (@option_intersection ?M2014)), id 0)
                     exact impl_True (cost 0, pattern 
                     @RightAbsorb Prop iff True impl, id 0)
                     exact or_True (cost 0, pattern 
                     @RightAbsorb Prop iff True or, id 0)
                     exact and_False (cost 0, pattern 
                     @RightAbsorb Prop iff False and, id 0)
                     simple eapply @intersection_empty_r (cost 4, pattern 
                     @RightAbsorb ?M3134
                       (@equiv ?M3134
                          (@set_equiv_instance ?M3133 ?M3134 ?M3135))
                       (@empty ?M3134 ?M3136) (@intersection ?M3134 ?M3139), id 0)
                     simple eapply @intersection_empty_r_L (cost 7, pattern 
                     @RightAbsorb ?M3183 (@eq ?M3183) 
                       (@empty ?M3183 ?M3185) (@intersection ?M3183 ?M3188), id 0)
                     simple eapply @map_intersection_empty (cost 8, pattern 
                     @RightAbsorb (?M4103 ?M4113) 
                       (@eq (?M4103 ?M4113))
                       (@empty (?M4103 ?M4113) (?M4106 ?M4113))
                       (@intersection (?M4103 ?M4113)
                          (@map_intersection ?M4103 ?M4109 ?M4113)), id 0)
                     simple eapply @RightAbsorb_instance_1 (cost 8, pattern 
                     @RightAbsorb (?M4064 ?M4074) 
                       (@eq (?M4064 ?M4074))
                       (@empty (?M4064 ?M4074) (?M4067 ?M4074))
                       (@intersection_with ?M4074 
                          (?M4064 ?M4074)
                          (@map_intersection_with ?M4064 ?M4070 ?M4074)
                          ?M4075), id 0)
                     simple eapply @RightAbsorb_instance_0 (cost 9, pattern 
                     @RightAbsorb (?M3886 ?M3896) 
                       (@eq (?M3886 ?M3896))
                       (@empty (?M3886 ?M3896) (?M3889 ?M3896))
                       (@merge ?M3886 ?M3892 ?M3896 ?M3896 ?M3896 ?M3897), id 0)
For RightId ->   simple apply @gmultiset_disj_union_right_id (cost 0, pattern 
                 @RightId (@gmultiset ?M5574 ?M5575 ?M5576)
                   (@eq (@gmultiset ?M5574 ?M5575 ?M5576))
                   (@empty (@gmultiset ?M5574 ?M5575 ?M5576)
                      (@gmultiset_empty ?M5574 ?M5575 ?M5576))
                   (@disj_union (@gmultiset ?M5574 ?M5575 ?M5576)
                      (@gmultiset_disj_union ?M5574 ?M5575 ?M5576)), id 0)
                 simple apply @gmultiset_union_right_id (cost 0, pattern 
                 @RightId (@gmultiset ?M5544 ?M5545 ?M5546)
                   (@eq (@gmultiset ?M5544 ?M5545 ?M5546))
                   (@empty (@gmultiset ?M5544 ?M5545 ?M5546)
                      (@gmultiset_empty ?M5544 ?M5545 ?M5546))
                   (@union (@gmultiset ?M5544 ?M5545 ?M5546)
                      (@gmultiset_union ?M5544 ?M5545 ?M5546)), id 0)
                 simple apply @list.RightId_instance_0 (cost 0, pattern 
                 @RightId (list ?M2119) (@eq (list ?M2119)) 
                   (@nil ?M2119) (@app ?M2119), id 0)
                 exact Qp.div_right_id (cost 0, pattern 
                 @RightId Qp (@eq Qp) (pos_to_Qp xH) Qp.div, id 0)
                 exact Qp.mul_right_id (cost 0, pattern 
                 @RightId Qp (@eq Qp) (pos_to_Qp xH) Qp.mul, id 0)
                 exact Qcdiv_right_id (cost 0, pattern 
                 @RightId Qcanon.Qc (@eq Qcanon.Qc)
                   (Qcanon.Q2Qc (QArith_base.Qmake (Zpos xH) xH))
                   Qcanon.Qcdiv, id 0)
                 exact Qcmult_right_id (cost 0, pattern 
                 @RightId Qcanon.Qc (@eq Qcanon.Qc)
                   (Qcanon.Q2Qc (QArith_base.Qmake (Zpos xH) xH))
                   Qcanon.Qcmult, id 0)
                 exact Qcminus_right_id (cost 0, pattern 
                 @RightId Qcanon.Qc (@eq Qcanon.Qc)
                   (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)) Qcanon.Qcminus, id 0)
                 exact Qcplus_right_id (cost 0, pattern 
                 @RightId Qcanon.Qc (@eq Qcanon.Qc)
                   (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)) Qcanon.Qcplus, id 0)
                 exact Z.div_right_id (cost 0, pattern 
                 @RightId Z (@eq Z) (Zpos xH) Z.div, id 0)
                 exact Z.mul_right_id (cost 0, pattern 
                 @RightId Z (@eq Z) (Zpos xH) Z.mul, id 0)
                 exact Z.sub_right_id (cost 0, pattern 
                 @RightId Z (@eq Z) Z0 Z.sub, id 0)
                 exact Z.add_right_id (cost 0, pattern 
                 @RightId Z (@eq Z) Z0 Z.add, id 0)
                 exact N.div_right_id (cost 0, pattern 
                 @RightId N (@eq N) (Npos xH) N.div, id 0)
                 exact N.mul_right_id (cost 0, pattern 
                 @RightId N (@eq N) (Npos xH) N.mul, id 0)
                 exact N.sub_right_id (cost 0, pattern 
                 @RightId N (@eq N) N0 N.sub, id 0)
                 exact N.add_right_id (cost 0, pattern 
                 @RightId N (@eq N) N0 N.add, id 0)
                 exact Pos.app_1_r (cost 0, pattern 
                 @RightId positive (@eq positive) xH Pos.app, id 0)
                 exact Pos.mul_right_id (cost 0, pattern 
                 @RightId positive (@eq positive) xH Pos.mul, id 0)
                 exact Nat.div_right_id (cost 0, pattern 
                 @RightId nat (@eq nat) (S O) Nat.div, id 0)
                 exact Nat.mul_right_id (cost 0, pattern 
                 @RightId nat (@eq nat) (S O) Nat.mul, id 0)
                 exact Nat.sub_right_id (cost 0, pattern 
                 @RightId nat (@eq nat) O Nat.sub, id 0)
                 exact Nat.add_right_id (cost 0, pattern 
                 @RightId nat (@eq nat) O Nat.add, id 0)
                 simple apply @difference_with_right_id (cost 0, pattern 
                 @RightId (option ?M2033) (@eq (option ?M2033))
                   (@None ?M2033)
                   (@difference_with ?M2033 (option ?M2033)
                      (@option_difference_with ?M2033) 
                      ?M2034), id 0)
                 simple apply @union_with_right_id (cost 0, pattern 
                 @RightId (option ?M2018) (@eq (option ?M2018))
                   (@None ?M2018)
                   (@union_with ?M2018 (option ?M2018)
                      (@option_union_with ?M2018) 
                      ?M2019), id 0)
                 simple apply @option_union_right_id (cost 0, pattern 
                 @RightId (option ?M2012) (@eq (option ?M2012))
                   (@None ?M2012)
                   (@union (option ?M2012) (@option_union ?M2012)), id 0)
                 exact or_False (cost 0, pattern @RightId Prop iff False or, id 0)
                 exact and_True (cost 0, pattern @RightId Prop iff True and, id 0)
                 simple eapply @union_empty_r (cost 2, pattern 
                 @RightId ?M3006
                   (@equiv ?M3006 (@set_equiv_instance ?M3005 ?M3006 ?M3007))
                   (@empty ?M3006 ?M3008) (@union ?M3006 ?M3010), id 0)
                 simple eapply @union_empty_r_L (cost 5, pattern 
                 @RightId ?M3065 (@eq ?M3065) (@empty ?M3065 ?M3067)
                   (@union ?M3065 ?M3069), id 0)
                 simple eapply @map_difference_right_id (cost 8, pattern 
                 @RightId (?M4139 ?M4149) (@eq (?M4139 ?M4149))
                   (@empty (?M4139 ?M4149) (?M4142 ?M4149))
                   (@difference (?M4139 ?M4149)
                      (@map_difference ?M4139 ?M4145 ?M4149)), id 0)
                 simple eapply @map_union_empty (cost 8, pattern 
                 @RightId (?M4011 ?M4021) (@eq (?M4011 ?M4021))
                   (@empty (?M4011 ?M4021) (?M4014 ?M4021))
                   (@union (?M4011 ?M4021) (@map_union ?M4011 ?M4017 ?M4021)), id 0)
                 simple eapply @RightId_instance_1 (cost 8, pattern 
                 @RightId (?M3972 ?M3982) (@eq (?M3972 ?M3982))
                   (@empty (?M3972 ?M3982) (?M3975 ?M3982))
                   (@union_with ?M3982 (?M3972 ?M3982)
                      (@map_union_with ?M3972 ?M3978 ?M3982) 
                      ?M3983), id 0)
                 simple eapply @RightId_instance_0 (cost 9, pattern 
                 @RightId (?M3858 ?M3868) (@eq (?M3858 ?M3868))
                   (@empty (?M3858 ?M3868) (?M3861 ?M3868))
                   (@merge ?M3858 ?M3864 ?M3868 ?M3868 ?M3868 ?M3869), id 0)
For ZifyClasses.Saturate ->   exact ZifyInst.SatPowNonneg (cost 0, pattern 
                              @ZifyClasses.Saturate Z Z.pow, id 0)
                              exact ZifyInst.SatPowPos (cost 0, pattern 
                              @ZifyClasses.Saturate Z Z.pow, id 0)
For ScalarMul (modes -
!) ->   simple apply @gmultiset_scalar_mul (cost 0, pattern 
        ScalarMul nat (@gmultiset ?M5339 ?M5340 ?M5341), id 0)
For SemiSet (modes - ! - - -
-) ->   simple apply @topGset_set (cost 0, pattern 
        @SemiSet ?M5918 (@topGset ?M5918 ?M5919 ?M5920)
          (@topGset_elem_of ?M5918 ?M5919 ?M5920)
          (@topGset_empty ?M5918 ?M5919 ?M5920)
          (@topGset_singleton ?M5918 ?M5919 ?M5920)
          (@topGset_union ?M5918 ?M5919 ?M5920), id 0)
        simple apply @listset_simple_set (cost 0, pattern 
        @SemiSet ?M4590 (listset ?M4590) (@listset_elem_of ?M4590)
          (@listset_empty ?M4590) (@listset_singleton ?M4590)
          (@listset_union ?M4590), id 0)
        simple apply @gset_semi_set (cost 1, pattern 
        @SemiSet ?M5195 (@gset ?M5195 ?M5196 ?M5197)
          (@gset_elem_of ?M5195 ?M5196 ?M5197)
          (@gset_empty ?M5195 ?M5196 ?M5197)
          (@gset_singleton ?M5195 ?M5196 ?M5197)
          (@gset_union ?M5195 ?M5196 ?M5197), id 0)
        simple eapply @set_semi_set (cost 3, pattern 
        @SemiSet ?M5966 ?M5967 ?M5968 ?M5969 ?M5970 
          ?M5971, id 0)
        simple eapply @monad_set_semi_set (cost 5, pattern 
        @SemiSet ?M5996 (?M5986 ?M5996) (?M5987 ?M5996) 
          (?M5988 ?M5996) (?M5989 ?M5996) (?M5990 ?M5996), id 0)
For SetUnfold (modes + -) ->   simple apply @set_unfold_multiset_subset (cost 0, pattern 
        SetUnfold
          (@strict (@gmultiset ?M5466 ?M5467 ?M5468)
             (@subseteq (@gmultiset ?M5466 ?M5467 ?M5468)
                (@gmultiset_subseteq ?M5466 ?M5467 ?M5468))
             ?M5469 ?M5470)
          (and (forall x : ?M5466, le (?M5471 x) (?M5472 x))
             (not (forall x : ?M5466, le (?M5472 x) (?M5471 x)))), id 0)
        simple apply @set_unfold_multiset_subseteq (cost 0, pattern 
        SetUnfold
          (@subseteq (@gmultiset ?M5457 ?M5458 ?M5459)
             (@gmultiset_subseteq ?M5457 ?M5458 ?M5459) 
             ?M5460 ?M5461)
          (forall x : ?M5457, le (?M5462 x) (?M5463 x)), id 0)
        simple apply @set_unfold_multiset_eq (cost 0, pattern 
        SetUnfold (@eq (@gmultiset ?M5448 ?M5449 ?M5450) ?M5451 ?M5452)
          (forall x : ?M5448, @eq nat (?M5453 x) (?M5454 x)), id 0)
        simple apply @set_unfold_multiset_equiv (cost 0, pattern 
        SetUnfold
          (@equiv (@gmultiset ?M5439 ?M5440 ?M5441)
             (@gmultiset_equiv ?M5439 ?M5440 ?M5441) 
             ?M5442 ?M5443)
          (forall x : ?M5439, @eq nat (?M5444 x) (?M5445 x)), id 0)
        (*external*) (class_apply @set_unfold_exist) (cost 0, pattern 
        SetUnfold (@ex _ (fun H => _)) _, id 0)
        (*external*) (class_apply set_unfold_not) (cost 0, pattern 
        SetUnfold (not _) _, id 0)
        (*external*) (class_apply set_unfold_iff) (cost 0, pattern 
        SetUnfold (iff _ _) _, id 0)
        (*external*) (class_apply set_unfold_or) (cost 0, pattern 
        SetUnfold (or _ _) _, id 0)
        (*external*) (class_apply set_unfold_and) (cost 0, pattern 
        SetUnfold (and _ _) _, id 0)
        (*external*) (class_apply set_unfold_impl) (cost 0, pattern 
        SetUnfold (forall H, _) _, id 0)
        simple apply @set_unfold_equiv_same_L (cost 1, pattern 
        SetUnfold (@eq ?M2761 ?M2762 ?M2762) True, id 0)
        simple apply @set_unfold_equiv_same (cost 1, pattern 
        SetUnfold
          (@equiv ?M2702 (@set_equiv_instance ?M2701 ?M2702 ?M2703) 
             ?M2704 ?M2704)
          True, id 0)
        (*external*) (class_apply @set_unfold_forall) (cost 1, pattern 
        SetUnfold (forall H, _) _, id 0)
        simple apply @set_unfold_elem_of_set_unfold (cost 1, pattern 
        SetUnfold (@elem_of ?M2662 ?M2663 ?M2664 ?M2665 ?M2666) 
          ?M2667, id 0)
        simple apply @set_unfold_set_Exists (cost 2, pattern 
        SetUnfold (@set_Exists ?M3285 ?M3286 ?M3287 ?M3288 ?M3289)
          (@ex ?M3285 (fun x : ?M3285 => and (?M3290 x) (?M3291 x))), id 0)
        simple apply @set_unfold_set_Forall (cost 2, pattern 
        SetUnfold (@set_Forall ?M3276 ?M3277 ?M3278 ?M3279 ?M3280)
          (forall (x : ?M3276) (_ : ?M3281 x), ?M3282 x), id 0)
        simple apply @set_unfold_included (cost 2, pattern 
        SetUnfold
          (@subseteq (list ?M2922) (@list_subseteq ?M2922) ?M2923 ?M2924)
          (forall (x : ?M2922) (_ : ?M2925 x), ?M2926 x), id 0)
        simple apply @set_unfold_disjoint (cost 2, pattern 
        SetUnfold
          (@disjoint ?M2753 (@set_disjoint_instance ?M2752 ?M2753 ?M2754)
             ?M2757 ?M2758)
          (forall (x : ?M2752) (_ : ?M2755 x) (_ : ?M2756 x), False), id 0)
        simple apply @set_unfold_subset (cost 2, pattern 
        SetUnfold
          (@strict ?M2744
             (@subseteq ?M2744 (@set_subseteq_instance ?M2743 ?M2744 ?M2745))
             ?M2748 ?M2749)
          (and (forall (x : ?M2743) (_ : ?M2746 x), ?M2747 x)
             (not (forall (x : ?M2743) (_ : ?M2747 x), ?M2746 x))), id 0)
        simple apply @set_unfold_subseteq (cost 2, pattern 
        SetUnfold
          (@subseteq ?M2735 (@set_subseteq_instance ?M2734 ?M2735 ?M2736)
             ?M2739 ?M2740)
          (forall (x : ?M2734) (_ : ?M2737 x), ?M2738 x), id 0)
        simple eapply @set_unfold_equiv_empty_r_L (cost 5, pattern 
        SetUnfold (@eq ?M2775 ?M2783 (@empty ?M2775 ?M2777))
          (forall x : ?M2774, not (?M2782 x)), id 0)
        simple eapply @set_unfold_equiv_empty_l_L (cost 5, pattern 
        SetUnfold (@eq ?M2764 (@empty ?M2764 ?M2766) ?M2771)
          (forall x : ?M2763, not (?M2772 x)), id 0)
        simple eapply @set_unfold_equiv_empty_r (cost 5, pattern 
        SetUnfold
          (@equiv ?M2716 (@set_equiv_instance ?M2715 ?M2716 ?M2717) 
             ?M2723 (@empty ?M2716 ?M2718))
          (forall x : ?M2715, not (?M2722 x)), id 0)
        simple eapply @set_unfold_equiv_empty_l (cost 5, pattern 
        SetUnfold
          (@equiv ?M2706 (@set_equiv_instance ?M2705 ?M2706 ?M2707)
             (@empty ?M2706 ?M2708) ?M2712)
          (forall x : ?M2705, not (?M2713 x)), id 0)
        simple eapply @set_unfold_equiv_L (cost 10, pattern 
        SetUnfold (@eq ?M2786 ?M2791 ?M2792)
          (forall x : ?M2785, iff (?M2789 x) (?M2790 x)), id 0)
        simple apply @set_unfold_equiv (cost 10, pattern 
        SetUnfold
          (@equiv ?M2726 (@set_equiv_instance ?M2725 ?M2726 ?M2727) 
             ?M2730 ?M2731)
          (forall x : ?M2725, iff (?M2728 x) (?M2729 x)), id 0)
        simple eapply @set_unfold_map_disjoint (cost 17, pattern 
        SetUnfold (@map_disjoint ?M4954 ?M4955 ?M4959 ?M4973 ?M4974 ?M4975)
          ?M4976, id 0)
        simple apply set_unfold_default (cost 1000, pattern 
        SetUnfold ?M2669 ?M2669, id 0)
For SetUnfoldElemOf (modes + + + - + -) ->   simple apply @set_unfold_gmultiset_dom (cost 0, pattern 
        @SetUnfoldElemOf ?M5530 (@gset ?M5530 ?M5531 ?M5532)
          (@gset_elem_of ?M5530 ?M5531 ?M5532) ?M5533
          (@dom (@gmultiset ?M5530 ?M5531 ?M5532)
             (@gset ?M5530 ?M5531 ?M5532)
             (@gmultiset_dom ?M5530 ?M5531 ?M5532) 
             ?M5534)
          (@elem_of ?M5530 (@gmultiset ?M5530 ?M5531 ?M5532)
             (@gmultiset_elem_of ?M5530 ?M5531 ?M5532) 
             ?M5533 ?M5534), id 0)
        simple apply @set_unfold_gmultiset_singleton (cost 0, pattern 
        @SetUnfoldElemOf ?M5486 (@gmultiset ?M5486 ?M5487 ?M5488)
          (@gmultiset_elem_of ?M5486 ?M5487 ?M5488) 
          ?M5489
          (@singletonMS ?M5486 (@gmultiset ?M5486 ?M5487 ?M5488)
             (@gmultiset_singleton ?M5486 ?M5487 ?M5488) 
             ?M5490)
          (@eq ?M5486 ?M5489 ?M5490), id 0)
        simple apply @set_unfold_gmultiset_empty (cost 0, pattern 
        @SetUnfoldElemOf ?M5482 (@gmultiset ?M5482 ?M5483 ?M5484)
          (@gmultiset_elem_of ?M5482 ?M5483 ?M5484) 
          ?M5485
          (@empty (@gmultiset ?M5482 ?M5483 ?M5484)
             (@gmultiset_empty ?M5482 ?M5483 ?M5484))
          False, id 0)
        simple apply @set_unfold_elem_of_mfail (cost 0, pattern 
        @SetUnfoldElemOf ?M3257 (?M3247 ?M3257) (?M3248 ?M3257) 
          ?M3258
          (@mthrow unit ?M3247
             (@set_mfail ?M3247 ?M3248 ?M3249 ?M3250 
                ?M3251 ?M3252 ?M3253 ?M3254 ?M3255 
                ?M3256)
             ?M3257 tt)
          False, id 0)
        simple apply set_unfold_list_seqZ (cost 0, pattern 
        @SetUnfoldElemOf Z (list Z) (@list_elem_of Z) 
          ?M2959 (seqZ ?M2960 ?M2961)
          (and (Z.le ?M2960 ?M2959) (Z.lt ?M2959 (Z.add ?M2960 ?M2961))), id 0)
        simple apply set_unfold_list_seq (cost 0, pattern 
        @SetUnfoldElemOf nat (list nat) (@list_elem_of nat) 
          ?M2956 (seq ?M2957 ?M2958)
          (and (le ?M2957 ?M2956) (lt ?M2956 (Init.Nat.add ?M2957 ?M2958))), id 0)
        simple apply @set_unfold_nil (cost 0, pattern 
        @SetUnfoldElemOf ?M2897 (list ?M2897) (@list_elem_of ?M2897) 
          ?M2898 (@nil ?M2897) False, id 0)
        simple apply @set_unfold_PropSet (cost 1, pattern 
        @SetUnfoldElemOf ?M5835 (propset ?M5835) (@propset_elem_of ?M5835)
          ?M5837 (@PropSet ?M5835 ?M5836) ?M5838, id 0)
        simple apply @set_unfold_gmultiset_map (cost 1, pattern 
        @SetUnfoldElemOf ?M5612 (@gmultiset ?M5612 ?M5613 ?M5614)
          (@gmultiset_elem_of ?M5612 ?M5613 ?M5614) 
          ?M5618
          (@gmultiset_map ?M5609 ?M5610 ?M5611 ?M5612 
             ?M5613 ?M5614 ?M5615 ?M5616)
          (@ex ?M5609
             (fun x : ?M5609 => and (@eq ?M5612 ?M5618 (?M5615 x)) (?M5617 x))), id 0)
        simple apply @set_unfold_gmultiset_filter (cost 1, pattern 
        @SetUnfoldElemOf ?M5521 (@gmultiset ?M5521 ?M5522 ?M5523)
          (@gmultiset_elem_of ?M5521 ?M5522 ?M5523) 
          ?M5526
          (@filter ?M5521 (@gmultiset ?M5521 ?M5522 ?M5523)
             (@gmultiset_filter ?M5521 ?M5522 ?M5523) 
             ?M5524 ?M5525 ?M5527)
          (and (?M5524 ?M5526) ?M5528), id 0)
        simple apply set_unfold_gset_to_coPSet (cost 1, pattern 
        @SetUnfoldElemOf positive coPset coPset_elem_of 
          ?M5232 (gset_to_coPset ?M5233) ?M5234, id 0)
        simple apply set_unfold_Pset_to_coPSet (cost 1, pattern 
        @SetUnfoldElemOf positive coPset coPset_elem_of 
          ?M5228 (Pset_to_coPset ?M5229) ?M5230, id 0)
        simple apply set_unfold_cons_binder (cost 1, pattern 
        @SetUnfoldElemOf string (list string) (@list_elem_of string) 
          ?M4560 (cons_binder ?M4561 ?M4562)
          (or (@eq binder (BNamed ?M4560) ?M4561) ?M4563), id 0)
        simple apply @set_unfold_seq (cost 1, pattern 
        @SetUnfoldElemOf nat ?M3365 ?M3366 ?M3373
          (@set_seq ?M3365 ?M3368 ?M3369 ?M3367 ?M3371 ?M3372)
          (and (le ?M3371 ?M3373) (lt ?M3373 (Init.Nat.add ?M3371 ?M3372))), id 0)
        simple apply @set_unfold_guard (cost 1, pattern 
        @SetUnfoldElemOf ?M3271 (?M3259 ?M3271) (?M3260 ?M3271) 
          ?M3272
          (@mbind ?M3259 ?M3264 ?M3269 ?M3271 (fun _ : ?M3269 => ?M3273)
             (@guard_or unit tt ?M3259
                (@set_mfail ?M3259 ?M3260 ?M3261 ?M3262 
                   ?M3263 ?M3264 ?M3265 ?M3266 ?M3267 
                   ?M3268)
                ?M3265 ?M3269 ?M3270))
          (and ?M3269 ?M3274), id 0)
        simple apply @set_unfold_fin_to_set (cost 1, pattern 
        @SetUnfoldElemOf ?M3227 ?M3228 ?M3229 ?M3236
          (@fin_to_set ?M3227 ?M3228 ?M3231 ?M3230 ?M3232 ?M3234 ?M3235) True, id 0)
        simple apply @set_unfold_rotate (cost 1, pattern 
        @SetUnfoldElemOf ?M2941 (list ?M2941) (@list_elem_of ?M2941) 
          ?M2942 (@rotate ?M2941 ?M2945 ?M2943) ?M2944, id 0)
        simple apply @set_unfold_list_fmap (cost 1, pattern 
        @SetUnfoldElemOf ?M2935 (list ?M2935) (@list_elem_of ?M2935) 
          ?M2939 (@fmap list list_fmap ?M2934 ?M2935 ?M2936 ?M2937)
          (@ex ?M2934
             (fun x : ?M2934 => and (@eq ?M2935 ?M2939 (?M2936 x)) (?M2938 x))), id 0)
        simple apply @set_unfold_reverse (cost 1, pattern 
        @SetUnfoldElemOf ?M2929 (list ?M2929) (@list_elem_of ?M2929) 
          ?M2930 (@reverse ?M2929 ?M2931) ?M2932, id 0)
        simple apply @set_unfold_cons (cost 1, pattern 
        @SetUnfoldElemOf ?M2899 (list ?M2899) (@list_elem_of ?M2899) 
          ?M2900 (@cons ?M2899 ?M2901 ?M2902)
          (or (@eq ?M2899 ?M2900 ?M2901) ?M2903), id 0)
        simple apply @set_unfold_top (cost 1, pattern 
        @SetUnfoldElemOf ?M2827 ?M2828 ?M2829 ?M2832 
          (@top ?M2828 ?M2830) True, id 0)
        simple apply @set_unfold_gmultiset_intersection (cost 2, pattern 
        @SetUnfoldElemOf ?M5511 (@gmultiset ?M5511 ?M5512 ?M5513)
          (@gmultiset_elem_of ?M5511 ?M5512 ?M5513) 
          ?M5514
          (@intersection (@gmultiset ?M5511 ?M5512 ?M5513)
             (@gmultiset_intersection ?M5511 ?M5512 ?M5513) 
             ?M5515 ?M5516)
          (and ?M5517 ?M5518), id 0)
        simple apply @set_unfold_gmultiset_disj_union (cost 2, pattern 
        @SetUnfoldElemOf ?M5501 (@gmultiset ?M5501 ?M5502 ?M5503)
          (@gmultiset_elem_of ?M5501 ?M5502 ?M5503) 
          ?M5504
          (@disj_union (@gmultiset ?M5501 ?M5502 ?M5503)
             (@gmultiset_disj_union ?M5501 ?M5502 ?M5503) 
             ?M5505 ?M5506)
          (or ?M5507 ?M5508), id 0)
        simple apply @set_unfold_gmultiset_union (cost 2, pattern 
        @SetUnfoldElemOf ?M5491 (@gmultiset ?M5491 ?M5492 ?M5493)
          (@gmultiset_elem_of ?M5491 ?M5492 ?M5493) 
          ?M5494
          (@union (@gmultiset ?M5491 ?M5492 ?M5493)
             (@gmultiset_union ?M5491 ?M5492 ?M5493) 
             ?M5495 ?M5496)
          (or ?M5497 ?M5498), id 0)
        simple apply @set_unfold_gset_cprod (cost 2, pattern 
        @SetUnfoldElemOf (prod ?M5213 ?M5216)
          (@gset (prod ?M5213 ?M5216)
             (@prod_eq_dec ?M5213 ?M5214 ?M5216 ?M5217)
             (@prod_countable ?M5213 ?M5214 ?M5215 ?M5216 ?M5217 ?M5218))
          (@gset_elem_of (prod ?M5213 ?M5216)
             (@prod_eq_dec ?M5213 ?M5214 ?M5216 ?M5217)
             (@prod_countable ?M5213 ?M5214 ?M5215 ?M5216 ?M5217 ?M5218))
          ?M5221
          (@cprod (@gset ?M5213 ?M5214 ?M5215) (@gset ?M5216 ?M5217 ?M5218)
             (@gset (prod ?M5213 ?M5216)
                (@prod_eq_dec ?M5213 ?M5214 ?M5216 ?M5217)
                (@prod_countable ?M5213 ?M5214 ?M5215 ?M5216 ?M5217 ?M5218))
             (@gset_cprod ?M5213 ?M5214 ?M5215 ?M5216 ?M5217 ?M5218) 
             ?M5219 ?M5220)
          (and ?M5222 ?M5223), id 0)
        simple apply @set_unfold_boolset_cprod (cost 2, pattern 
        @SetUnfoldElemOf (prod ?M4656 ?M4657) (boolset (prod ?M4656 ?M4657))
          (@boolset_elem_of (prod ?M4656 ?M4657)) 
          ?M4660
          (@cprod (boolset ?M4656) (boolset ?M4657)
             (boolset (prod ?M4656 ?M4657)) (@boolset_cprod ?M4656 ?M4657)
             ?M4658 ?M4659)
          (and ?M4661 ?M4662), id 0)
        simple apply set_unfold_app_binder (cost 2, pattern 
        @SetUnfoldElemOf string (list string) (@list_elem_of string) 
          ?M4565 (app_binder ?M4566 ?M4567) (or ?M4568 ?M4569), id 0)
        simple apply @set_unfold_list_to_set (cost 2, pattern 
        @SetUnfoldElemOf ?M3201 ?M3202 ?M3203 ?M3209
          (@list_to_set ?M3201 ?M3202 ?M3205 ?M3204 ?M3206 ?M3208) 
          ?M3210, id 0)
        simple eapply @set_unfold_option_to_set (cost 2, pattern 
        @SetUnfoldElemOf ?M3192 ?M3193 ?M3194 ?M3200
          (@option_to_set ?M3192 ?M3193 ?M3196 ?M3195 ?M3199)
          (@eq (option ?M3192) ?M3199 (@Some ?M3192 ?M3200)), id 0)
        simple apply @set_unfold_list_bind (cost 2, pattern 
        @SetUnfoldElemOf ?M2948 (list ?M2948) (@list_elem_of ?M2948) 
          ?M2953 (@mbind list list_bind ?M2947 ?M2948 ?M2949 ?M2950)
          (@ex ?M2947 (fun x : ?M2947 => and (?M2952 x) (?M2951 x))), id 0)
        simple apply @set_unfold_list_cprod (cost 2, pattern 
        @SetUnfoldElemOf (prod ?M2913 ?M2914) (list (prod ?M2913 ?M2914))
          (@list_elem_of (prod ?M2913 ?M2914)) ?M2915
          (@cprod (list ?M2913) (list ?M2914) (list (prod ?M2913 ?M2914))
             (@list_cprod ?M2913 ?M2914) ?M2916 ?M2917)
          (and ?M2918 ?M2919), id 0)
        simple apply @set_unfold_app (cost 2, pattern 
        @SetUnfoldElemOf ?M2905 (list ?M2905) (@list_elem_of ?M2905) 
          ?M2906 (@app ?M2905 ?M2907 ?M2908) (or ?M2909 ?M2910), id 0)
        simple eapply @set_unfold_singleton (cost 3, pattern 
        @SetUnfoldElemOf ?M2678 ?M2679 ?M2680 ?M2685
          (@singleton ?M2678 ?M2679 ?M2682 ?M2686) 
          (@eq ?M2678 ?M2685 ?M2686), id 0)
        simple eapply @set_unfold_empty (cost 3, pattern 
        @SetUnfoldElemOf ?M2670 ?M2671 ?M2672 ?M2677 
          (@empty ?M2671 ?M2673) False, id 0)
        simple eapply @set_unfold_filter (cost 5, pattern 
        @SetUnfoldElemOf ?M3447 ?M3448 ?M3449 ?M3462
          (@filter ?M3447 ?M3448
             (@set_filter ?M3447 ?M3448 ?M3455 ?M3450 ?M3451 ?M3452) 
             ?M3458 ?M3459 ?M3460)
          (and (?M3458 ?M3462) ?M3461), id 0)
        simple eapply @set_unfold_union (cost 5, pattern 
        @SetUnfoldElemOf ?M2687 ?M2688 ?M2689 ?M2694
          (@union ?M2688 ?M2692 ?M2695 ?M2696) (or ?M2697 ?M2698), id 0)
        simple eapply @set_unfold_map_img_singleton (cost 7, pattern 
        @SetUnfoldElemOf ?M4550 ?M4551 ?M4552 ?M4557
          (@map_img ?M4539 ?M4550 (?M4540 ?M4550) 
             (?M4547 ?M4550) ?M4551 ?M4554 ?M4553 
             ?M4555
             (@singletonM ?M4539 ?M4550 (?M4540 ?M4550)
                (@map_singleton ?M4539 ?M4550 (?M4540 ?M4550) 
                   (?M4544 ?M4550) (?M4543 ?M4550))
                ?M4558 ?M4559))
          (@eq ?M4550 ?M4557 ?M4559), id 0)
        simple eapply @set_unfold_ret (cost 7, pattern 
        @SetUnfoldElemOf ?M2843 (?M2833 ?M2843) (?M2834 ?M2843) 
          ?M2844 (@mret ?M2833 ?M2839 ?M2843 ?M2845)
          (@eq ?M2843 ?M2844 ?M2845), id 0)
        simple eapply @set_unfold_difference (cost 7, pattern 
        @SetUnfoldElemOf ?M2811 ?M2812 ?M2813 ?M2820
          (@difference ?M2812 ?M2818 ?M2821 ?M2822) 
          (and ?M2823 (not ?M2824)), id 0)
        simple eapply @set_unfold_intersection (cost 7, pattern 
        @SetUnfoldElemOf ?M2795 ?M2796 ?M2797 ?M2804
          (@intersection ?M2796 ?M2801 ?M2805 ?M2806) 
          (and ?M2807 ?M2808), id 0)
        simple eapply @set_unfold_map_img_empty (cost 8, pattern 
        @SetUnfoldElemOf ?M4531 ?M4532 ?M4533 ?M4538
          (@map_img ?M4520 ?M4531 (?M4521 ?M4531) 
             (?M4528 ?M4531) ?M4532 ?M4535 ?M4534 
             ?M4536 (@empty (?M4521 ?M4531) (?M4524 ?M4531)))
          False, id 0)
        simple eapply @set_unfold_monadset_cprod (cost 8, pattern 
        @SetUnfoldElemOf (prod ?M3344 ?M3345) (?M3334 (prod ?M3344 ?M3345))
          (?M3335 (prod ?M3344 ?M3345)) ?M3350
          (@cprod (?M3334 ?M3344) (?M3334 ?M3345)
             (?M3334 (prod ?M3344 ?M3345))
             (@monadset_cprod ?M3334 ?M3339 ?M3341 ?M3344 ?M3345) 
             ?M3346 ?M3347)
          (and ?M3348 ?M3349), id 0)
        simple eapply @set_unfold_join (cost 8, pattern 
        @SetUnfoldElemOf ?M2892 (?M2882 ?M2892) (?M2883 ?M2892) 
          ?M2895 (@mjoin ?M2882 ?M2890 ?M2892 ?M2893)
          (@ex (?M2882 ?M2892)
             (fun Y : ?M2882 ?M2892 =>
              and (@elem_of ?M2892 (?M2882 ?M2892) (?M2883 ?M2892) ?M2895 Y)
                (?M2894 Y))), id 0)
        simple eapply @set_unfold_fmap (cost 8, pattern 
        @SetUnfoldElemOf ?M2876 (?M2865 ?M2876) (?M2866 ?M2876) 
          ?M2880 (@fmap ?M2865 ?M2872 ?M2875 ?M2876 ?M2877 ?M2878)
          (@ex ?M2875
             (fun y : ?M2875 => and (@eq ?M2876 ?M2880 (?M2877 y)) (?M2879 y))), id 0)
        simple eapply @set_unfold_elements (cost 9, pattern 
        @SetUnfoldElemOf ?M3410 (list ?M3410) (@list_elem_of ?M3410) 
          ?M3422 (@elements ?M3410 ?M3411 ?M3418 ?M3421) 
          ?M3423, id 0)
        simple eapply @set_unfold_bind (cost 9, pattern 
        @SetUnfoldElemOf ?M2857 (?M2846 ?M2857) (?M2847 ?M2857) 
          ?M2862 (@mbind ?M2846 ?M2851 ?M2856 ?M2857 ?M2858 ?M2859)
          (@ex ?M2856 (fun y : ?M2856 => and (?M2861 y) (?M2860 y))), id 0)
        simple eapply @set_unfold_omap (cost 10, pattern 
        @SetUnfoldElemOf ?M3595 ?M3596 ?M3597 ?M3605
          (@set_omap ?M3584 ?M3585 ?M3592 ?M3595 ?M3596 
             ?M3599 ?M3598 ?M3600 ?M3602 ?M3603)
          (@ex ?M3584
             (fun x : ?M3584 =>
              and (@eq (option ?M3595) (@Some ?M3595 ?M3605) (?M3602 x))
                (?M3604 x))), id 0)
        simple eapply @set_unfold_map (cost 10, pattern 
        @SetUnfoldElemOf ?M3475 ?M3476 ?M3477 ?M3485
          (@set_map ?M3464 ?M3465 ?M3472 ?M3475 ?M3476 
             ?M3479 ?M3478 ?M3480 ?M3482 ?M3483)
          (@ex ?M3464
             (fun x : ?M3464 => and (@eq ?M3475 ?M3485 (?M3482 x)) (?M3484 x))), id 0)
        simple eapply @set_unfold_dom_seq (cost 12, pattern 
        @SetUnfoldElemOf nat ?M4979 ?M4989 ?M4999
          (@dom (?M4978 ?M4996) ?M4979 (?M4980 ?M4996)
             (@map_seq ?M4996 (?M4978 ?M4996)
                (@map_insert nat ?M4996 (?M4978 ?M4996) (?M4984 ?M4996))
                (?M4983 ?M4996) ?M4997 ?M4998))
          (and (le ?M4997 ?M4999)
             (lt ?M4999 (Init.Nat.add ?M4997 (@length ?M4996 ?M4998)))), id 0)
        simple eapply @set_unfold_dom_singleton (cost 12, pattern 
        @SetUnfoldElemOf ?M4824 ?M4826 ?M4836 ?M4844
          (@dom (?M4825 ?M4843) ?M4826 (?M4827 ?M4843)
             (@singletonM ?M4824 ?M4843 (?M4825 ?M4843)
                (@map_singleton ?M4824 ?M4843 (?M4825 ?M4843) 
                   (?M4831 ?M4843) (?M4830 ?M4843))
                ?M4845 ?M4846))
          (@eq ?M4824 ?M4844 ?M4845), id 0)
        simple eapply @set_unfold_set_bind (cost 12, pattern 
        @SetUnfoldElemOf ?M3534 ?M3535 ?M3536 ?M3543
          (@set_bind ?M3523 ?M3524 ?M3531 ?M3535 ?M3537 ?M3539 ?M3541 ?M3542)
          (@ex ?M3523 (fun x : ?M3523 => and (?M3545 x) (?M3544 x ?M3543))), id 0)
        simple eapply @set_unfold_dom_empty (cost 13, pattern 
        @SetUnfoldElemOf ?M4726 ?M4728 ?M4738 ?M4746
          (@dom (?M4727 ?M4745) ?M4728 (?M4729 ?M4745)
             (@empty (?M4727 ?M4745) (?M4732 ?M4745)))
          False, id 0)
        simple eapply @set_unfold_dom_fmap (cost 14, pattern 
        @SetUnfoldElemOf ?M4928 ?M4930 ?M4940 ?M4950
          (@dom (?M4929 ?M4948) ?M4930 (?M4931 ?M4948)
             (@fmap ?M4929 ?M4932 ?M4947 ?M4948 ?M4949 ?M4951))
          ?M4952, id 0)
        simple eapply @set_unfold_dom_delete (cost 14, pattern 
        @SetUnfoldElemOf ?M4799 ?M4801 ?M4811 ?M4819
          (@dom (?M4800 ?M4818) ?M4801 (?M4802 ?M4818)
             (@delete ?M4799 (?M4800 ?M4818)
                (@map_delete ?M4799 ?M4818 (?M4800 ?M4818) (?M4806 ?M4818))
                ?M4820 ?M4821))
          (and ?M4822 (not (@eq ?M4799 ?M4819 ?M4820))), id 0)
        simple eapply @set_unfold_dom_insert (cost 14, pattern 
        @SetUnfoldElemOf ?M4773 ?M4775 ?M4785 ?M4793
          (@dom (?M4774 ?M4792) ?M4775 (?M4776 ?M4792)
             (@insert ?M4773 ?M4792 (?M4774 ?M4792)
                (@map_insert ?M4773 ?M4792 (?M4774 ?M4792) (?M4780 ?M4792))
                ?M4794 ?M4795 ?M4796))
          (or (@eq ?M4773 ?M4793 ?M4794) ?M4797), id 0)
        simple eapply @set_unfold_dom_alter (cost 14, pattern 
        @SetUnfoldElemOf ?M4747 ?M4749 ?M4759 ?M4768
          (@dom (?M4748 ?M4766) ?M4749 (?M4750 ?M4766)
             (@alter ?M4747 ?M4766 (?M4748 ?M4766)
                (@map_alter ?M4747 ?M4766 (?M4748 ?M4766) (?M4754 ?M4766))
                ?M4767 ?M4769 ?M4770))
          ?M4771, id 0)
        simple eapply @set_unfold_dom_difference (cost 15, pattern 
        @SetUnfoldElemOf ?M4901 ?M4903 ?M4913 ?M4921
          (@dom (?M4902 ?M4920) ?M4903 (?M4904 ?M4920)
             (@difference (?M4902 ?M4920)
                (@map_difference ?M4902 ?M4910 ?M4920) 
                ?M4922 ?M4923))
          (and ?M4924 (not ?M4925)), id 0)
        simple eapply @set_unfold_dom_intersection (cost 15, pattern 
        @SetUnfoldElemOf ?M4874 ?M4876 ?M4886 ?M4894
          (@dom (?M4875 ?M4893) ?M4876 (?M4877 ?M4893)
             (@intersection (?M4875 ?M4893)
                (@map_intersection ?M4875 ?M4883 ?M4893) 
                ?M4895 ?M4896))
          (and ?M4897 ?M4898), id 0)
        simple eapply @set_unfold_dom_union (cost 15, pattern 
        @SetUnfoldElemOf ?M4847 ?M4849 ?M4859 ?M4867
          (@dom (?M4848 ?M4866) ?M4849 (?M4850 ?M4866)
             (@union (?M4848 ?M4866) (@map_union ?M4848 ?M4856 ?M4866) 
                ?M4868 ?M4869))
          (or ?M4870 ?M4871), id 0)
        simple apply @set_unfold_multiset_elem_of (cost 100, pattern 
        @SetUnfoldElemOf ?M5475 (@gmultiset ?M5475 ?M5476 ?M5477)
          (@gmultiset_elem_of ?M5475 ?M5476 ?M5477) 
          ?M5479 ?M5478 (lt O ?M5480), id 0)
        simple apply @set_unfold_elem_of_default (cost 1000, pattern 
        @SetUnfoldElemOf ?M2657 ?M2658 ?M2659 ?M2660 
          ?M2661 (@elem_of ?M2657 ?M2658 ?M2659 ?M2660 ?M2661), id 0)
For SetUnfoldSimpl ->   (*external*) (csimpl; constructor) (cost 0, pattern 
                        SetUnfoldSimpl _ _, id 0)
For Set_ (modes - ! - - - - -
-) ->   simple apply @propset_set (cost 0, pattern 
        @Set_ ?M5833 (propset ?M5833) (@propset_elem_of ?M5833)
          (@propset_empty ?M5833) (@propset_singleton ?M5833)
          (@propset_union ?M5833) (@propset_intersection ?M5833)
          (@propset_difference ?M5833), id 0)
        simple apply @coGset_set (cost 0, pattern 
        @Set_ ?M5264 (@coGset ?M5264 ?M5265 ?M5266)
          (@coGset_elem_of ?M5264 ?M5265 ?M5266)
          (@coGset_empty ?M5264 ?M5265 ?M5266)
          (@coGset_singleton ?M5264 ?M5265 ?M5266)
          (@coGset_union ?M5264 ?M5265 ?M5266)
          (@coGset_intersection ?M5264 ?M5265 ?M5266)
          (@coGset_difference ?M5264 ?M5265 ?M5266), id 0)
        exact coPset_set (cost 0, pattern @Set_ positive coPset
                                            coPset_elem_of coPset_empty
                                            coPset_singleton coPset_union
                                            coPset_intersection
                                            coPset_difference, id 0)
        simple apply @boolset_set (cost 0, pattern 
        @Set_ ?M4651 (boolset ?M4651) (@boolset_elem_of ?M4651)
          (@boolset_empty ?M4651) (@boolset_singleton ?M4651 ?M4652)
          (@boolset_union ?M4651) (@boolset_intersection ?M4651)
          (@boolset_difference ?M4651), id 0)
        simple apply @gset_set (cost 1, pattern @Set_ 
                                                 ?M5198
                                                 (@gset ?M5198 ?M5199 ?M5200)
                                                 (@gset_elem_of 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200)
                                                 (@gset_empty 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200)
                                                 (@gset_singleton 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200)
                                                 (@gset_union 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200)
                                                 (@gset_intersection 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200)
                                                 (@gset_difference 
                                                 ?M5198 
                                                 ?M5199 
                                                 ?M5200), id 0)
        simple eapply @fin_set_set (cost 3, pattern 
        @Set_ ?M5975 ?M5976 ?M5977 ?M5978 ?M5979 ?M5980 
          ?M5981 ?M5982, id 0)
        simple eapply @finmap_dom_set (cost 11, pattern 
        @Set_ ?M6022 ?M6024 ?M6034 ?M6035 ?M6036 ?M6037 
          ?M6038 ?M6039, id 0)
For Singleton (modes -
!) ->   simple apply @topGset_singleton (cost 0, pattern 
        Singleton ?M5912 (@topGset ?M5912 ?M5913 ?M5914), id 0)
        simple apply @propset_singleton (cost 0, pattern 
        Singleton ?M5829 (propset ?M5829), id 0)
        simple apply @listset_nodup_singleton (cost 0, pattern 
        Singleton ?M5664 (listset_nodup ?M5664), id 0)
        simple apply @hashset_singleton (cost 0, pattern 
        Singleton ?M5646 (@hashset ?M5646 ?M5647), id 0)
        simple apply @coGset_singleton (cost 0, pattern 
        Singleton ?M5252 (@coGset ?M5252 ?M5253 ?M5254), id 0)
        exact coPset_singleton (cost 0, pattern Singleton positive coPset, id 0)
        simple apply @gset_singleton (cost 0, pattern 
        Singleton ?M5155 (@gset ?M5155 ?M5156 ?M5157), id 0)
        simple apply @listset_singleton (cost 0, pattern 
        Singleton ?M4588 (listset ?M4588), id 0)
        simple apply @boolset_singleton (cost 1, pattern 
        Singleton ?M4643 (boolset ?M4643), id 0)
        simple apply @mapset_singleton (cost 2, pattern 
        Singleton ?M5005 (mapset' (?M5006 unit)), id 0)
For SingletonM (modes - -
!) ->   simple apply @map_singleton (cost 2, pattern 
        SingletonM ?M3708 ?M3709 ?M3710, id 0)
For SingletonMS (modes -
!) ->   simple apply @gmultiset_singleton (cost 0, pattern 
        SingletonMS ?M5324 (@gmultiset ?M5324 ?M5325 ?M5326), id 0)
For Size (modes !) ->   simple apply @gmultiset_size (cost 0, pattern 
                        Size (@gmultiset ?M5318 ?M5319 ?M5320), id 0)
                        simple eapply @set_size (cost 2, pattern 
                        Size ?M3398, id 0)
                        simple eapply @map_size (cost 3, pattern 
                        Size ?M3715, id 0)
For SolveProperSubrelation (modes + ! !) ->   simple apply @subrelation_solve_proper_subrelation (cost 1, pattern 
        @SolveProperSubrelation ?M1924 ?M1925 ?M1926, id 0)
For SqSubsetEq (modes !) ->   
For CRelationClasses.StrictOrder ->   (*external*) (
                                      class_apply
                                       @CRelationClasses.flip_StrictOrder) (cost 3, pattern 
                                      @CRelationClasses.StrictOrder _
                                        (@CRelationClasses.flip _ _ _ _), id 0)
                                      (*external*) (
                                      class_apply
                                       @CMorphisms.PartialOrder_StrictOrder) (cost 4, pattern 
                                      @CRelationClasses.StrictOrder _
                                        (@CRelationClasses.relation_conjunction
                                           _ _ _), id 0)
For StrictOrder ->   exact Z_lexico_po (cost 0, pattern 
                     @StrictOrder Z (@lexico Z Z_lexico), id 0)
                     exact N_lexico_po (cost 0, pattern 
                     @StrictOrder N (@lexico N N_lexico), id 0)
                     exact nat_lexico_po (cost 0, pattern 
                     @StrictOrder nat (@lexico nat nat_lexico), id 0)
                     exact bool_lexico_po (cost 0, pattern 
                     @StrictOrder bool (@lexico bool bool_lexico), id 0)
                     exact Qp.lt_strict (cost 0, pattern 
                     @StrictOrder Qp Qp.lt, id 0)
                     exact Qc_lt_strict (cost 0, pattern 
                     @StrictOrder Qcanon.Qc Qcanon.Qclt, id 0)
                     exact PositiveOrder.TO.lt_strorder (cost 0, pattern 
                     @StrictOrder positive
                       (fun x y : positive =>
                        @eq comparison (Positive_as_OT.compare x y) Lt), id 0)
                     exact Positive_as_OT.lt_strorder (cost 0, pattern 
                     @StrictOrder positive Positive_as_OT.lt, id 0)
                     exact Positive_as_DT.lt_strorder (cost 0, pattern 
                     @StrictOrder positive Positive_as_DT.lt, id 0)
                     exact Z.lt_strorder (cost 0, pattern 
                     @StrictOrder Z Z.lt, id 0)
                     exact N.lt_strorder (cost 0, pattern 
                     @StrictOrder N N.lt, id 0)
                     exact Pos.lt_strorder (cost 0, pattern 
                     @StrictOrder positive Pos.lt, id 0)
                     exact Nat.lt_strorder (cost 0, pattern 
                     @StrictOrder nat lt, id 0)
                     simple apply @sig_lexico_po (cost 1, pattern 
                     @StrictOrder (@sig ?M4631 ?M4634)
                       (@lexico (@sig ?M4631 ?M4634)
                          (@sig_lexico ?M4631 ?M4632 ?M4634 ?M4635)), id 0)
                     simple apply @list_lexico_po (cost 1, pattern 
                     @StrictOrder (list ?M4625)
                       (@lexico (list ?M4625) (@list_lexico ?M4625 ?M4626)), id 0)
                     simple apply @StrictOrder_instance_0 (cost 1, pattern 
                     @StrictOrder ?M2489 (@strict ?M2489 ?M2490), id 0)
                     simple apply @prod_lexico_po (cost 2, pattern 
                     @StrictOrder (prod ?M4613 ?M4615)
                       (@lexico (prod ?M4613 ?M4615)
                          (@prod_lexico ?M4613 ?M4614 ?M4615 ?M4616)), id 0)
                     (*external*) (class_apply @flip_StrictOrder) (cost 3, pattern 
                     @StrictOrder _ (@flip _ _ _ _), id 0)
                     (*external*) (class_apply @PartialOrder_StrictOrder) (cost 4, pattern 
                     @StrictOrder _ (@relation_conjunction _ _ _), id 0)
For SubsetEq (modes !) ->   simple apply @gmultiset_subseteq (cost 0, pattern 
                            SubsetEq (@gmultiset ?M5309 ?M5310 ?M5311), id 0)
                            simple apply @list_subseteq (cost 0, pattern 
                            SubsetEq (list ?M2127), id 0)
                            simple eapply @map_subseteq (cost 2, pattern 
                            SubsetEq (?M3732 ?M3734), id 0)
                            simple eapply @set_subseteq_instance (cost 20, pattern 
                            SubsetEq ?M2566, id 0)
For Surj ->   simple apply @prod_swap_surj (cost 0, pattern 
              @Surj (prod ?M1235 ?M1236) (prod ?M1236 ?M1235)
                (@eq (prod ?M1236 ?M1235)) (@prod_swap ?M1235 ?M1236), id 0)
              simple apply @id_surj (cost 0, pattern 
              @Surj ?M1190 ?M1190 (@eq ?M1190) (@id ?M1190), id 0)
              simple apply @compose_surj (cost 2, pattern 
              @Surj ?M1191 ?M1193 ?M1194
                (@compose ?M1191 ?M1192 ?M1193 ?M1196 ?M1195), id 0)
For CRelationClasses.Symmetric ->   exact CRelationClasses.iffT_Symmetric (cost 0, pattern 
                                    @CRelationClasses.Symmetric Type
                                      CRelationClasses.iffT, id 0)
                                    exact CRelationClasses.iff_Symmetric (cost 0, pattern 
                                    @CRelationClasses.Symmetric Prop iff, id 0)
                                    simple apply @CRelationClasses.eq_Symmetric (cost 0, pattern 
                                    @CRelationClasses.Symmetric 
                                      ?M419 (@eq ?M419), id 0)
                                    simple apply @CRelationClasses.Equivalence_Symmetric (cost 1, pattern 
                                    @CRelationClasses.Symmetric 
                                      ?M406 ?M407, id 0)
                                    (*external*) (
                                    class_apply
                                     @CRelationClasses.flip_Symmetric) (cost 3, pattern 
                                    @CRelationClasses.Symmetric _
                                      (@CRelationClasses.flip _ _ _ _), id 0)
                                    (*external*) (
                                    class_apply
                                     @CRelationClasses.complement_Symmetric) (cost 3, pattern 
                                    @CRelationClasses.Symmetric _
                                      (@CRelationClasses.complement _ _), id 0)
                                    simple apply @CRelationClasses.PER_Symmetric (cost 3, pattern 
                                    @CRelationClasses.Symmetric 
                                      ?M397 ?M398, id 0)
For Symmetric (modes -
!) ->   simple apply @map_disjoint_sym (cost 0, pattern 
        @Symmetric (?M3955 ?M3957)
          (@map_disjoint ?M3954 ?M3955 ?M3956 ?M3957), id 0)
        simple apply @map_agree_sym (cost 0, pattern 
        @Symmetric (?M3951 ?M3953) (@map_agree ?M3950 ?M3951 ?M3952 ?M3953), id 0)
        simple apply @sc_symmetric (cost 0, pattern 
        @Symmetric ?M3393 (@sc ?M3393 ?M3394), id 0)
        exact iff_Symmetric (cost 0, pattern @Symmetric Prop iff, id 0)
        simple apply @neq_Symmetric (cost 0, pattern 
        @Symmetric ?M258 (fun x y : ?M258 => not (@eq ?M258 x y)), id 0)
        simple apply @eq_Symmetric (cost 0, pattern 
        @Symmetric ?M255 (@eq ?M255), id 0)
        simple apply @Symmetric_instance_0 (cost 1, pattern 
        @Symmetric (list ?M2180) (@Forall2 ?M2180 ?M2180 ?M2181), id 0)
        simple apply @option_Forall2_sym (cost 1, pattern 
        @Symmetric (option ?M1942) (@option_Forall2 ?M1942 ?M1942 ?M1943), id 0)
        simple apply @Equivalence.equiv_symmetric (cost 1, pattern 
        @Symmetric ?M508 (@Equivalence.equiv ?M508 ?M509 ?M510), id 0)
        simple apply @Equivalence_Symmetric (cost 1, pattern 
        @Symmetric ?M242 ?M243, id 0)
        simple apply @sum_relation_sym (cost 2, pattern 
        @Symmetric (sum ?M1437 ?M1439)
          (@sum_relation ?M1437 ?M1439 ?M1438 ?M1440), id 0)
        simple apply @prod_relation_sym (cost 2, pattern 
        @Symmetric (prod ?M1243 ?M1245)
          (@prod_relation ?M1243 ?M1245 ?M1244 ?M1246), id 0)
        (*external*) (class_apply @flip_Symmetric) (cost 3, pattern 
        @Symmetric _ (@flip _ _ _ _), id 0)
        (*external*) (class_apply @complement_Symmetric) (cost 3, pattern 
        @Symmetric _ (@complement _ _), id 0)
        simple apply @PER_Symmetric (cost 3, pattern 
        @Symmetric ?M233 ?M234, id 0)
        simple eapply @disjoint_sym (cost 4, pattern 
        @Symmetric ?M3027
          (@disjoint ?M3027 (@set_disjoint_instance ?M3026 ?M3027 ?M3028)), id 0)
        simple apply @Equivalence.pointwise_symmetric (cost 9, pattern 
        @Symmetric (forall _ : ?M518, ?M519)
          (@pointwise_relation ?M518 ?M519 ?M520), id 0)
For TCAnd (modes !
!) ->   simple apply TCAnd_intro (cost 2, pattern TCAnd ?M1097 ?M1098, id 0)
For TCDiag (modes ! ! - !, ! ! !
-) ->   simple apply @TCDiag_diag (cost 1, pattern 
        @TCDiag ?M1141 ?M1142 ?M1143 ?M1143, id 0)
For TCElemOf (modes ! !
!) ->   simple apply @TCElemOf_here (cost 0, pattern 
        @TCElemOf ?M1131 ?M1132 (@cons ?M1131 ?M1132 ?M1133), id 0)
        simple apply @TCElemOf_further (cost 1, pattern 
        @TCElemOf ?M1134 ?M1135 (@cons ?M1134 ?M1136 ?M1137), id 0)
For TCEq (modes ! -
-) ->   simple apply @TCEq_refl (cost 0, pattern @TCEq ?M1139 ?M1140 ?M1140, id 0)
For TCExists (modes ! !
!) ->   simple apply @TCExists_cons_hd (cost 10, pattern 
        @TCExists ?M1121 ?M1122 (@cons ?M1121 ?M1123 ?M1124), id 0)
        simple apply @TCExists_cons_tl (cost 20, pattern 
        @TCExists ?M1126 ?M1127 (@cons ?M1126 ?M1128 ?M1129), id 0)
For TCFastDone ->   (*external*) (change P; fast_done) (cost 1, pattern 
                    TCFastDone ?P, id 0)
For TCForall (modes ! !
!) ->   simple apply @TCForall_nil (cost 0, pattern 
        @TCForall ?M1101 ?M1102 (@nil ?M1101), id 0)
        simple apply @TCForall_app (cost 2, pattern 
        @TCForall ?M2296 ?M2297 (@app ?M2296 ?M2298 ?M2299), id 0)
        simple apply @TCForall_cons (cost 2, pattern 
        @TCForall ?M1103 ?M1104 (@cons ?M1103 ?M1105 ?M1106), id 0)
For TCForall2 (modes ! ! ! - !, ! ! ! !
-) ->   simple apply @TCForall2_nil (cost 0, pattern 
        @TCForall2 ?M1109 ?M1110 ?M1111 (@nil ?M1109) 
          (@nil ?M1110), id 0)
        simple apply @TCForall2_cons (cost 2, pattern 
        @TCForall2 ?M1112 ?M1113 ?M1114 (@cons ?M1112 ?M1115 ?M1117)
          (@cons ?M1113 ?M1116 ?M1118), id 0)
For TCIf ->   (*external*) (first
              [ notypeclasses refine (TCIf_true _ _ _ _ _); [ tc_solve |  ]
              | notypeclasses refine (TCIf_false _ _ _ _) ]) (cost 0, pattern 
              TCIf _ _ _, id 0)
For TCNoBackTrack ->   (*external*) (notypeclasses refine
                                       (TCNoBackTrack_intro _ _);
                                      tc_solve) (cost 0, pattern 
                       TCNoBackTrack _, id 0)
For TCOr (modes !
!) ->   simple apply TCOr_l (cost 9, pattern TCOr ?M1091 ?M1092, id 0)
        simple apply TCOr_r (cost 10, pattern TCOr ?M1094 ?M1095, id 0)
For TCSimpl (modes ! -
-) ->   (*external*) (simpl; notypeclasses refine (@TCEq_refl _ _)) (cost 0, pattern 
        @TCSimpl _ _ _, id 0)
For TCTrue ->   exact TCTrue_intro (cost 0, pattern TCTrue, id 0)
For Top (modes !) ->   simple apply @topGset_top (cost 0, pattern 
                       Top (@topGset ?M5909 ?M5910 ?M5911), id 0)
                       simple apply @propset_top (cost 0, pattern 
                       Top (propset ?M5827), id 0)
                       simple apply @coGset_top (cost 0, pattern 
                       Top (@coGset ?M5249 ?M5250 ?M5251), id 0)
                       exact coPset_top (cost 0, pattern 
                       Top coPset, id 0)
                       simple apply @boolset_top (cost 0, pattern 
                       Top (boolset ?M4641), id 0)
For TopSet (modes - ! -
-) ->   simple apply @topGset_top_set (cost 0, pattern 
        @TopSet ?M5921 (@topGset ?M5921 ?M5922 ?M5923)
          (@topGset_elem_of ?M5921 ?M5922 ?M5923)
          (@topGset_top ?M5921 ?M5922 ?M5923), id 0)
        simple apply @propset_top_set (cost 0, pattern 
        @TopSet ?M5834 (propset ?M5834) (@propset_elem_of ?M5834)
          (@propset_top ?M5834), id 0)
        simple apply @coGset_top_set (cost 0, pattern 
        @TopSet ?M5267 (@coGset ?M5267 ?M5268 ?M5269)
          (@coGset_elem_of ?M5267 ?M5268 ?M5269)
          (@coGset_top ?M5267 ?M5268 ?M5269), id 0)
        exact coPset_top_set (cost 0, pattern @TopSet positive coPset
                                                coPset_elem_of coPset_top, id 0)
        simple apply @boolset_top_set (cost 1, pattern 
        @TopSet ?M4653 (boolset ?M4653) (@boolset_elem_of ?M4653)
          (@boolset_top ?M4653), id 0)
For Total ->   exact String.le_total (cost 0, pattern 
               @Total string String.le, id 0)
               exact Qp.le_total (cost 0, pattern 
               @Total Qp Qp.le, id 0)
               exact Qc_le_total (cost 0, pattern 
               @Total Qcanon.Qc Qcanon.Qcle, id 0)
               exact Z.le_total (cost 0, pattern @Total Z Z.le, id 0)
               exact N.le_total (cost 0, pattern @Total N N.le, id 0)
               exact Pos.le_total (cost 0, pattern 
               @Total positive Pos.le, id 0)
               exact Nat.le_total (cost 0, pattern 
               @Total nat le, id 0)
               simple apply @trichotomy_total (cost 2, pattern 
               @Total ?M2495 ?M2496, id 0)
For TotalOrder (modes ! !) ->   
For CRelationClasses.Transitive ->   exact CRelationClasses.iffT_Transitive (cost 0, pattern 
                                     @CRelationClasses.Transitive Type
                                       CRelationClasses.iffT, id 0)
                                     exact CRelationClasses.arrow_Transitive (cost 0, pattern 
                                     @CRelationClasses.Transitive Type
                                       CRelationClasses.arrow, id 0)
                                     exact CRelationClasses.iff_Transitive (cost 0, pattern 
                                     @CRelationClasses.Transitive Prop iff, id 0)
                                     exact CRelationClasses.impl_Transitive (cost 0, pattern 
                                     @CRelationClasses.Transitive Prop impl, id 0)
                                     simple apply @CRelationClasses.eq_Transitive (cost 0, pattern 
                                     @CRelationClasses.Transitive 
                                       ?M420 (@eq ?M420), id 0)
                                     simple apply @CRelationClasses.Equivalence_Transitive (cost 1, pattern 
                                     @CRelationClasses.Transitive 
                                       ?M409 ?M410, id 0)
                                     simple apply @CRelationClasses.StrictOrder_Transitive (cost 1, pattern 
                                     @CRelationClasses.Transitive 
                                       ?M391 ?M392, id 0)
                                     simple apply @CRelationClasses.PreOrder_Transitive (cost 2, pattern 
                                     @CRelationClasses.Transitive 
                                       ?M385 ?M386, id 0)
                                     (*external*) (
                                     class_apply
                                      @CRelationClasses.flip_Transitive) (cost 3, pattern 
                                     @CRelationClasses.Transitive _
                                       (@CRelationClasses.flip _ _ _ _), id 0)
                                     simple apply @CRelationClasses.PER_Transitive (cost 3, pattern 
                                     @CRelationClasses.Transitive 
                                       ?M400 ?M401, id 0)
For Transitive (modes -
!) ->   simple apply @tc_transitive (cost 0, pattern 
        @Transitive ?M3388 (@tc ?M3388 ?M3389), id 0)
        exact iff_Transitive (cost 0, pattern @Transitive Prop iff, id 0)
        exact impl_Transitive (cost 0, pattern @Transitive Prop impl, id 0)
        simple apply @eq_Transitive (cost 0, pattern 
        @Transitive ?M256 (@eq ?M256), id 0)
        simple apply @Transitive_instance_0 (cost 1, pattern 
        @Transitive (list ?M2183) (@Forall2 ?M2183 ?M2183 ?M2184), id 0)
        simple apply @option_Forall2_trans (cost 1, pattern 
        @Transitive (option ?M1945) (@option_Forall2 ?M1945 ?M1945 ?M1946), id 0)
        simple apply @Equivalence.equiv_transitive (cost 1, pattern 
        @Transitive ?M511 (@Equivalence.equiv ?M511 ?M512 ?M513), id 0)
        simple apply @Equivalence_Transitive (cost 1, pattern 
        @Transitive ?M245 ?M246, id 0)
        simple apply @StrictOrder_Transitive (cost 1, pattern 
        @Transitive ?M227 ?M228, id 0)
        simple apply @sum_relation_trans (cost 2, pattern 
        @Transitive (sum ?M1443 ?M1445)
          (@sum_relation ?M1443 ?M1445 ?M1444 ?M1446), id 0)
        simple apply @prod_relation_trans (cost 2, pattern 
        @Transitive (prod ?M1249 ?M1251)
          (@prod_relation ?M1249 ?M1251 ?M1250 ?M1252), id 0)
        simple apply @PreOrder_Transitive (cost 2, pattern 
        @Transitive ?M221 ?M222, id 0)
        (*external*) (class_apply @flip_Transitive) (cost 3, pattern 
        @Transitive _ (@flip _ _ _ _), id 0)
        simple apply @PER_Transitive (cost 3, pattern 
        @Transitive ?M236 ?M237, id 0)
        exact Z.divide_transitive (cost 5, pattern 
        @Transitive Z Z.divide, id 0)
        exact N.divide_transitive (cost 5, pattern 
        @Transitive N N.divide, id 0)
        exact N.Private_NZGcdProp.divide_transitive (cost 5, pattern 
        @Transitive N N.divide, id 0)
        exact Nat.divide_transitive (cost 5, pattern 
        @Transitive nat Nat.divide, id 0)
        exact Nat.Private_NZGcdProp.divide_transitive (cost 5, pattern 
        @Transitive nat Nat.divide, id 0)
        simple apply @Equivalence.pointwise_transitive (cost 9, pattern 
        @Transitive (forall _ : ?M522, ?M523)
          (@pointwise_relation ?M522 ?M523 ?M524), id 0)
For Trichotomy ->   simple apply @total_order_trichotomy (cost 1, pattern 
                    @Trichotomy ?M5963 (@strict ?M5963 ?M5964), id 0)
                    simple apply @trichotomyT_trichotomy (cost 1, pattern 
                    @Trichotomy ?M2503 ?M2504, id 0)
For TrichotomyT ->   exact Z_lexico_trichotomy (cost 0, pattern 
                     @TrichotomyT Z (@lexico Z Z_lexico), id 0)
                     exact N_lexico_trichotomy (cost 0, pattern 
                     @TrichotomyT N (@lexico N N_lexico), id 0)
                     exact nat_lexico_trichotomy (cost 0, pattern 
                     @TrichotomyT nat (@lexico nat nat_lexico), id 0)
                     exact bool_lexico_trichotomy (cost 0, pattern 
                     @TrichotomyT bool (@lexico bool bool_lexico), id 0)
                     simple apply @sig_lexico_trichotomy (cost 1, pattern 
                     @TrichotomyT (@sig ?M4636 ?M4639)
                       (@lexico (@sig ?M4636 ?M4639)
                          (@sig_lexico ?M4636 ?M4637 ?M4639 ?M4640)), id 0)
                     simple apply @list_lexico_trichotomy (cost 1, pattern 
                     @TrichotomyT (list ?M4628)
                       (@lexico (list ?M4628) (@list_lexico ?M4628 ?M4629)), id 0)
                     simple apply @prod_lexico_trichotomyT (cost 2, pattern 
                     @TrichotomyT (prod ?M4619 ?M4622)
                       (@lexico (prod ?M4619 ?M4622)
                          (@prod_lexico ?M4619 ?M4620 ?M4622 ?M4623)), id 0)
For ZifyClasses.UnOp ->   exact ZifyInst.Op_Z_to_pos (cost 0, pattern 
                          @ZifyClasses.UnOp Z positive Z Z Z.to_pos
                            ZifyInst.Inj_Z_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_Z_to_nat (cost 0, pattern 
                          @ZifyClasses.UnOp Z nat Z Z Z.to_nat
                            ZifyInst.Inj_Z_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_Z_quot2 (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.quot2 ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_div2 (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.div2 ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_square (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.square ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_succ_double (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.succ_double
                            ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_pred_double (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.pred_double
                            ZifyInst.Inj_Z_Z ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_double (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.double ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_sgn (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.sgn ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_abs (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.abs ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_opp (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.opp ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_pred (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.pred ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_succ (cost 0, pattern 
                          @ZifyClasses.UnOp Z Z Z Z Z.succ ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_N_square (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.square ZifyInst.Inj_N_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_div2 (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.div2 ZifyInst.Inj_N_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_succ_pos (cost 0, pattern 
                          @ZifyClasses.UnOp N positive Z Z N.succ_pos
                            ZifyInst.Inj_N_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_N_double (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.double ZifyInst.Inj_N_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_succ_double (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.succ_double
                            ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_succ (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.succ ZifyInst.Inj_N_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_pred (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z N.pred ZifyInst.Inj_N_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_pos (cost 0, pattern 
                          @ZifyClasses.UnOp positive N Z Z Npos
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_Z_abs_N (cost 0, pattern 
                          @ZifyClasses.UnOp Z N Z Z Z.abs_N ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_of_nat (cost 0, pattern 
                          @ZifyClasses.UnOp nat N Z Z N.of_nat
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_N_Npos (cost 0, pattern 
                          @ZifyClasses.UnOp positive N Z Z Npos
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_Z_of_nat (cost 0, pattern 
                          @ZifyClasses.UnOp nat Z Z Z Z.of_nat
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_xI (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z xI
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_xO (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z xO
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_Pos_Ndouble (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z Pos.Ndouble
                            ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_Pos_Nsucc_double (cost 0, pattern 
                          @ZifyClasses.UnOp N N Z Z Pos.Nsucc_double
                            ZifyInst.Inj_N_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_pos_square (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z Pos.square
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_pos_of_nat (cost 0, pattern 
                          @ZifyClasses.UnOp nat positive Z Z Pos.of_nat
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_pos_of_succ_nat (cost 0, pattern 
                          @ZifyClasses.UnOp nat positive Z Z Pos.of_succ_nat
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_pos_predN (cost 0, pattern 
                          @ZifyClasses.UnOp positive N Z Z Pos.pred_N
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_pos_pred (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z Pos.pred
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_pos_pred_double (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z
                            Pos.pred_double ZifyInst.Inj_pos_Z
                            ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_pos_succ (cost 0, pattern 
                          @ZifyClasses.UnOp positive positive Z Z Pos.succ
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_pos_Z, id 0)
                          exact ZifyInst.Op_Z_pos (cost 0, pattern 
                          @ZifyClasses.UnOp positive Z Z Z Zpos
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_neg (cost 0, pattern 
                          @ZifyClasses.UnOp positive Z Z Z Zneg
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_Z_to_N (cost 0, pattern 
                          @ZifyClasses.UnOp Z N Z Z Z.to_N ZifyInst.Inj_Z_Z
                            ZifyInst.Inj_N_Z, id 0)
                          exact ZifyInst.Op_Z_of_N (cost 0, pattern 
                          @ZifyClasses.UnOp N Z Z Z Z.of_N ZifyInst.Inj_N_Z
                            ZifyInst.Inj_Z_Z, id 0)
                          exact ZifyInst.Op_N_to_nat (cost 0, pattern 
                          @ZifyClasses.UnOp N nat Z Z N.to_nat
                            ZifyInst.Inj_N_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_pos_to_nat (cost 0, pattern 
                          @ZifyClasses.UnOp positive nat Z Z Pos.to_nat
                            ZifyInst.Inj_pos_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_nat_double (cost 0, pattern 
                          @ZifyClasses.UnOp nat nat Z Z Nat.double
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_nat_div2 (cost 0, pattern 
                          @ZifyClasses.UnOp nat nat Z Z Nat.div2
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_Z_abs_nat (cost 0, pattern 
                          @ZifyClasses.UnOp Z nat Z Z Z.abs_nat
                            ZifyInst.Inj_Z_Z ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_S (cost 0, pattern 
                          @ZifyClasses.UnOp nat nat Z Z S ZifyInst.Inj_nat_Z
                            ZifyInst.Inj_nat_Z, id 0)
                          exact ZifyInst.Op_pred (cost 0, pattern 
                          @ZifyClasses.UnOp nat nat Z Z Nat.pred
                            ZifyInst.Inj_nat_Z ZifyInst.Inj_nat_Z, id 0)
For ZifyClasses.UnOpSpec ->   exact ZifyInst.ZabsSpec (cost 0, pattern 
                              @ZifyClasses.UnOpSpec Z Z Z.abs, id 0)
                              exact ZifyInst.ZsgnSpec (cost 0, pattern 
                              @ZifyClasses.UnOpSpec Z Z Z.sgn, id 0)
For Unconvertible ->   (*external*) unconvertible (cost 0, pattern 
                       Unconvertible _ _ _, id 0)
For Union (modes !) ->   simple apply @topGset_union (cost 0, pattern 
                         Union (@topGset ?M5915 ?M5916 ?M5917), id 0)
                         simple apply @propset_union (cost 0, pattern 
                         Union (propset ?M5830), id 0)
                         simple apply @gmultiset_union (cost 0, pattern 
                         Union (@gmultiset ?M5327 ?M5328 ?M5329), id 0)
                         simple apply @coGset_union (cost 0, pattern 
                         Union (@coGset ?M5255 ?M5256 ?M5257), id 0)
                         exact coPset_union (cost 0, pattern 
                         Union coPset, id 0)
                         simple apply @gset_union (cost 0, pattern 
                         Union (@gset ?M5158 ?M5159 ?M5160), id 0)
                         simple apply @boolset_union (cost 0, pattern 
                         Union (boolset ?M4646), id 0)
                         simple apply @listset_union (cost 0, pattern 
                         Union (listset ?M4589), id 0)
                         simple apply @option_union (cost 0, pattern 
                         Union (option ?M2010), id 0)
                         simple apply @listset_nodup_union (cost 1, pattern 
                         Union (listset_nodup ?M5665), id 0)
                         simple apply @hashset_union (cost 1, pattern 
                         Union (@hashset ?M5648 ?M5650), id 0)
                         simple apply @mapset_union (cost 1, pattern 
                         Union (mapset' (?M5009 unit)), id 0)
                         simple apply @map_union (cost 1, pattern 
                         Union (?M3735 ?M3737), id 0)
For UnionWith (modes - !) ->   simple apply @option_union_with (cost 0, pattern 
        UnionWith ?M2007 (option ?M2007), id 0)
        simple apply @map_union_with (cost 1, pattern 
        UnionWith ?M3719 (?M3717 ?M3719), id 0)
For UpClose (modes - !) ->   exact nclose (cost 0, pattern UpClose namespace coPset, id 0)
For CRelationClasses.subrelation ->   (*external*) (
                                      class_apply @CMorphisms.flip2) (cost 1, pattern 
                                      @CRelationClasses.subrelation _ _
                                        (@CRelationClasses.flip _ _ _ _), id 0)
                                      (*external*) (
                                      class_apply @CMorphisms.flip1) (cost 1, pattern 
                                      @CRelationClasses.subrelation _
                                        (@CRelationClasses.flip _ _ _ _) _, id 0)
                                      exact CMorphisms.iffT_flip_arrow_subrelation (cost 2, pattern 
                                      @CRelationClasses.subrelation Type
                                        CRelationClasses.iffT
                                        (@CRelationClasses.flip Type Type
                                           Type CRelationClasses.arrow), id 0)
                                      exact CMorphisms.iffT_arrow_subrelation (cost 2, pattern 
                                      @CRelationClasses.subrelation Type
                                        CRelationClasses.iffT
                                        CRelationClasses.arrow, id 0)
                                      exact CMorphisms.iff_flip_impl_subrelation (cost 2, pattern 
                                      @CRelationClasses.subrelation Prop iff
                                        (@CRelationClasses.flip Prop Prop
                                           Prop impl), id 0)
                                      exact CMorphisms.iff_impl_subrelation (cost 2, pattern 
                                      @CRelationClasses.subrelation Prop iff
                                        impl, id 0)
                                      (*external*) (
                                      CMorphisms.subrelation_tac T U) (cost 3, pattern 
                                      @CRelationClasses.subrelation _ 
                                        ?T ?U, id 0)
                                      (*external*) (
                                      apply
                                       (@CMorphisms.forall_subrelation A B R
                                          S);
                                       intro) (cost 4, pattern 
                                      @CRelationClasses.subrelation _
                                        (@CMorphisms.forall_relation ?A ?B ?R)
                                        (@CMorphisms.forall_relation _ _ ?S), id 0)
                                      simple apply @CMorphisms.pointwise_subrelation (cost 4, pattern 
                                      @CRelationClasses.subrelation
                                        (forall _ : ?M439, ?M440)
                                        (@CMorphisms.pointwise_relation 
                                           ?M439 ?M440 
                                           ?M441)
                                        (@CMorphisms.pointwise_relation 
                                           ?M439 ?M440 
                                           ?M442), id 0)
                                      (*external*) (
                                      class_apply
                                       @CRelationClasses.subrelation_symmetric) (cost 4, pattern 
                                      @CRelationClasses.subrelation _
                                        (@CRelationClasses.flip _ _ _ _) _, id 0)
For subrelation ->   (*external*) (class_apply @flip2) (cost 1, pattern 
                     @subrelation _ _ (@flip _ _ _ _), id 0)
                     (*external*) (class_apply @flip1) (cost 1, pattern 
                     @subrelation _ (@flip _ _ _ _) _, id 0)
                     exact iff_flip_impl_subrelation (cost 2, pattern 
                     @subrelation Prop iff (@flip Prop Prop Prop impl), id 0)
                     exact iff_impl_subrelation (cost 2, pattern 
                     @subrelation Prop iff impl, id 0)
                     (*external*) (subrelation_tac T U) (cost 3, pattern 
                     @subrelation _ ?T ?U, id 0)
                     (*external*) (apply (@forall_subrelation A B R S); intro) (cost 4, pattern 
                     @subrelation _ (@forall_relation ?A ?B ?R)
                       (@forall_relation _ _ ?S), id 0)
                     simple apply @pointwise_subrelation (cost 4, pattern 
                     @subrelation (forall _ : ?M279, ?M280)
                       (@pointwise_relation ?M279 ?M280 ?M281)
                       (@pointwise_relation ?M279 ?M280 ?M282), id 0)
                     (*external*) (class_apply @subrelation_symmetric) (cost 4, pattern 
                     @subrelation _ (@flip _ _ _ _) _, id 0)
For texist ->   (*external*) (progress
                               cbn[texist tele_fold tele_bind tele_app]) (cost 1, pattern 
                @texist _ _, id 0)
For tforall ->   (*external*) (progress
                                cbn[tforall tele_fold tele_bind tele_app]) (cost 1, pattern 
                 @tforall _ _, id 0)
For vm_compute_eq ->   (*external*) (vm_compute; reflexivity) (cost 0, pattern 
                       @vm_compute_eq _ _ _, id 0)


*)